import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition

/-!
# Positive-degree cohomology of a point: source provider

This provider isolates the singular-complex calculation used by the circle
profile.  The actual point singular complex has one simplex in every degree;
its alternating boundary is the identity in every positive even degree and
zero in odd degree, so the dual cocycle quotient is zero in every positive
degree.  This is the calculation in Hatcher, Proposition 2.8 p.110 and
pp.197--198, including characteristic two.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false in
/-- Positive cohomology vanishes for any one-point space, with commutative
coefficients in any universe. Source: Hatcher Proposition 2.8
p.110 and pp.197–198. The unique simplex in each degree makes the alternating
coboundary zero in even source degree and identity in odd source degree. Thus
odd cocycles vanish and positive even cocycles are boundaries, over any ring. -/
theorem unique_positive_cohomology (K : Type u) [CommRing K]
    (X : TopCat.{u}) [Unique X] :
    ∀ n : ℕ, 0 < n → Subsingleton (cohomology K X n) := by
  intro n hn
  let S := TopCat.toSSet.obj X
  let Q := complex K X
  have hs (m : ℕ) : Subsingleton (S _⦋m⦌) := by
    apply (TopCat.toSSetObjEquiv X (op ⦋m⦌)).injective.subsingleton
  let (m : ℕ) : Subsingleton (S _⦋m⦌) := hs m
  let σ (m : ℕ) : S _⦋m⦌ := (TopCat.toSSetObjEquiv X (op ⦋m⦌)).symm
    (ContinuousMap.const _ (default : X))
  have hδ (m : ℕ) (a : (S.chainComplex (ModuleCat.of K K)).X m ⟶ ModuleCat.of K K)
      (τ : S _⦋m + 1⦌) :
      S.ιChainComplex τ ≫ (S.chainComplex (ModuleCat.of K K)).d (m + 1) m ≫ a =
        (if Even m then (0 : ℤ) else 1) • (S.ιChainComplex (σ m) ≫ a) := by
    rw [← Category.assoc, SSet.ιChainComplex_d]
    have hf (i : Fin (m + 2)) : S.δ i τ = σ m := Subsingleton.elim _ _
    simp only [hf, Preadditive.zsmul_comp, ← Finset.sum_smul,
      Fin.sum_neg_one_pow, Nat.even_add, show Even (2 : ℕ) from ⟨1, rfl⟩, iff_true]
  change Subsingleton (cycles K Q n ⧸ boundaries K Q n)
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro a _
  change ∃ b, (Q.sc n).moduleCatToCycles b = a
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  by_cases he : Even (m + 1)
  · let b : Q.X m := Sigma.desc (fun _ : S _⦋m⦌ ↦ S.ιChainComplex (σ (m + 1)) ≫ a.val)
    have hδb : (Q.d m (m + 1)).hom b = a.val := by
      apply SSet.chainComplex_hom_ext
      intro τ
      change S.ιChainComplex τ ≫ (S.chainComplex (ModuleCat.of K K)).d (m + 1) m ≫ b = _
      rw [hδ]
      have hem : ¬ Even m := by simpa only [Nat.even_add_one] using he
      simp only [hem, ite_false, one_smul]
      change Sigma.ι (fun _ : S _⦋m⦌ ↦ ModuleCat.of K K) (σ m) ≫
        Sigma.desc _ = _
      rw [Sigma.ι_comp_desc]
      change S.ιChainComplex (σ (m + 1)) ≫ a.val = S.ιChainComplex τ ≫ a.val
      rw [Subsingleton.elim (σ (m + 1)) τ]
    refine ⟨(Q.xPrevIso (ComplexShape.up_mk m (m + 1) rfl)).inv b, ?_⟩
    apply Subtype.ext
    change (((Q.xPrevIso (ComplexShape.up_mk m (m + 1) rfl)).inv ≫
      Q.dTo (m + 1)).hom b) = a.val
    rw [Q.xPrevIso_comp_dTo]
    exact hδb
  · have ha := a.property
    change (Q.d (m + 1) ((ComplexShape.up ℕ).next (m + 1))).hom a.val = 0 at ha
    rw [(ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (m + 1) (m + 1 + 1) rfl)] at ha
    change (S.chainComplex (ModuleCat.of K K)).d (m + 1 + 1) (m + 1) ≫ a.val = 0 at ha
    have haz : a.val = 0 := by
      apply SSet.chainComplex_hom_ext
      intro τ
      have hz := congrArg (fun f ↦ S.ιChainComplex (σ (m + 1 + 1)) ≫ f) ha
      rw [hδ] at hz
      simpa only [he, ite_false, one_smul, CategoryTheory.Limits.comp_zero,
        Subsingleton.elim τ (σ (m + 1))] using hz
    refine ⟨0, ?_⟩
    apply Subtype.ext
    change 0 = a.val
    exact haz.symm


end HolomorphicAnosov.SingularCochain
end

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The actual singular cohomology of a point is subsingleton in every
positive degree over a field.

Source: Hatcher, Algebraic Topology, Proposition 2.8 p.110 and the dual cochain
complex definition pp.197–198. There is one singular simplex in every degree.
Its boundary is the alternating sum of its identical faces. The integer sum
of the signs is zero when the number of faces is even and one otherwise.
Consequently an odd-degree cocycle vanishes on the unique generator, so it
is zero. In positive even degree n, define a degree-(n−1) cochain to have the
same value on its unique generator as the given cocycle. The alternating
boundary sum has coefficient one in that degree, so this cochain has the
given cocycle as its coboundary. Thus every cocycle lies in the actual incoming
boundary range, and the kernel/image quotient is a subsingleton. The sign
calculation takes place over the integers and acts on K, so no division by two
or restriction on the characteristic is used. Degree zero is excluded. -/
theorem point_positive_cohomology_provider (K : Type) [Field K] :
    ∀ n : ℕ, 0 < n → Subsingleton (cohomology K pointSpace n) :=
  SingularCochain.unique_positive_cohomology K pointSpace

end
end HolomorphicAnosov.CircleSingularCohomology

