import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Cross-universe chain and homology comparison

Agent-written packaging of Mathlib's componentwise complex isomorphism and exact
module-universe-lift homology comparison. No preservation of arbitrary coproducts
is used or assumed.
-/

open CategoryTheory
universe u
noncomputable section
namespace HolomorphicAnosov

/-- A family of degreewise rational linear equivalences commuting with successor boundaries
assembles to an isomorphism with the lifted small complex and induces homology
linear equivalences commuting with every pair of corresponding chain maps.

Source: agent-written universe adapter for the chain-map and induced-homology
construction of Hatcher, Algebraic Topology §2.1 pp.108–112. Lift the target
modules, compose the given degree equivalences with the canonical upward linear
equivalence, and use the boundary equations to construct a complex isomorphism.
Apply native homology, then the exact ULift functor's homology comparison, and
finally project downward. Naturality follows by applying homology to the chain
square and the naturality of the exact-functor comparison. Small and large module
universes are explicit; degree zero and the zero complex require no exceptions.
-/
theorem chain_complex_ulift_comparison {ι : Type*}
    (K : ι → ChainComplex (ModuleCat.{u} ℚ) ℕ)
    (L : ι → ChainComplex (ModuleCat.{0} ℚ) ℕ)
    (e : ∀ s n, (K s).X n ≃ₗ[ℚ] (L s).X n)
    (he : ∀ s n x, e s n ((K s).d (n + 1) n x) =
      (L s).d (n + 1) n (e s (n + 1) x)) :
    let F := ModuleCat.uliftFunctor.{u, 0} ℚ
    ∃ E : ∀ s, K s ≅ (F.mapHomologicalComplex (.down ℕ)).obj (L s),
      (∀ s n x, (((E s).hom.f n) x).down = e s n x) ∧
      ∀ k, ∃ h : ∀ s, (K s).homology k ≃ₗ[ℚ] (L s).homology k,
        ∀ s t (a : K s ⟶ K t) (b : L s ⟶ L t),
          (∀ n x, e t n (a.f n x) = b.f n (e s n x)) →
          ∀ x, h t (HomologicalComplex.homologyMap a k x) =
            HomologicalComplex.homologyMap b k (h s x) := by
  let F := ModuleCat.uliftFunctor.{u, 0} ℚ
  let LF s := (F.mapHomologicalComplex (.down ℕ)).obj (L s)
  let ei (s : ι) (n : ℕ) : (K s).X n ≅ (LF s).X n :=
    ((e s n).trans
      (ULift.moduleEquiv.symm : (L s).X n ≃ₗ[ℚ] ULift.{u} ((L s).X n))).toModuleIso
  have hei : ∀ s i j, (ComplexShape.down ℕ).Rel i j →
      (ei s i).hom ≫ (LF s).d i j = (K s).d i j ≫ (ei s j).hom := by
    intro s i j hij
    have hij' : j + 1 = i := hij
    subst i
    ext x
    exact congrArg ULift.up (he s j x).symm
  let E (s : ι) : K s ≅ LF s := HomologicalComplex.Hom.isoOfComponents (ei s) (hei s)
  refine ⟨E, (by intro s n x; rfl), ?_⟩
  intro k
  let q (s : ι) : (LF s).homology k ≅ F.obj ((L s).homology k) :=
    ((L s).sc k).mapHomologyIso F
  let H (s : ι) : (K s).homology k ≅ F.obj ((L s).homology k) :=
    HomologicalComplex.homologyMapIso (E s) k ≪≫ q s
  let h (s : ι) : (K s).homology k ≃ₗ[ℚ] (L s).homology k :=
    (H s).toLinearEquiv.trans ULift.moduleEquiv
  refine ⟨h, ?_⟩
  intro s t a b hab
  have hs : a ≫ (E t).hom = (E s).hom ≫
      (F.mapHomologicalComplex (.down ℕ)).map b := by
    ext n x
    exact congrArg ULift.up (hab n x)
  have hh := congrArg (fun f ↦ HomologicalComplex.homologyMap f k) hs
  simp only [HomologicalComplex.homologyMap_comp] at hh
  have hq := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℚ) (.down ℕ) k).map b) F
  intro x
  exact congrArg ULift.down (congrArg (fun f ↦ f.hom x)
    (show HomologicalComplex.homologyMap a k ≫ (H t).hom =
      (H s).hom ≫ F.map (HomologicalComplex.homologyMap b k) by
        change HomologicalComplex.homologyMap a k ≫
          (HomologicalComplex.homologyMap (E t).hom k ≫ (q t).hom) =
          (HomologicalComplex.homologyMap (E s).hom k ≫ (q s).hom) ≫
            F.map (HomologicalComplex.homologyMap b k)
        rw [← Category.assoc, hh, Category.assoc]
        exact congrArg (fun f ↦ HomologicalComplex.homologyMap (E s).hom k ≫ f) hq))

end HolomorphicAnosov
