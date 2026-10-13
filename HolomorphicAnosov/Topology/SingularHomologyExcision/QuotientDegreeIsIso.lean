import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions
import HolomorphicAnosov.Topology.SingularHomologyExcision.PairProjectionNaturality

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u w
variable {K : Type w} [CommRing K]

namespace HolomorphicAnosov

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Hatcher's quotient calculation holds for arbitrary coefficient groups, degreewise.
Source: excision proof p.124 and coefficients p.153. The inverse discards precisely the
A-supported summands; the canonical native cokernel performs the descent. -/
theorem excision_quotient_degree_isIso
    (X : TopCat.{u}) (A B : Set X) (R : ModuleCat.{u} K) (n : ℕ) :
    IsIso ((SSetPair.chainComplexMap (singularExcisionQuotientInclusion X A B) R).f n) := by
  classical
  let a := singularSubspace X A
  let b := singularSubspace X B
  let U : SSet.{u} := (a ⊔ b : (TopCat.toSSet.obj X).Subcomplex)
  let P := singularIntersectionPair X A B
  let Q := singularExcisionSmallPair X A B
  let q := (SSetPair.chainComplexMap (singularExcisionQuotientInclusion X A B) R).f n
  let πP := (P.chainComplexπ R).f n
  let πQ := (Q.chainComplexπ R).f n
  have hQ : ∀ x : a.obj (op ⦋n⦌),
      U.ιChainComplex (R := R) ⟨x.val, Or.inl x.property⟩ ≫ πQ = 0 := by
    intro x
    have h := congrArg (fun g ↦ a.toSSet.ιChainComplex (R := R) x ≫ g)
      (Q.chainComplex_condition_f R n)
    change _ ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE le_sup_left) R).f n ≫ _ = _ at h
    simp only [SSet.ι_chainComplexMap_f_assoc, comp_zero] at h
    change U.ιChainComplex (R := R) ⟨x.val, Or.inl x.property⟩ ≫ πQ = 0 at h
    exact h
  have hP : ∀ x : (a ⊓ b).obj (op ⦋n⦌),
      b.toSSet.ιChainComplex (R := R) ⟨x.val, x.property.2⟩ ≫ πP = 0 := by
    intro x
    have h := congrArg (fun g ↦ (a ⊓ b).toSSet.ιChainComplex (R := R) x ≫ g)
      (P.chainComplex_condition_f R n)
    change _ ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE inf_le_right) R).f n ≫ _ = _ at h
    simp only [SSet.ι_chainComplexMap_f_assoc, comp_zero] at h
    change b.toSSet.ιChainComplex (R := R) ⟨x.val, x.property.2⟩ ≫ πP = 0 at h
    exact h
  let t : ∀ x : U _⦋n⦌, R ⟶ (P.chainComplex R).X n := fun x ↦
    if hx : x.val ∈ a.obj (op ⦋n⦌) then 0
    else b.toSSet.ιChainComplex (R := R)
      ⟨x.val, x.property.resolve_left hx⟩ ≫ πP
  let l : (U.chainComplex R).X n ⟶ (P.chainComplex R).X n := Sigma.desc t
  have hlt : ∀ x : U _⦋n⦌, U.ιChainComplex (R := R) x ≫ l = t x := by
    intro x
    exact Sigma.ι_comp_desc t x
  have hz : (SSet.chainComplexMap Q.hom R).f n ≫ l = 0 := by
    apply SSet.chainComplex_hom_ext
    intro x
    change a.toSSet.ιChainComplex x ≫
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE le_sup_left) R).f n ≫ l = _
    rw [SSet.ι_chainComplexMap_f_assoc, hlt]
    simp [t]
  obtain ⟨r, hr⟩ := CokernelCofork.IsColimit.desc' (Q.isColimitCokernelCoforkChainComplexX R n) l hz
  change πQ ≫ r = l at hr
  have hnat : πP ≫ q =
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (S₁ := b) le_sup_right) R).f n ≫ πQ :=
    pair_projection_naturality (singularExcisionQuotientInclusion X A B) R n
  have hqr : q ≫ r = 𝟙 _ := by
    apply (cancel_epi πP).mp
    rw [← Category.assoc, hnat, Category.assoc, hr, Category.comp_id]
    change (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (S₁ := b) le_sup_right) R).f n ≫ l = πP
    apply SSet.chainComplex_hom_ext
    intro x
    rw [SSet.ι_chainComplexMap_f_assoc, hlt]
    by_cases hx : x.val ∈ a.obj (op ⦋n⦌)
    · simpa [t, hx] using (hP ⟨x.val, hx, x.property⟩).symm
    · simp [t, hx]
  have hrq : r ≫ q = 𝟙 _ := by
    apply (cancel_epi πQ).mp
    rw [← Category.assoc, hr]
    change l ≫ q = πQ
    apply SSet.chainComplex_hom_ext
    intro x
    rw [← Category.assoc, hlt]
    by_cases hx : x.val ∈ a.obj (op ⦋n⦌)
    · simpa [t, hx] using (hQ ⟨x.val, hx⟩).symm
    · simp only [t, dite_eq_right hx, Category.assoc, hnat,
        SSet.ι_chainComplexMap_f_assoc]
      rfl
  exact ⟨⟨r, hqr, hrq⟩⟩


end
end HolomorphicAnosov

