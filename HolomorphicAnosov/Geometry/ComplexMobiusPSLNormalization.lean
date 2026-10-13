import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
namespace HolomorphicAnosov
open Ghys Matrix

private theorem matrix_exists_psl_action (A : GL (Fin 2) ℂ) :
    ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      ∀ z : ComplexProjectiveLine, g • z = A • z := by
  obtain ⟨r, hr⟩ := Complex.isSquare (Matrix.det (A : Matrix (Fin 2) (Fin 2) ℂ))
  have hr0 : r ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simpa [h] using hr
  let B : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
    ⟨r⁻¹ • (A : Matrix (Fin 2) (Fin 2) ℂ), by
      rw [Matrix.det_smul]
      simp only [Fintype.card_fin]
      rw [hr]
      field_simp⟩
  refine ⟨B, ?_⟩
  intro z
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
  induction z using Projectivization.ind with
  | _ v hv =>
    rw [Projectivization.smul_mk, Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff']
    refine ⟨r⁻¹, ?_⟩
    change r⁻¹ • ((A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) =
      (r⁻¹ • (A : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v
    simp [mul_add, mul_assoc]

/-- Every effective complex projective linear transformation has a unique representative in PSL(2,ℂ) with the same action on the homogeneous projective line. (Ghys, §5, p. 597). -/
theorem complex_mobius_psl_normalization (g : ComplexMobiusTransformation) :
    ∃! h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      ∀ z : ComplexProjectiveLine, h • z = g.apply z := by
  obtain ⟨A, hA⟩ := g.property
  obtain ⟨h, hh⟩ := matrix_exists_psl_action A
  refine ⟨h, fun z ↦ (hh z).trans (hA z).symm, ?_⟩
  intro k hk
  exact FaithfulSMul.eq_of_smul_eq_smul (α := ComplexProjectiveLine) fun z ↦ (hk z).trans ((hA z).trans (hh z).symm)

/-- The effective GL(2,ℂ) projective-action group is isomorphic to PSL(2,ℂ), preserving the action on every projective point. (Ghys, §5, p. 597). -/
theorem effective_complex_mobius_psl_equiv :
    let G := (MulAction.toPermHom (GL (Fin 2) ℂ) ComplexProjectiveLine).range
    ∃ e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      ∀ g : G, ∀ z : ComplexProjectiveLine, e g • z = g.val z := by
  classical
  intro G
  have hex : ∀ g : G, ∃ h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      ∀ z : ComplexProjectiveLine, h • z = g.val z := by
    intro g
    obtain ⟨A, hA⟩ := g.property
    obtain ⟨h, hh⟩ := matrix_exists_psl_action A
    refine ⟨h, ?_⟩
    intro z
    exact (hh z).trans (congrArg (fun σ : Equiv.Perm ComplexProjectiveLine ↦ σ z) hA)
  choose h hh using hex
  let φ : G →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ := {
    toFun := h
    map_one' := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := ComplexProjectiveLine)
      intro z
      rw [one_smul]
      exact hh 1 z
    map_mul' := fun a b ↦ FaithfulSMul.eq_of_smul_eq_smul (α := ComplexProjectiveLine) fun z ↦ by
      rw [mul_smul, hh, hh, hh]
      rfl }
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Equiv.ext
    intro z
    exact (hh a z).symm.trans ((congrArg (fun g ↦ g • z) hab).trans (hh b z))
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H B =>
      let g : G := ⟨MulAction.toPerm (B : GL (Fin 2) ℂ), ⟨B, rfl⟩⟩
      refine ⟨g, FaithfulSMul.eq_of_smul_eq_smul (α := ComplexProjectiveLine) fun z ↦ ?_⟩
      change h g • z = (B : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) • z
      rw [hh, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
      induction z using Projectivization.ind with
      | _ v hv => rfl
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, hh⟩

end HolomorphicAnosov

