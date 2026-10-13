import HolomorphicAnosov.Targets.Theorem12Support.IntegerCoordinateLattice
import HolomorphicAnosov.Targets.Theorem12Support.IntegerLatticePreservation
import HolomorphicAnosov.Targets.Theorem12Support.RealMatrixComplexification
import HolomorphicAnosov.Targets.Theorem12Support.RealQuotientTorus
import HolomorphicAnosov.Targets.Theorem12Support.RealToralModel
import HolomorphicAnosov.Targets.Theorem12Support.LatticeQuotientTopology

section
universe u
namespace HolomorphicAnosov.Theorem12RealToralModel
open HolomorphicAnosov.IntegerCoordinateLattice
open HolomorphicAnosov.Theorem12RealQuotientTorus

/-- A hyperbolic integral toral conjugacy yields a conjugacy to a real linear automorphism on the
compact quotient by a discrete full coordinate lattice. The automorphism preserves the lattice,
and its complexification has no eigenvalue of modulus one. (Zhang, §3, p. 11) -/
theorem real_toral_model_of_hyperbolic_conjugacy {n : ℕ} {X : Type u}
    [TopologicalSpace X] (f : X → X) (hmodel : HyperbolicRealToralConjugacy n X f) :
    let Γ := integerLattice n
    DiscreteTopology Γ ∧
    IsZLattice ℝ Γ ∧
    Submodule.span ℝ (Γ : Set (Fin n → ℝ)) = ⊤ ∧
    Module.finrank ℝ (Fin n → ℝ) = n ∧
    CompactSpace ((Fin n → ℝ) ⧸ Γ.toAddSubgroup) ∧
    ∃ (R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
      (hq : X ≃ₜ ((Fin n → ℝ) ⧸ Γ.toAddSubgroup)),
      R '' (Γ : Set (Fin n → ℝ)) = (Γ : Set (Fin n → ℝ)) ∧
      (∀ μ : ℂ, Module.End.HasEigenvalue
        (R.toLinearEquiv.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) ∧
      ∀ x v, (QuotientAddGroup.mk v : (Fin n → ℝ) ⧸ Γ.toAddSubgroup) = hq x →
        hq (f x) = QuotientAddGroup.mk (R v) := by
  dsimp only
  obtain ⟨A, h, hhyper, hconj⟩ := hmodel
  let E := quotientTorusHomeomorph n
  let hq := h.trans E.symm
  refine ⟨ZSpan.discreteTopology_pi_basisFun, inferInstance,
    ZSpan.span_top (Pi.basisFun ℝ (Fin n)), Module.finrank_fin_fun ℝ,
    IntegerCoordinateQuotient.latticeQuotient_compact n, realCLE A, hq, ?_, ?_, ?_⟩
  · apply IntegerLatticePreservation.integer_gl_image_lattice _ _ A
    intro v
    simpa [integerLattice, eq_comm] using (Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ v
  · intro μ hμ
    apply hhyper μ
    simpa using Theorem12MatrixScratch.hasEigenvalue_complex_matrix_of_baseChange
      (fun i j ↦ (A i j : ℝ)) μ hμ
  · intro x v hv
    apply E.injective
    have heq : h x = E (QuotientAddGroup.mk v) := by
      rw [hv]
      exact (E.apply_symm_apply (h x)).symm
    change E (E.symm (h (f x))) = E (QuotientAddGroup.mk (realCLE A v))
    rw [E.apply_symm_apply, hconj, heq]
    exact (coordinateProjection_mulVec A v).symm

end HolomorphicAnosov.Theorem12RealToralModel
end
