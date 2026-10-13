import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Pointwise real immersions into a finite-dimensional complex manifold admit a fixed complement of
dimension `2*d-r`. -/

noncomputable section
open scoped ContDiff Manifold
namespace HolomorphicAnosov

/-- Pointwise real immersion into a finite-dimensional complex manifold gives a global immersion
with fixed complement `Fin (2*d-r) → ℝ`. -/
theorem real_immersion_of_pointwise_into_complex_model_g1
    {r d : ℕ} {L M : Type*}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    {n : ℕ∞ω} {f : L → M}
    (hf : ∀ x, Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) (realModel d) n f x) :
    Manifold.IsImmersion 𝓘(ℝ, Fin r → ℝ) (realModel d) n f := by
  refine ⟨Fin (2*d-r) → ℝ, inferInstance, inferInstance, ?_⟩
  intro x
  let h := hf x
  let : FiniteDimensional ℝ ((Fin r → ℝ) × h.complement) :=
    FiniteDimensional.of_injective h.equiv.toLinearEquiv.toLinearMap h.equiv.injective
  let : FiniteDimensional ℝ h.complement :=
    FiniteDimensional.of_injective (LinearMap.inr ℝ (Fin r → ℝ) h.complement)
      (by intro v w heq; exact congrArg Prod.snd heq)
  have he := h.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at he
  have hdim : r + Module.finrank ℝ h.complement = 2*d := by
    simpa [ComplexModel, finrank_real_of_complex] using he
  let e : h.complement ≃L[ℝ] (Fin (2*d-r) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [Module.finrank_pi, Fintype.card_fin]
      omega)
  exact h.isImmersionAtOfComplement_complement.trans_F e

end HolomorphicAnosov
