import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! The composite of an immersion and a map whose derivative vanishes on the immersion
distribution has zero manifold derivative. -/

open Set Topology _root_.Topology
open scoped Manifold

namespace HolomorphicAnosov.Theorem12PlaqueSupport

variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable (I : ModelWithCorners ℝ E H)

theorem transverse_comp_mfderiv_zero
    (j : N → M) (hj : MDifferentiable (modelWithCornersSelf ℝ G) I j)
    (P : (x : M) → Submodule ℝ (TangentSpace I x))
    (hP : ∀ z, LinearMap.range
      (mfderiv (modelWithCornersSelf ℝ G) I j z).toLinearMap = P (j z))
    (τ : M → F) {z : N} (hτ : MDifferentiableAt I (modelWithCornersSelf ℝ F) τ (j z))
    (hkill : ∀ v ∈ P (j z), mfderiv I (modelWithCornersSelf ℝ F) τ (j z) v = 0) :
    mfderiv (modelWithCornersSelf ℝ G) (modelWithCornersSelf ℝ F) (τ ∘ j) z = 0 := by
  rw [mfderiv_comp z hτ (hj z)]
  ext v
  apply hkill
  rw [← hP z]
  exact ⟨v, rfl⟩

end HolomorphicAnosov.Theorem12PlaqueSupport
