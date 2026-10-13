import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_tube_laws
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_inverse_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_frame
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_centered_frame_domain
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_radius

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] in
/-- For a smooth function on an open product domain, each iterated derivative in the fiber variables
equals the total iterated derivative restricted to vertical arguments. (HPS, p. 62) -/
theorem vertical_jet_restriction
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Q : F × E → G) (D : Set (F × E)) (hD : IsOpen D)
    (n : ℕ∞ω) (hQ : ContDiffOn ℝ n Q D)
    (p : F) (w : E) (hpw : (p, w) ∈ D) (j : ℕ) (hj : j ≤ n) :
    iteratedFDeriv ℝ j (fun u ↦ Q (p, u)) w =
      (iteratedFDeriv ℝ j Q (p, w)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ F E) := by
  let a : F × E := (p, 0)
  let T : F × E → F × E := fun z ↦ a + z
  let S : Set (F × E) := T ⁻¹' D
  let i : E →L[ℝ] F × E := ContinuousLinearMap.inr ℝ F E
  have hS : IsOpen S := hD.preimage (continuous_const.add continuous_id)
  have hiS : IsOpen (i ⁻¹' S) := hS.preimage i.continuous
  have hiw : i w ∈ S := by simpa [S, T, a, i] using hpw
  have hQT : ContDiffOn ℝ n (fun z ↦ Q (a + z)) S :=
    hQ.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ h ↦ h)
  have hshift : a +ᵥ S = D := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      refine ⟨-a + z, ?_, ?_⟩
      · simpa [S, T, add_assoc] using hz
      · simp
  have h := i.iteratedFDerivWithin_comp_right hQT hS.uniqueDiffOn hiS.uniqueDiffOn hiw hj
  rw [iteratedFDerivWithin_of_isOpen j hiS hiw] at h
  rw [iteratedFDerivWithin_comp_add_left, hshift] at h
  rw [iteratedFDerivWithin_of_isOpen j hD (by simpa [a, i] using hpw)] at h
  simpa [Function.comp_def, a, i] using h


end ExponentialLift
end HolomorphicAnosov
