import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Analysis.MovingOperatorNormStrictLocalBound
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeForwardInverse
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward
import HolomorphicAnosov.Geometry.DiffeomorphInverseIterateBasepoint
import HolomorphicAnosov.Geometry.DiffeomorphForwardInverseIterateBasepoint
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov.FixedBlockEstimates.Inverse
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- Forward derivative invariance gives invariance under the original inverse map. -/
theorem inverse_distribution_invariant (g : Diffeomorph I I X X ∞)
    (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x)) (x : X) :
    (P x).map (mfderiv I I g.symm x).toLinearMap = P (g.symm x) := by
  have hmap := hP (g.symm x)
  rw [g.apply_symm_apply] at hmap
  have hleft (w : TangentSpace I (g.symm x)) :
      mfderiv I I g.symm x (mfderiv I I g (g.symm x) w) = w := by
    have hh := HolomorphicAnosov.derivative_inverse_forward g (g.symm x) w
    rw [g.apply_symm_apply] at hh
    exact hh
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [← hmap] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    subst u
    change mfderiv I I g.symm x (mfderiv I I g (g.symm x) w) ∈ P (g.symm x)
    rw [hleft]
    exact hw
  · intro hv
    refine ⟨mfderiv I I g (g.symm x) v, ?_, ?_⟩
    · rw [← hmap]
      exact ⟨v, hv, rfl⟩
    · exact hleft v

end HolomorphicAnosov.FixedBlockEstimates.Inverse
