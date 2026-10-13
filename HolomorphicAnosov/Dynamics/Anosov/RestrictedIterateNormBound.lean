import HolomorphicAnosov.Analysis.QuotientTimeToExponential
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov
universe u
namespace UniformIterateBounds
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)]

omit [IsManifold I ∞ X] in
/-- The operator norm in the original Anosov datum controls the literal restricted derivative.
No replacement of the source tangent subspace or of its metric is involved. -/
theorem restricted_iterate_norm_le
    (f : Diffeomorph I I X X ∞) (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I f x).toLinearMap = P (f x))
    (n : ℕ) (x : X) (v : TangentSpace I x) (hv : v ∈ P x) :
    ‖mfderiv I I ((f : X → X)^[n]) x v‖ ≤
      ‖(restrictedIterateDerivative f P hP n x).toContinuousLinearMap‖ * ‖v‖ := by
  exact (restrictedIterateDerivative f P hP n x).toContinuousLinearMap.le_opNorm ⟨v, hv⟩

end UniformIterateBounds
end HolomorphicAnosov
