import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The transported complex structure preserves the real Hermitian quadratic form. (Demailly, I
§3.C, p.23; Moroianu, §5.1, p.27) -/
theorem real_pairing_J {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] (h : HermitianTangentMetricCore d M)
    (x : M) (v : TangentSpace (realModel d) x) :
    hermitianTangentRealPairing h x
      (complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v))
      (complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v)) =
    hermitianTangentRealPairing h x v v := by
  let : InnerProductSpace.Core ℂ (TangentSpace (complexModel d) x) := h x
  simp only [hermitianTangentRealPairing, hermitianTangentPairing,
    ContinuousLinearEquiv.symm_apply_apply]
  let : Inner ℂ (TangentSpace (complexModel d) x) := (h x).toInner
  change (inner ℂ (Complex.I • (complexTangentToReal d x).symm v)
    (Complex.I • (complexTangentToReal d x).symm v)).re = _
  rw [InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right]
  simp

end StableFoliationsSupport
end HolomorphicAnosov
