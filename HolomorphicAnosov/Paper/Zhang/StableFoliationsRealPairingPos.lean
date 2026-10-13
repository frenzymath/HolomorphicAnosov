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

/-- The real Hermitian quadratic form is strictly positive on nonzero tangent vectors. (Moroianu,
§5.1, p.27) -/
theorem real_pairing_pos {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] (h : HermitianTangentMetricCore d M)
    (x : M) (v : TangentSpace (realModel d) x) (hv : v ≠ 0) :
    0 < hermitianTangentRealPairing h x v v := by
  let : InnerProductSpace.Core ℂ (TangentSpace (complexModel d) x) := h x
  change 0 < ((h x).inner ((complexTangentToReal d x).symm v)
    ((complexTangentToReal d x).symm v)).re
  apply lt_of_le_of_ne ((h x).re_inner_nonneg ((complexTangentToReal d x).symm v))
  intro hz
  have hz' : InnerProductSpace.Core.normSq ((complexTangentToReal d x).symm v) = 0 := hz.symm
  have hv' := InnerProductSpace.Core.normSq_eq_zero.mp hz'
  exact hv ((complexTangentToReal d x).symm.injective (by simpa using hv'))

end StableFoliationsSupport
end HolomorphicAnosov
