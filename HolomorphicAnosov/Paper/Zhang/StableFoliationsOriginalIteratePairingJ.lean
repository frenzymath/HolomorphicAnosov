import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalIterateDerivativeCommutesJ

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The images of `v` and `Jv` under the derivative of a holomorphic iterate have equal Hermitian
quadratic norms. (Ghys, Lemma 2.1, p.589) -/
theorem original_iterate_pairing_J
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (h : HermitianTangentMetricCore d M)
    (n : ℕ) (x : M) (v : TangentSpace (realModel d) x) :
    let D := mfderiv (realModel d) (realModel d)
      (realIterate (realModel d) f.toReal n) x
    let Jv := complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v)
    hermitianTangentRealPairing h ((f : M → M)^[n] x) (D Jv) (D Jv) =
      hermitianTangentRealPairing h ((f : M → M)^[n] x) (D v) (D v) := by
  dsimp only
  rw [original_iterate_derivative_commutes_J]
  exact real_pairing_J h _ _

end StableFoliationsSupport
end HolomorphicAnosov
