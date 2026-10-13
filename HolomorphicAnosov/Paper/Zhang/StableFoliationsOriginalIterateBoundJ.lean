import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalIteratePairingJ

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- A Hermitian derivative-growth bound for `v` under a holomorphic iterate also holds for `Jv`.
(Ghys, Lemma 2.1, p.589) -/
theorem original_iterate_bound_J
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (h : HermitianTangentMetricCore d M)
    (n : ℕ) (x : M) (v : TangentSpace (realModel d) x) (A : ℝ)
    (hv : Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
      (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)
      (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)) ≤
      A * Real.sqrt (hermitianTangentRealPairing h x v v)) :
    let Jv := complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v)
    Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
      (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x Jv)
      (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x Jv)) ≤
      A * Real.sqrt (hermitianTangentRealPairing h x Jv Jv) := by
  dsimp only
  rw [original_iterate_pairing_J, real_pairing_J]
  exact hv

end StableFoliationsSupport
end HolomorphicAnosov
