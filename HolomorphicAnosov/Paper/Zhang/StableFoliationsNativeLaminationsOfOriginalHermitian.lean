import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetric
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetricInner
import HolomorphicAnosov.Paper.Zhang.StableFoliationsNativeLaminationsOfExactPairing

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- Exponential stable and inverse-unstable bounds for a smooth Hermitian metric give native real
laminations tangent to both distributions. -/
theorem native_laminations_of_original_hermitian
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M)
    (h : HermitianTangentMetricCore d M)
    (hh : IsSmoothHermitianTangentMetric h)
    (P : InvariantRealTangentSplitting f.toReal)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate ∧ rate < 1)
    (hs : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.stable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v))
    (hu : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.unstable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) :
    HPS.HasNativeLamination P.stable.toDistribution f.toReal (fun _ _ _ ↦ True) ∧
    HPS.HasNativeLamination P.unstable.toDistribution f.toReal (fun _ _ _ ↦ True) := by
  exact native_laminations_of_exact_pairing f h hh P C rate hC hrate hs hu
    (originalSmoothRealMetric h hh) (originalSmoothRealMetric_inner h hh)

end StableFoliationsSupport
end HolomorphicAnosov
