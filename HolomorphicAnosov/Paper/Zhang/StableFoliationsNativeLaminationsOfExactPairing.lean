import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import HolomorphicAnosov.Paper.Zhang.StableFoliationsTensorBoundsOfExactPairing

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- Exponential stable and inverse-unstable bounds in a smooth metric equal to the real Hermitian
pairing give native real laminations tangent to both distributions. -/
theorem native_laminations_of_exact_pairing
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
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v))
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (hg : ∀ x v w, g.inner x v w = hermitianTangentRealPairing h x v w) :
    HPS.HasNativeLamination P.stable.toDistribution f.toReal (fun _ _ _ ↦ True) ∧
    HPS.HasNativeLamination P.unstable.toDistribution f.toReal (fun _ _ _ ↦ True) := by
  exact HPS.anosov_global_lamination_tensor f.toReal P g
    (tensor_bounds_of_exact_pairing f h hh P C rate hC hrate hs hu g hg)

end StableFoliationsSupport
end HolomorphicAnosov
