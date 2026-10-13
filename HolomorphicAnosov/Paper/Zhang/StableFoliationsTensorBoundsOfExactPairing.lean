import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- Stable and inverse-unstable Hermitian contraction estimates give tensor Anosov bounds for a
smooth real metric equal to the real Hermitian pairing. (HPS, 2.8–2.9, pp.13–15) -/
theorem tensor_bounds_of_exact_pairing
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M)
    (h : HermitianTangentMetricCore d M)
    (_hh : IsSmoothHermitianTangentMetric h)
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
    Nonempty (TensorAnosovBounds f.toReal P g) := by
  refine ⟨⟨C, rate, hC, hrate.1, hrate.2, ?_, ?_⟩⟩
  · intro n x v hv
    simp only [hg]
    exact hs n x v hv
  · intro n x v hv
    simp only [hg]
    exact hu n x v hv

end StableFoliationsSupport
end HolomorphicAnosov
