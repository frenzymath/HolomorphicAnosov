import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataG8

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- Apply the published fixed-block conversion to the ORIGINAL Anosov datum. -/
theorem covering_conjugacy_tensor_bounds_g15
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f) :
    ∃ b : TensorAnosovBounds f.toReal a.splitting a.metric, 1 ≤ b.C := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C, lam, hC, hlam, hlam1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
  have hi (x : X) (v w : TangentSpace (realModel d) x) :
      inner ℝ v w = a.metric.inner x v w := rfl
  refine ⟨{ C := max C 1
            lambda := lam
            C_pos := lt_of_lt_of_le hC (le_max_left _ _)
            lambda_pos := hlam
            lambda_lt_one := hlam1
            stable := ?_
            unstable := ?_ }, le_max_right _ _⟩
  · intro n x v hv
    have h := (hs n x v hv).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hlam.le n))
        (norm_nonneg v))
    change Real.sqrt (a.metric.inner ((f : X → X)^[n] x)
      (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x v)
      (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x v)) ≤ _
    simpa only [norm_eq_sqrt_real_inner, hi] using h
  · intro n x v hv
    have h := (hu n x v hv).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hlam.le n))
        (norm_nonneg v))
    change Real.sqrt (a.metric.inner ((f.symm : X → X)^[n] x)
      (mfderiv (realModel d) (realModel d) ((f.symm : X → X)^[n]) x v)
      (mfderiv (realModel d) (realModel d) ((f.symm : X → X)^[n]) x v)) ≤ _
    simpa only [norm_eq_sqrt_real_inner, hi] using h


end HolomorphicAnosov
