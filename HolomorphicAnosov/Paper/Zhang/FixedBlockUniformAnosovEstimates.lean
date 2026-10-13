import HolomorphicAnosov.Dynamics.Anosov.InverseDistributionInvariant
import HolomorphicAnosov.Dynamics.Anosov.DerivativeEquivSymmApply
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateSymmVal
import HolomorphicAnosov.Dynamics.Anosov.InverseIterateNormLeAtForward
import HolomorphicAnosov.Dynamics.Anosov.InverseIterateNormLeOfBasepoint
import HolomorphicAnosov.Dynamics.Anosov.InverseIterateNormLe
import HolomorphicAnosov.Dynamics.Anosov.InverseIterateBoundOfOperatorBound
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm
import HolomorphicAnosov.Geometry.ContinuousFrameTotalSpace
import HolomorphicAnosov.Geometry.ContinuousOriginalFrameNorms
import HolomorphicAnosov.Geometry.ContinuousRestrictedFrameNorms
import HolomorphicAnosov.Geometry.RestrictedOpNormEventuallyLt
import HolomorphicAnosov.Geometry.RestrictedOpNormEventuallyLe
import HolomorphicAnosov.Geometry.AmbientOpNormEventuallyLt
import HolomorphicAnosov.Geometry.RestrictedInverseOpNormAtForward
import HolomorphicAnosov.Topology.CompactFiniteLocalBound
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeForwardInverse
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward
import HolomorphicAnosov.Geometry.DiffeomorphInverseIterateBasepoint
import HolomorphicAnosov.Geometry.DiffeomorphForwardInverseIterateBasepoint
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateNormBound
import HolomorphicAnosov.Dynamics.Anosov.AllIterateBoundOfUniformBlock
import HolomorphicAnosov.Analysis.MovingOperatorNormStrictLocalBound
import HolomorphicAnosov.Analysis.QuotientTimeToExponential
import HolomorphicAnosov.Analysis.CommonExponentialConstants
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Topology.CompactLocalUpperBound
import HolomorphicAnosov.Topology.CompactCommonLocalStrictBound
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! This file derives uniform all-iterate estimates from the fixed-block Anosov bounds. (Zhang, p. 1) -/
noncomputable section
noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle

namespace HolomorphicAnosov.FixedBlockEstimates.Moving

universe u v w z

end HolomorphicAnosov.FixedBlockEstimates.Moving




namespace HolomorphicAnosov.FixedBlockEstimates.Native

attribute [local instance] complex_isManifold_real

universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original Anosov stable block has a strict local upper bound at every base point. -/
private theorem original_stable_local_bounds {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (a : AnosovDatum f) :
    letI : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∀ x : X, ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative f.toReal a.splitting.stable.toDistribution
        a.splitting.stable_map a.k y).toContinuousLinearMap‖ ≤ q := by
  let := complex_isManifold_real d X
  let : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro x
  exact restricted_opNorm_eventually_le a.splitting.stable a.metric f.toReal
    a.splitting.stable_map a.k x (a.stable_contracting x)


/-- The original unstable inverse block has a strict local upper bound. -/
private theorem original_unstable_local_bounds {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (a : AnosovDatum f) :
    letI : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∀ x : X, ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative f.toReal a.splitting.unstable.toDistribution
        a.splitting.unstable_map a.k y).symm.toContinuousLinearMap‖ ≤ q := by
  let := complex_isManifold_real d X
  let : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro x
  have hc : ‖(restrictedIterateDerivative f.toReal.symm
      a.splitting.unstable.toDistribution
      (FixedBlockEstimates.Inverse.inverse_distribution_invariant f.toReal
        a.splitting.unstable.toDistribution a.splitting.unstable_map) a.k
      (((f.toReal : X → X)^[a.k]) x)).toContinuousLinearMap‖ < 1 := by
    rw [← restricted_inverse_opNorm_at_forward a.splitting.unstable.toDistribution
      a.metric f.toReal a.splitting.unstable_map a.k x]
    exact a.unstable_contracting x
  obtain ⟨q, hq0, hq1, hlocal⟩ := restricted_opNorm_eventually_le
    a.splitting.unstable a.metric f.toReal.symm
    (FixedBlockEstimates.Inverse.inverse_distribution_invariant f.toReal
      a.splitting.unstable.toDistribution a.splitting.unstable_map) a.k
    (((f.toReal : X → X)^[a.k]) x) hc
  have hnear := ((f.toReal.contMDiff.iterate a.k).continuous.continuousAt).eventually
    hlocal
  refine ⟨q, hq0, hq1, hnear.mono fun y hy ↦ ?_⟩
  rw [restricted_inverse_opNorm_at_forward a.splitting.unstable.toDistribution
    a.metric f.toReal a.splitting.unstable_map a.k y]
  exact hy

/-- Every finite forward residue has a local upper bound in the original metric. -/
private theorem original_forward_residue_local_bounds {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (a : AnosovDatum f) :
    letI : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∀ r : Fin a.k, ∀ x : X, ∃ q : ℝ, ∀ᶠ y in 𝓝 x,
      ‖mfderiv (realModel d) (realModel d) ((f : X → X)^[r.val]) y‖ ≤ q := by
  let := complex_isManifold_real d X
  let : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro r x
  refine ⟨‖mfderiv (realModel d) (realModel d) ((f : X → X)^[r.val]) x‖ + 1, ?_⟩
  exact (ambient_opNorm_eventually_lt a.metric _
    (f.toReal.contMDiff.iterate r.val) x (lt_add_one _)).mono fun _ hy ↦ hy.le

/-- Every finite backward residue has a local upper bound in the original metric. -/
private theorem original_backward_residue_local_bounds {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (a : AnosovDatum f) :
    letI : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∀ r : Fin a.k, ∀ x : X, ∃ q : ℝ, ∀ᶠ y in 𝓝 x,
      ‖mfderiv (realModel d) (realModel d) ((f.symm : X → X)^[r.val]) y‖ ≤ q := by
  let := complex_isManifold_real d X
  let : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro r x
  refine ⟨‖mfderiv (realModel d) (realModel d) ((f.symm : X → X)^[r.val]) x‖ + 1, ?_⟩
  exact (ambient_opNorm_eventually_lt a.metric _
    (f.toReal.symm.contMDiff.iterate r.val) x (lt_add_one _)).mono fun _ hy ↦ hy.le


end HolomorphicAnosov.FixedBlockEstimates.Native


namespace HolomorphicAnosov.FixedBlockEstimates.Compact
open scoped Bundle ContDiff Topology _root_.Topology
section OriginalDatum
attribute [local instance] complex_isManifold_real

/-- Internal compact assembly on the literal original Anosov datum. -/
private theorem original_uniform_bounds_of_local_bounds {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M) (a : AnosovDatum f) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    (∀ x, ∃ q : ℝ, q < 1 ∧ ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative f.toReal a.splitting.stable.toDistribution
        a.splitting.stable_map a.k y).toContinuousLinearMap‖ ≤ q) →
    (∀ x, ∃ q : ℝ, q < 1 ∧ ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative f.toReal a.splitting.unstable.toDistribution
        a.splitting.unstable_map a.k y).symm.toContinuousLinearMap‖ ≤ q) →
    (∀ (r : Fin a.k) x, ∃ q : ℝ, ∀ᶠ y in 𝓝 x,
      ‖mfderiv (realModel d) (realModel d) ((f : M → M)^[r.val]) y‖ ≤ q) →
    (∀ (r : Fin a.k) x, ∃ q : ℝ, ∀ᶠ y in 𝓝 x,
      ‖mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[r.val]) y‖ ≤ q) →
    ∃ theta R : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < R ∧
      (∀ x, ‖(restrictedIterateDerivative f.toReal a.splitting.stable.toDistribution
        a.splitting.stable_map a.k x).toContinuousLinearMap‖ ≤ theta) ∧
      (∀ x, ‖(restrictedIterateDerivative f.toReal a.splitting.unstable.toDistribution
        a.splitting.unstable_map a.k x).symm.toContinuousLinearMap‖ ≤ theta) ∧
      (∀ (r : Fin a.k) x,
        ‖mfderiv (realModel d) (realModel d) ((f : M → M)^[r.val]) x‖ ≤ R) ∧
      (∀ (r : Fin a.k) x,
        ‖mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[r.val]) x‖ ≤ R) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro hs hu hrf hri
  obtain ⟨theta, ht0, ht1, hsb, hub⟩ := HolomorphicAnosov.compact_common_local_strict_bound _ _ hs hu
  obtain ⟨Rf, hRf, hfb⟩ := HolomorphicAnosov.compact_finite_local_residue_bound _ hrf
  obtain ⟨Ri, hRi, hib⟩ := HolomorphicAnosov.compact_finite_local_residue_bound _ hri
  refine ⟨theta, max Rf Ri, ht0, ht1, lt_of_lt_of_le hRf (le_max_left _ _),
    hsb, hub, fun r x ↦ (hfb r x).trans (le_max_left _ _),
    fun r x ↦ (hib r x).trans (le_max_right _ _)⟩

/-- The exact original stable and inverse-unstable distributions satisfy one pair of all-time Anosov estimates once their native local upper bounds are supplied. -/
private theorem original_all_iterates_of_local_bounds {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M) (a : AnosovDatum f) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    (∀ x, ∃ q : ℝ, q < 1 ∧ ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative f.toReal a.splitting.stable.toDistribution
        a.splitting.stable_map a.k y).toContinuousLinearMap‖ ≤ q) →
    (∀ x, ∃ q : ℝ, q < 1 ∧ ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative f.toReal a.splitting.unstable.toDistribution
        a.splitting.unstable_map a.k y).symm.toContinuousLinearMap‖ ≤ q) →
    (∀ (r : Fin a.k) x, ∃ q : ℝ, ∀ᶠ y in 𝓝 x,
      ‖mfderiv (realModel d) (realModel d) ((f : M → M)^[r.val]) y‖ ≤ q) →
    (∀ (r : Fin a.k) x, ∃ q : ℝ, ∀ᶠ y in 𝓝 x,
      ‖mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[r.val]) y‖ ≤ q) →
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ lam < 1 ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.stable.toDistribution x →
        ‖mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v‖ ≤
          C * lam ^ n * ‖v‖) ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.unstable.toDistribution x →
        ‖mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n]) x v‖ ≤
          C * lam ^ n * ‖v‖) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro hs hu hrf hri
  obtain ⟨theta, R, ht0, ht1, hR, hsb, hub, hfb, hib⟩ :=
    original_uniform_bounds_of_local_bounds f a hs hu hrf hri
  have hk : 0 < a.k := lt_of_lt_of_le Nat.zero_lt_one a.one_le_k
  obtain ⟨Cs, ls, hCs, hls, hls1, hstable⟩ :=
    HolomorphicAnosov.UniformIterateBounds.all_iterate_bound_of_uniform_block f.toReal
      a.splitting.stable.toDistribution a.splitting.stable_map a.k hk
      theta R ht0 ht1 hR
      (fun x v hv ↦
        (HolomorphicAnosov.UniformIterateBounds.restricted_iterate_norm_le f.toReal
          a.splitting.stable.toDistribution a.splitting.stable_map a.k x v hv).trans
          (mul_le_mul_of_nonneg_right (hsb x) (norm_nonneg v)))
      (fun r hr x v _ ↦
        ((mfderiv (realModel d) (realModel d) ((f : M → M)^[r]) x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hfb ⟨r, hr⟩ x) (norm_nonneg v)))
  obtain ⟨Cu, lu, hCu, hlu, hlu1, hunstable⟩ :=
    HolomorphicAnosov.UniformIterateBounds.all_iterate_bound_of_uniform_block f.toReal.symm
      a.splitting.unstable.toDistribution
      (FixedBlockEstimates.Inverse.inverse_distribution_invariant f.toReal
        a.splitting.unstable.toDistribution a.splitting.unstable_map) a.k hk
      theta R ht0 ht1 hR
      (fun x v hv ↦ FixedBlockEstimates.Inverse.inverse_iterate_bound_of_operator_bound f.toReal
        a.splitting.unstable.toDistribution a.splitting.unstable_map a.k theta hub x v hv)
      (fun r hr x v _ ↦
        ((mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[r]) x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hib ⟨r, hr⟩ x) (norm_nonneg v)))
  obtain ⟨C, lam, hC, hlam, hlam1, hsn, hun⟩ :=
    HolomorphicAnosov.common_exponential_constants Cs Cu ls lu
      hCs hCu hls hlu hls1 hlu1
  refine ⟨C, lam, hC, hlam, hlam1, fun n x v hv ↦ ?_, fun n x v hv ↦ ?_⟩
  · exact (hstable n x v hv).trans
      (mul_le_mul_of_nonneg_right (hsn n) (norm_nonneg v))
  · exact (hunstable n x v hv).trans
      (mul_le_mul_of_nonneg_right (hun n) (norm_nonneg v))

/-- The original Anosov datum itself supplies uniform all-forward and all-backward estimates. -/
private theorem original_anosov_all_iterates {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M) (a : AnosovDatum f) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ lam < 1 ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.stable.toDistribution x →
        ‖mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v‖ ≤
          C * lam ^ n * ‖v‖) ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.unstable.toDistribution x →
        ‖mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n]) x v‖ ≤
          C * lam ^ n * ‖v‖) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  apply original_all_iterates_of_local_bounds f a
  · intro x
    obtain ⟨q, _, hq1, hlocal⟩ := FixedBlockEstimates.Native.original_stable_local_bounds f a x
    exact ⟨q, hq1, hlocal⟩
  · intro x
    obtain ⟨q, _, hq1, hlocal⟩ := FixedBlockEstimates.Native.original_unstable_local_bounds f a x
    exact ⟨q, hq1, hlocal⟩
  · exact FixedBlockEstimates.Native.original_forward_residue_local_bounds f a
  · exact FixedBlockEstimates.Native.original_backward_residue_local_bounds f a

end OriginalDatum
end HolomorphicAnosov.FixedBlockEstimates.Compact

namespace HolomorphicAnosov
section
attribute [local instance] complex_isManifold_real
open scoped Bundle ContDiff

/-- Uniform original-metric estimates for every iterate of a holomorphic Anosov map. -/
theorem fixed_block_uniform_anosov_estimates {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold (complexModel d) ∞ M] (f : Biholomorph d d M M) (a : AnosovDatum f) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ lam < 1 ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.stable.toDistribution x →
        ‖mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v‖ ≤
          C * lam ^ n * ‖v‖) ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.unstable.toDistribution x →
        ‖mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n]) x v‖ ≤
          C * lam ^ n * ‖v‖) := by
  exact FixedBlockEstimates.Compact.original_anosov_all_iterates f a

end
end HolomorphicAnosov
