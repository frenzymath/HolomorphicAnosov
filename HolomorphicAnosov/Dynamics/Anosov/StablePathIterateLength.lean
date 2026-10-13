import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Dynamics.Anosov.NativePlaqueUniformLength
import HolomorphicAnosov.Topology.ExistsFullLengthMetric
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import Mathlib.Topology.UniformSpace.Compact

/-!
# Original Anosov contraction of stable path lengths

DAG node: `dynamics.anosov_stable_path_iterate_length_g17`.
Zhang's Anosov definition and the fixed-block all-iterate estimate give
contraction of actual stable C1 connectors in the stored Riemannian metric.
The endpoint estimate is extended-metric valued, so disconnected ambient
manifolds cause no exception. The finite compatible metric, uniform native
plaque shrinking, and stable-class membership consequences use the same
original map, tensor, and intrinsic presentation.
-/

noncomputable section
open Set Filter MeasureTheory Manifold
open scoped ContDiff Manifold Bundle ENNReal _root_.Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- The original all-iterate Anosov bound contracts the length of every C1
stable connector in the original stored Riemannian metric. Its endpoints are
therefore at most the same bound apart in the Riemannian extended distance.

Use the proved fixed-block-to-all-iterate estimates, retaining their original
map and metric. The manifold chain rule identifies the velocity of f^n ∘ γ
with Df^n applied to the original within velocity. That velocity is stable by
hypothesis, so its norm contracts by C λ^n. Monotonicity of the nonnegative
speed integral and extraction of the finite constant give the length bound;
the defining path-infimum distance is no larger than this actual path length.
The proof does not assume the ambient manifold connected.

Source: Zhang's Anosov definition p.1, the original all-iterate estimate,
and Lee (2003) §11 pp.275–279, length as the speed integral. -/
theorem anosov_stable_path_iterate_length
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (γ : ℝ → M), ContMDiffOn 𝓘(ℝ) (realModel d) 1 γ (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        mfderivWithin 𝓘(ℝ) (realModel d) γ (Icc 0 1) t 1 ∈
          a.splitting.stable.toDistribution (γ t)) →
      ∀ n : ℕ,
        pathELength (realModel d) (((f : M → M)^[n]) ∘ γ) 0 1 ≤
          ENNReal.ofReal (C * ρ ^ n) * pathELength (realModel d) γ 0 1 ∧
        riemannianEDist (realModel d) (((f : M → M)^[n]) (γ 0))
            (((f : M → M)^[n]) (γ 1)) ≤
          ENNReal.ofReal (C * ρ ^ n) * pathELength (realModel d) γ 0 1 := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C,ρ,hC,hρ,hρ1,hs,_⟩ := fixed_block_uniform_anosov_estimates f a
  refine ⟨C,ρ,hC,hρ,hρ1,?_⟩
  intro γ hγ hstable n
  have hf : ContMDiff (realModel d) (realModel d) ∞ ((f : M → M)^[n]) :=
    f.toReal.contMDiff.iterate n
  have hlength : pathELength (realModel d) (((f : M → M)^[n]) ∘ γ) 0 1 ≤
      ENNReal.ofReal (C * ρ ^ n) * pathELength (realModel d) γ 0 1 := by
    rw [pathELength_eq_lintegral_mfderivWithin_Icc,
      pathELength_eq_lintegral_mfderivWithin_Icc,
      ← lintegral_const_mul' _ _ (by simp)]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have hd := mfderiv_comp_mfderivWithin t
      ((hf (γ t)).mdifferentiableAt (by simp))
      ((hγ t ht).mdifferentiableWithinAt one_ne_zero)
      ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
    rw [hd]
    change ‖mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) (γ t)
      (mfderivWithin 𝓘(ℝ) (realModel d) γ (Icc 0 1) t 1)‖ₑ ≤ _
    simpa only [← ofReal_norm, ENNReal.ofReal_mul (mul_nonneg hC.le (pow_nonneg hρ.le n))] using
      ENNReal.ofReal_le_ofReal (hs n (γ t) _ (hstable t ht))
  refine ⟨hlength, ?_⟩
  exact (riemannianEDist_le_pathELength
    ((hf.of_le (by simp)).comp_contMDiffOn hγ) rfl rfl zero_le_one).trans hlength


/-- A compatible finite metric preserves every finite distance of the original
Riemannian metric, without an ambient connectedness assumption. This is the
finite-distance-class metric construction applied to the original tensor. -/
theorem anosov_exists_full_length_metric
    {d : ℕ} {M : Type*} [tM : TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∃ m : MetricSpace M, m.toUniformSpace.toTopologicalSpace = tM ∧
      ∀ x y : M, riemannianEDist (realModel d) x y < ⊤ →
        ENNReal.ofReal (m.dist x y) = riemannianEDist (realModel d) x y := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.inner, a.metric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (realModel d) M
  exact exists_full_length_metric M

/-- Every compact inner family of actual stable plaques shrinks uniformly
under the original iterates. Use the uniformly bounded actual radial paths,
contract their lengths, and identify their finite endpoint distances with the
chosen compatible metric. The bound C ρ^n B tends to zero. -/
theorem anosov_native_stable_plaque_uniform_shrinking
    {d : ℕ} {M V : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (m : MetricSpace M) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    (∀ x y : M, riemannianEDist (realModel d) x y < ⊤ →
      ENNReal.ofReal (m.dist x y) = riemannianEDist (realModel d) x y) →
    ∀ {center : M}
      (P : NativePlaqueFamily (realModel d) (V := V)
        a.splitting.stable.toDistribution center)
      (K : Set P.centerDomain), IsCompact K →
      ∀ {r : ℝ}, 0 < r → r < P.radius →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ p ∈ K, ∀ v ∈ Metric.closedBall (0 : V) r,
          m.dist (((f : M → M)^[n]) ((P.plaque p).param v))
            (((f : M → M)^[n]) p.val) < ε := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro hm center P K hK r hr0 hr ε hε
  obtain ⟨C,ρ,hC,hρ,hρ1,hcontr⟩ := anosov_stable_path_iterate_length f a
  obtain ⟨B,hB0,hB⟩ := P.uniform_radial_length a.metric K hK hr0 hr
  have ht : Tendsto (fun n : ℕ ↦ C * ρ^n * B) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul C).mul_const B
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn p hp v hv
  obtain ⟨hγ,hstable,hlen⟩ := hB p hp v hv
  have hed := (hcontr _ hγ hstable n).2
  have hbound : riemannianEDist (realModel d) (((f : M → M)^[n]) p.val)
      (((f : M → M)^[n]) ((P.plaque p).param v)) ≤
      ENNReal.ofReal (C * ρ^n * B) := by
    have h := hed.trans (mul_le_mul_right hlen (ENNReal.ofReal (C * ρ^n)))
    simpa only [Function.comp_apply, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, (P.plaque p).centered,
      ENNReal.ofReal_mul (mul_nonneg hC.le (pow_nonneg hρ.le n))] using h
  have hfinite := lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hdist : m.dist (((f : M → M)^[n]) p.val)
      (((f : M → M)^[n]) ((P.plaque p).param v)) ≤ C * ρ^n * B := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
      (mul_nonneg hC.le (pow_nonneg hρ.le n)) hB0)).mp
    rw [hm _ _ hfinite]
    exact hbound
  have hcomm := @dist_comm M m.toPseudoMetricSpace
    (((f : M → M)^[n]) ((P.plaque p).param v)) (((f : M → M)^[n]) p.val)
  exact hcomm.trans_le hdist |>.trans_lt hn


/-- The actual native stable plaques belong to the stable classes of ANY
supplied intrinsic presentation. Shrinking proves forward asymptoticity in the
original length metric; uniqueness of compact uniformity transports this to
the presentation metric. Thus no equality of native choices is assumed. -/
theorem anosov_native_plaque_in_presentation_stable_class
    {d : ℕ} {M V : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : Ghys.AnosovIntrinsicFoliationPresentation f a) {center : M}
    (F : NativePlaqueFamily (realModel d) (V := V)
      a.splitting.stable.toDistribution center)
    (p : F.centerDomain) (v : V) (hv : v ∈ Metric.ball (0 : V) F.radius) :
    letI := P.realCharts
    P.foliations.stablePartition p.val ((F.plaque p).param v) := by
  let := P.realCharts
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨m,hmTop,hm⟩ := anosov_exists_full_length_metric f a
  let : MetricSpace M := m.replaceTopology hmTop.symm
  obtain ⟨r,hvr,hr⟩ := exists_between (show ‖v‖ < F.radius by simpa using hv)
  have hr0 : 0 < r := (norm_nonneg v).trans_lt hvr
  have hdist : @ForwardAsymptotic M m f p.val ((F.plaque p).param v) := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      exact Filter.Eventually.of_forall (fun n ↦ hb.trans_le
        (@dist_nonneg M m.toPseudoMetricSpace _ _))
    · intro ε hε
      filter_upwards [anosov_native_stable_plaque_uniform_shrinking f a m hm F
        {p} isCompact_singleton hr0 hr ε hε] with n hn
      exact hn p (Set.mem_singleton p) v (by simpa using hvr.le)
  have hu : P.metric.toUniformSpace = m.toUniformSpace :=
    unique_uniformity_of_compact P.metric_topology hmTop
  apply (P.stable_asymptotic _ _).mpr
  have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ P.metric.toPseudoMetricSpace
    (fun n ↦ (((f : M → M)^[n]) ((F.plaque p).param v), ((f : M → M)^[n]) p.val)) atTop
  have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m.toPseudoMetricSpace
    (fun n ↦ (((f : M → M)^[n]) ((F.plaque p).param v), ((f : M → M)^[n]) p.val)) atTop
  unfold ForwardAsymptotic at hdist ⊢
  rw [← h₁]
  rw [← h₂] at hdist
  change Tendsto _ _ P.metric.toUniformSpace.uniformity
  rw [hu]
  exact hdist

end HolomorphicAnosov
