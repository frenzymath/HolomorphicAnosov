import HolomorphicAnosov.Ghys.UniformIntrinsicNeighborhoods
import HolomorphicAnosov.Paper.Zhang.CompleteStableCoordinates

/-! Contraction estimates for intrinsic real length distances. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold ENNReal
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {L K M : Type*}
  [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
  [TopologicalSpace K] [ChartedSpace (Fin 2 → ℝ) K]
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]

/-- A bound on the actual pullback speed bounds the intrinsic extended distance. -/
theorem intrinsicRealMetricLeafEDist_map_le
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (a : L → K) (ha : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) 1 a)
    (j : L → M) (k : K → M) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ z (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z),
      realMetricLeafSpeed g k (a z)
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) a z v) ≤
        c * realMetricLeafSpeed g j z v) (x y : L) :
    intrinsicRealMetricLeafEDist g k (a x) (a y) ≤
      ENNReal.ofReal c * intrinsicRealMetricLeafEDist g j x y := by
  unfold intrinsicRealMetricLeafEDist
  rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hc))
    ENNReal.ofReal_ne_top]
  apply le_iInf
  intro p
  apply (iInf_le _ (p.map a ha)).trans
  unfold realMetricLeafPiecewiseLength
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change (∫⁻ t in p.pieceInterval i,
    ENNReal.ofReal (realMetricLeafSpeed g k (a (p.piece i t))
      ((p.map a ha).velocity i t))) ≤ _
  calc
    _ ≤ ∫⁻ t in p.pieceInterval i, ENNReal.ofReal c *
        ENNReal.ofReal (realMetricLeafSpeed g j (p.piece i t) (p.velocity i t)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [← ENNReal.ofReal_mul hc.le, p.map_velocity a ha i t ht]
      exact ENNReal.ofReal_le_ofReal (hbound _ _)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end HolomorphicAnosov.Ghys
