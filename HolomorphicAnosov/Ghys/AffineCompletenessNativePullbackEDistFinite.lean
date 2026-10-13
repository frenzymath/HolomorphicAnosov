import HolomorphicAnosov.Ghys.UniformIntrinsicNeighborhoods
import HolomorphicAnosov.Geometry.Riemannian.ConnectedSmoothPathExists
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff

namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))


open MeasureTheory Bundle
open scoped ENNReal Bundle


theorem affine_completeness_native_pullback_edist_lt_top (i : ι) (x y : L i) :
    intrinsicRealMetricLeafEDist a.metric (U.leaf i).inclusion x y < ⊤ := by
  let : ConnectedSpace (L i) := (U.leaf i).connected
  obtain ⟨c, hc, hc0, hc1⟩ :=
    connected_smooth_path_exists (E := Fin 2 → ℝ) x y
  let times : Fin 2 → ℝ := fun k => (k : ℝ)
  let p : IntrinsicPiecewiseC1Path (r := 2) x y := {
    n := 0
    time := times
    time_strictMono := by
      intro k l hkl
      simpa [times] using (show (k : ℝ) < (l : ℝ) by exact_mod_cast hkl)
    time_zero := by simp [times]
    time_one := by simp [times]
    piece := fun _ => c
    piece_c1 := fun _ => hc.contMDiffOn.of_le (by simp)
    source := hc0
    target := hc1
    junction := fun k => Fin.elim0 k }
  rw [intrinsicRealMetricLeafEDist, iInf_lt_iff]
  refine ⟨p, ?_⟩
  let : RiemannianBundle (TangentSpace (realModel d) : M → Type _) :=
    ⟨a.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (ComplexModel d)
      (TangentSpace (realModel d) : M → Type _) :=
    ⟨⟨a.metric.inner, a.metric.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hfinite (k : Fin (p.n + 1)) :
      (∫⁻ t in p.pieceInterval k,
        ENNReal.ofReal (realMetricLeafSpeed a.metric (U.leaf i).inclusion
          (p.piece k t) (p.velocity k t))) < ⊤ := by
    have ht := (p.piece_c1 k).continuousOn_tangentMapWithin (le_refl 1)
      ((uniqueDiffOn_Icc (p.time_strictMono Fin.castSucc_lt_succ)).uniqueMDiffOn)
    have hconst : Continuous (fun t : ℝ =>
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hv : ContinuousOn (fun t =>
        (⟨p.piece k t, p.velocity k t⟩ : TangentBundle 𝓘(ℝ, Fin 2 → ℝ) (L i)))
        (p.pieceInterval k) :=
      ht.comp hconst.continuousOn (fun _ h => h)
    have hj := (U.leaf i).immersion.contMDiff.continuous_tangentMap (by simp)
    have hw := hj.comp_continuousOn hv
    have hs : ContinuousOn (fun t => realMetricLeafSpeed a.metric
        (U.leaf i).inclusion (p.piece k t) (p.velocity k t)) (p.pieceInterval k) :=
      (hw.inner_bundle hw).sqrt
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hs
    calc
      _ ≤ ∫⁻ _t in p.pieceInterval k, ENNReal.ofReal C := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        exact ENNReal.ofReal_le_ofReal (hC ⟨t, ht, rfl⟩)
      _ < ⊤ := by
        simp only [IntrinsicPiecewiseC1Path.pieceInterval, setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  change ∑ k : Fin (p.n + 1), _ < ⊤
  exact ENNReal.sum_lt_top.mpr (fun k _ => hfinite k)

end HolomorphicAnosov.Ghys
