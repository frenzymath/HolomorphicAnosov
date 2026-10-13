import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Bundle _root_.Topology

namespace HolomorphicAnosov

/-- A differential bound by `C` on a Riemannian ball bounds the distance between the images of its
center and any point in the ball by `C` times their distance. (Lee, Prop. 11.20, pp.278–279) -/
theorem riemannianEDist_map_le_of_local_derivative_bound
    {E M E' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace N] [ChartedSpace E' N] [IsManifold 𝓘(ℝ, E') ∞ N]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E') : N → Type _)]
    {F : M → N} {U : Set M} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') 1 F U)
    (C : ℝ≥0)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) z,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') F z v‖ₑ ≤ C * ‖v‖ₑ)
    {x y : M} {R : ℝ≥0∞}
    (hball : ∀ z, riemannianEDist 𝓘(ℝ, E) x z < R → z ∈ U)
    (hxy : riemannianEDist 𝓘(ℝ, E) x y < R) :
    riemannianEDist 𝓘(ℝ, E') (F x) (F y) ≤ C * riemannianEDist 𝓘(ℝ, E) x y := by
  let D := riemannianEDist 𝓘(ℝ, E) x y
  have hq (q : Ioo D R) : riemannianEDist 𝓘(ℝ, E') (F x) (F y) ≤ C * q.val := by
    obtain ⟨γ, hγ0, hγ1, hγ, hlen, _, _⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt q.property.1 zero_lt_one
    have hstay : MapsTo γ (Icc (0 : ℝ) 1) U := by
      intro t ht
      apply hball
      have hp : riemannianEDist 𝓘(ℝ, E) x (γ t) ≤ pathELength 𝓘(ℝ, E) γ 0 t :=
        riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 rfl ht.1
      exact (hp.trans (pathELength_mono le_rfl ht.2)).trans_lt (hlen.trans q.property.2)
    have himage : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E') 1 (F ∘ γ) (Icc 0 1) :=
      hF.comp hγ.contMDiffOn hstay
    have hlenmap : pathELength 𝓘(ℝ, E') (F ∘ γ) 0 1 ≤ C * pathELength 𝓘(ℝ, E) γ 0 1 := by
      simp only [pathELength]
      rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hd := mfderiv_comp t
        ((hF (γ t) (hstay ht)).contMDiffAt (hU.mem_nhds (hstay ht)) |>.mdifferentiableAt one_ne_zero)
        (hγ.mdifferentiable one_ne_zero t)
      rw [hd, ContinuousLinearMap.comp_apply]
      exact hbound (γ t) (hstay ht) _
    exact (riemannianEDist_le_pathELength himage (congrArg F hγ0) (congrArg F hγ1) zero_le_one).trans
      (hlenmap.trans (mul_le_mul le_rfl hlen.le zero_le zero_le))
  have hne : Nonempty (Ioo D R) := nonempty_subtype.mpr (nonempty_Ioo.mpr hxy)
  have hi : (⨅ q : Ioo D R, (q : ℝ≥0∞)) = D := by
    rw [iInf_subtype, ← sInf_eq_iInf]
    exact csInf_Ioo hxy
  change riemannianEDist 𝓘(ℝ, E') (F x) (F y) ≤ C * D
  rw [← hi, ENNReal.mul_iInf (by simp)]
  exact le_iInf hq

/-- A differential bound by `C` on an open set gives a neighborhood of each point on which all image
distances are at most `C` times the original Riemannian distances. -/
theorem locally_riemannianEDist_map_le_of_derivative_bound
    {E M E' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RegularSpace M]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace N] [ChartedSpace E' N] [IsManifold 𝓘(ℝ, E') ∞ N]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E') : N → Type _)]
    {F : M → N} {U : Set M} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E') 1 F U)
    (C : ℝ≥0)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) z,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') F z v‖ₑ ≤ C * ‖v‖ₑ)
    {x : M} (hx : x ∈ U) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, ∀ z ∈ W,
        riemannianEDist 𝓘(ℝ, E') (F y) (F z) ≤ C * riemannianEDist 𝓘(ℝ, E) y z := by
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds 𝓘(ℝ, E) (hU.mem_nhds hx)
  let a : ℝ≥0 := c / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have hac : (a : ℝ≥0∞) < c := by
    exact_mod_cast (show a < c by dsimp [a]; exact div_lt_self hc (by norm_num))
  have hthree : (a : ℝ≥0∞) + (2 * a : ℝ≥0) < c := by
    rw [← ENNReal.coe_add, ENNReal.coe_lt_coe]
    dsimp [a]
    exact_mod_cast (show (c : ℝ) / 4 + 2 * ((c : ℝ) / 4) < c by exact (by positivity : (0 : ℝ) < c) |> fun h ↦ by linarith)
  let W := Metric.eball x (a : ℝ≥0∞)
  refine ⟨W, Metric.isOpen_eball, Metric.mem_eball_self (by exact_mod_cast ha), ?_, ?_⟩
  · intro y hy
    change edist y x < (a : ℝ≥0∞) at hy
    apply hball
    exact (edist_comm y x ▸ hy).trans hac
  · intro y hy z hz
    change edist y x < (a : ℝ≥0∞) at hy
    change edist z x < (a : ℝ≥0∞) at hz
    apply riemannianEDist_map_le_of_local_derivative_bound hU hF C hbound
      (R := ((2 * a : ℝ≥0) : ℝ≥0∞))
    · intro t ht
      apply hball
      change edist x t < c
      have hy' : edist x y < (a : ℝ≥0∞) := by simpa only [edist_comm] using hy
      exact (edist_triangle x y t).trans_lt ((ENNReal.add_lt_add hy' ht).trans hthree)
    · change edist y z < ((2 * a : ℝ≥0) : ℝ≥0∞)
      have hz' : edist x z < (a : ℝ≥0∞) := by simpa only [edist_comm] using hz
      have ht := (edist_triangle y x z).trans_lt (ENNReal.add_lt_add hy hz')
      simpa only [← ENNReal.coe_add, two_mul] using ht

/-- Coordinate chords, measured in the metric norm at the chart center, are locally bounded by any
factor greater than one times the Riemannian distance. (Petersen, pp.149–150) -/
theorem frozen_chart_chord_le_local_riemannianEDist
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [RegularSpace M]
    [Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
    (x : M) {r : ℝ} (hr : 1 < r) :
    let A := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ x
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ (extChartAt 𝓘(ℝ, E) x).source ∧
      ∀ y ∈ W, ∀ z ∈ W,
        ‖A (extChartAt 𝓘(ℝ, E) x y - extChartAt 𝓘(ℝ, E) x z)‖ₑ ≤
          ENNReal.ofReal r * riemannianEDist 𝓘(ℝ, E) y z := by
  let A := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ x
  let G : M → TangentSpace 𝓘(ℝ, E) x := A ∘ extChartAt 𝓘(ℝ, E) x
  have hnear := eventually_norm_symmL_trivializationAt_self_comp_lt
    E (TangentSpace 𝓘(ℝ, E)) x hr
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hnear (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) x))
  have hUsrc : U ⊆ (extChartAt 𝓘(ℝ, E) x).source := fun z hz ↦ (hUsub hz).2
  have hG : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 1 G U :=
    A.contMDiff.comp_contMDiffOn ((contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := x)).mono (by simpa only [extChartAt_source] using hUsrc))
  let C : ℝ≥0 := ⟨r, by linarith⟩
  have hbound (z : M) (hz : z ∈ U) (v : TangentSpace 𝓘(ℝ, E) z) :
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) G z v‖ₑ ≤ C * ‖v‖ₑ := by
    have hchart : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) z :=
      mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hUsrc hz)
    have hder := mfderiv_comp z (A.contMDiff.mdifferentiableAt one_ne_zero) hchart
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) G z = _ at hder
    rw [hder, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, A.fderiv,
      enorm_tangentSpace_vectorSpace]
    change ‖(A (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) z v) : TangentSpace 𝓘(ℝ, E) x)‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ
    have hn := (hUsub hz).1
    change ‖A.comp ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearMapAt ℝ z)‖ < r at hn
    rw [TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hUsrc hz)] at hn
    have hv := ((A.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) z)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hn.le (norm_nonneg v))
    change ‖A (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) z v)‖ ≤ r * ‖v‖ at hv
    have hCr : (C : ℝ) = r := rfl
    rw [← ofReal_norm, ← ofReal_norm, ENNReal.coe_nnreal_eq, hCr]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal r * ENNReal.ofReal ‖v‖
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ r)]
    exact ENNReal.ofReal_le_ofReal hv
  obtain ⟨W, hW, hxW, hWU, hdist⟩ :=
    locally_riemannianEDist_map_le_of_derivative_bound hU hG C hbound hxU
  refine ⟨W, hW, hxW, hWU.trans hUsrc, ?_⟩
  intro y hy z hz
  have hh := hdist y hy z hz
  have hCr : (C : ℝ) = r := rfl
  rw [← IsRiemannianManifold.out, ENNReal.coe_nnreal_eq, hCr] at hh
  simpa only [G, Function.comp_apply, edist_eq_enorm_sub, ← map_sub, A] using hh

end HolomorphicAnosov

