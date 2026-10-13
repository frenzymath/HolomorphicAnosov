import HolomorphicAnosov.Dynamics.NativeLeafPathEDistFinite
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathSpeedIntegrable
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathMap
import Mathlib.Topology.Compactness.Compact

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped ContDiff Manifold Topology ENNReal Bundle
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Coordinate segments, smoothly reparametrized, have arbitrarily small
pullback length as their endpoint approaches their starting point. The joint
velocity is continuous and vanishes on the constant central path; compactness
of the parameter interval gives a uniform speed bound. Source: Lee (2003),
Lemma 11.19, the upper local length estimate in intrinsic coordinates. -/
theorem nativeLeafPathEDist_small
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {x : M} (L : NativeSmoothLeaf 𝓘(ℝ, E) D x)
    (z : L.Carrier) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 z, nativeLeafPathEDist 𝓘(ℝ, E) h L z y < ENNReal.ofReal ε := by
  classical
  let V := Fin L.rank → ℝ
  let c := chartAt V z
  let a := c z
  have hz : z ∈ c.source := mem_chart_source _ _
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target a (c.map_source hz)
  let W : Set (V × ℝ) := Metric.ball a r ×ˢ univ
  have hW : IsOpen W := Metric.isOpen_ball.prod isOpen_univ
  let coord : V × ℝ → V := fun p ↦ AffineMap.lineMap a p.1 (Real.smoothTransition p.2)
  have hcoord : ContDiff ℝ ∞ coord := by
    dsimp [coord, AffineMap.lineMap_apply]
    fun_prop
  have hcoordmem : MapsTo coord W c.target := by
    intro p hp
    exact hball ((convex_ball a r).mapsTo_lineMap (Metric.mem_ball_self hr) hp.1
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
  let q : V × ℝ → M := fun p ↦ L.inclusion (c.symm (coord p))
  have hleaf : ContMDiffOn 𝓘(ℝ, V × ℝ) 𝓘(ℝ, V) ∞
      (fun p ↦ c.symm (coord p)) W := contMDiffOn_chart_symm.comp
        (contMDiff_iff_contDiff.mpr hcoord).contMDiffOn hcoordmem
  have hq : ContMDiffOn 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) ∞ q W :=
    L.inclusion_smooth.comp_contMDiffOn hleaf
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let velocity (p : V × ℝ) := mfderivWithin 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) q W p (0, 1)
  let speed (p : V × ℝ) := Real.sqrt (h.inner (q p) (velocity p) (velocity p))
  have ht := hq.continuousOn_tangentMapWithin (by simp) hW.uniqueMDiffOn
  have hsection : Continuous (fun p : V × ℝ ↦
      (⟨p, (0, 1)⟩ : TangentBundle 𝓘(ℝ, V × ℝ) (V × ℝ))) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, V × ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvel := ht.comp hsection.continuousOn (fun p (hp : p ∈ W) ↦ hp)
  have hspeed : ContinuousOn speed W := (hvel.inner_bundle hvel).sqrt
  have hzero (t : ℝ) : speed (a, t) = 0 := by
    have hat : (a, t) ∈ W := ⟨Metric.mem_ball_self hr, mem_univ _⟩
    have hdq : MDifferentiableAt 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) q (a, t) := (hq.mdifferentiableOn (by simp) _ hat).mdifferentiableAt (hW.mem_nhds hat)
    have hk : ContMDiff 𝓘(ℝ) 𝓘(ℝ, V × ℝ) ∞ (fun s : ℝ ↦ (a, s)) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    have heq : (q ∘ (fun s : ℝ ↦ (a, s))) = fun _ ↦ L.inclusion z := by
      ext s
      simp [q, coord, AffineMap.lineMap_apply, a, c.left_inv hz]
    have hder := congrArg (fun T ↦ T (1 : ℝ))
      (mfderiv_comp t hdq (hk.mdifferentiableAt (by simp)))
    rw [heq, mfderiv_const] at hder
    have hkder : mfderiv 𝓘(ℝ) 𝓘(ℝ, V × ℝ) (fun s : ℝ ↦ (a, s)) t 1 = (0, 1) := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun s : ℝ ↦ (a, s)) t 1 = (0, 1)
      rw [(hasFDerivAt_prodMk_right a t).fderiv]
      rfl
    have hv : velocity (a, t) = 0 := by
      dsimp [velocity]
      rw [mfderivWithin_of_mem_nhds (hW.mem_nhds hat)]
      change 0 = mfderiv 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) q (a, t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, V × ℝ) (fun s : ℝ ↦ (a, s)) t 1) at hder
      rw [hkder] at hder
      exact hder.symm
    simp [speed, hv]
  have hsmall : ∀ᶠ v in 𝓝 a, ∀ t ∈ Icc (0 : ℝ) 1, speed (v, t) < ε / 2 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hat : (a, t) ∈ W := ⟨Metric.mem_ball_self hr, mem_univ _⟩
    have hc := (hspeed _ hat).continuousAt (hW.mem_nhds hat)
    apply hc.eventually (gt_mem_nhds ?_)
    rw [hzero]
    exact half_pos hε
  have hevent : ∀ᶠ y in 𝓝 z, c y ∈ Metric.ball a r ∧
      (∀ t ∈ Icc (0 : ℝ) 1, speed (c y, t) < ε / 2) ∧ y ∈ c.source := by
    have hballEv : ∀ᶠ v in 𝓝 a, v ∈ Metric.ball a r := Metric.ball_mem_nhds _ hr
    exact ((c.continuousAt hz).eventually (hballEv.and hsmall)).and
      (c.open_source.mem_nhds hz) |>.mono fun y hy ↦ ⟨hy.1.1, hy.1.2, hy.2⟩
  filter_upwards [hevent] with y hy
  let curve : ℝ → L.Carrier := fun t ↦ c.symm (coord (c y, t))
  have hk : ContMDiff 𝓘(ℝ) 𝓘(ℝ, V × ℝ) ∞ (fun t : ℝ ↦ (c y, t)) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hcurve : ContMDiff 𝓘(ℝ) 𝓘(ℝ, V) ∞ curve := by
    rw [← contMDiffOn_univ]
    exact hleaf.comp hk.contMDiffOn (fun t ht ↦ ⟨hy.1, mem_univ _⟩)
  have hc0 : curve 0 = z := by simp [curve, coord, a, c.left_inv hz]
  have hc1 : curve 1 = y := by simp [curve, coord, c.left_inv hy.2.2]
  let times : Fin 2 → ℝ := fun i ↦ (i : ℝ)
  let p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, V) z y :=
    { n := 0
      time := times
      time_strictMono := by
        intro i j hij
        simpa [times] using (show (i : ℝ) < (j : ℝ) by exact_mod_cast hij)
      time_zero := by simp [times]
      time_one := by simp [times]
      piece := fun _ ↦ curve
      piece_smooth := fun i ↦ by simpa [times] using hcurve.contMDiffOn
      source := hc0
      target := hc1
      junction := fun i ↦ Fin.elim0 i }
  let ambient := p.map L.inclusion L.inclusion_smooth
  have htime0 : ambient.time (Fin.castSucc 0) = 0 := ambient.time_zero
  have htime1 : ambient.time (Fin.succ 0) = 1 := ambient.time_one
  have hinter : ambient.pieceInterval 0 = Icc (0 : ℝ) 1 := by
    rw [RiemannianPiecewiseSmoothPath.pieceInterval, htime0, htime1]
  have hspeed_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ambient.speed h 0 t = speed (c y, t) := by
    have hyt : (c y, t) ∈ W := ⟨hy.1, mem_univ _⟩
    have hdq := (hq.mdifferentiableOn (by simp) _ hyt).mdifferentiableAt (hW.mem_nhds hyt)
    have hkder : mfderiv 𝓘(ℝ) 𝓘(ℝ, V × ℝ) (fun s : ℝ ↦ (c y, s)) t 1 = (0, 1) := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun s : ℝ ↦ (c y, s)) t 1 = (0, 1)
      rw [(hasFDerivAt_prodMk_right (c y) t).fderiv]
      rfl
    have hv : ambient.velocity 0 t = velocity (c y, t) := by
      unfold RiemannianPiecewiseSmoothPath.velocity
      rw [hinter]
      change mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) (q ∘ (fun s ↦ (c y, s)))
        (Icc 0 1) t 1 = mfderivWithin 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) q W (c y, t) (0, 1)
      rw [mfderivWithin_eq_mfderiv ((uniqueDiffOn_Icc zero_lt_one).uniqueMDiffOn t ht)
        (hdq.comp t (hk.mdifferentiableAt (by simp))),
        mfderivWithin_of_mem_nhds (hW.mem_nhds hyt),
        mfderiv_comp t hdq (hk.mdifferentiableAt (by simp))]
      change mfderiv 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) q (c y, t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, V × ℝ) (fun s : ℝ ↦ (c y, s)) t 1) = _
      rw [hkder]
    change Real.sqrt (h.inner _ (ambient.velocity 0 t) (ambient.velocity 0 t)) = _
    rw [hv]
    rfl
  have hbound : nativeLeafPathLength 𝓘(ℝ, E) h L p ≤ ε / 2 := by
    change ambient.length h ≤ ε / 2
    change (∑ i : Fin 1, ∫ t in ambient.time i.castSucc..ambient.time i.succ,
      ambient.speed h i t) ≤ ε / 2
    rw [Fin.sum_univ_one]
    rw [htime0, htime1]
    have hi : IntervalIntegrable (ambient.speed h 0) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
      simpa only [hinter] using ambient.speed_integrableOn h 0
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, ε / 2 := intervalIntegral.integral_mono_on zero_le_one
        hi intervalIntegrable_const (fun t ht ↦ by rw [hspeed_eq t ht]; exact (hy.2.1 t ht).le)
      _ = ε / 2 := by simp
  exact (iInf_le (fun p ↦ ENNReal.ofReal (nativeLeafPathLength 𝓘(ℝ, E) h L p)) p).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (hbound.trans_lt (half_lt_self hε)))


end HolomorphicAnosov
