import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.CauchyIntegral

/-! This file proves analyticity and nonvanishing of the derivative for a local holomorphic curve
parametrization in compatible scalar coordinates. (Ghys, §3, p.591; Rudin, Thm 10.16,
pp.207–208) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u

/-- A local holomorphic parametrization expressed in a compatible curve chart is analytic with
nonzero derivative at zero. (Ghys, §3, p.591; Rudin, Thm 10.16, pp.207–208; Thm 10.30; Thm
10.33, p.217) -/
theorem curve_chart_parametrization_regular
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    (c : OpenPartialHomeomorph L ℂ)
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L)
    (e : OpenPartialHomeomorph ℂ L) (h0 : 0 ∈ e.source)
    (he : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ e e.source)
    (hes : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ∞ e.symm e.target)
    (hc0 : e 0 ∈ c.source) :
    AnalyticAt ℂ (c ∘ e) 0 ∧ deriv (c ∘ e) 0 ≠ 0 := by
  have hset : e.source ∩ (e : ℂ → L) ⁻¹' c.source ∈ 𝓝 (0 : ℂ) :=
    inter_mem (e.open_source.mem_nhds h0)
      ((he.continuousOn.continuousAt (e.open_source.mem_nhds h0)).preimage_mem_nhds
        (c.open_source.mem_nhds hc0))
  have hφ : ContDiffOn ℂ ∞ (c ∘ e) (e.source ∩ (e : ℂ → L) ⁻¹' c.source) :=
    ((contMDiffOn_of_mem_maximalAtlas hc).comp' he).contDiffOn
  refine ⟨(hφ.differentiableOn (by simp)).analyticAt hset, ?_⟩
  have hφd := (hφ.contDiffAt hset).differentiableAt (by simp)
  have hi := hes.contMDiffAt (e.open_target.mem_nhds (e.map_source h0))
  have hi' : ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ∞ e.symm (c.symm (c (e 0))) := by
    simpa only [c.left_inv hc0] using hi
  have hψd := ((hi'.comp _ (contMDiffAt_symm_of_mem_maximalAtlas hc
    (c.map_source hc0))).contDiffAt).differentiableAt (by simp)
  have heq : ((e.symm ∘ c.symm) ∘ (c ∘ e)) =ᶠ[𝓝 (0 : ℂ)] id := by
    filter_upwards [hset] with t ht
    simp only [Function.comp_apply, c.left_inv ht.2, e.left_inv ht.1, id_eq]
  have hprod := ((hψd.hasDerivAt.comp 0 hφd.hasDerivAt).congr_of_eventuallyEq
    heq.symm).unique (hasDerivAt_id (0 : ℂ))
  intro hz
  rw [hz, mul_zero] at hprod
  exact zero_ne_one hprod

end HolomorphicAnosov.Ghys
