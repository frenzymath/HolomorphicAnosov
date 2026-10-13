import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! This file gives the transformation laws for the first and normalized second Taylor coefficients
under a complex curve chart change. (Michor, §§1.3–1.6, pp.2–3; Ghys, §3, p.591) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff

namespace HolomorphicAnosov.Ghys
universe u

/-- First and normalized second derivatives transform under a complex curve chart change by the
first and second chain rules on the common chart domain. (Michor, §§1.3–1.6, pp.2–3; Ghys, §3,
p.591) -/
theorem curve_chart_two_jet_transport
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]
    (c d : OpenPartialHomeomorph L ℂ)
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L)
    (hd : d ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L)
    (f : ℂ → L) (hf : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ f 0)
    (hc0 : f 0 ∈ c.source) (hd0 : f 0 ∈ d.source) :
    deriv (d ∘ f) 0 = deriv (d ∘ c.symm) (c (f 0)) * deriv (c ∘ f) 0 ∧
    iteratedDeriv 2 (d ∘ f) 0 / 2 =
      deriv (d ∘ c.symm) (c (f 0)) * (iteratedDeriv 2 (c ∘ f) 0 / 2) +
      (iteratedDeriv 2 (d ∘ c.symm) (c (f 0)) / 2) * deriv (c ∘ f) 0 ^ 2 := by
  have hφ : ContDiffAt ℂ 2 (c ∘ f) 0 :=
    ((contMDiffAt_of_mem_maximalAtlas hc hc0).comp 0 hf).contDiffAt.of_le (by simp)
  have hd' := contMDiffAt_of_mem_maximalAtlas hd hd0
  have hc' := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hc0)
  have hh : ContDiffAt ℂ 2 (d ∘ c.symm) (c (f 0)) := by
    have hd'' : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) ∞ d (c.symm (c (f 0))) := by
      simpa only [c.left_inv hc0] using hd'
    exact (hd''.comp _ hc').contDiffAt.of_le (by simp)
  have heq : (d ∘ f) =ᶠ[𝓝 (0 : ℂ)] (d ∘ c.symm) ∘ (c ∘ f) := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hc0)] with t ht
    simp only [Function.comp_apply, c.left_inv ht]
  constructor
  · rw [heq.deriv_eq, deriv_comp 0 (hh.differentiableAt (by norm_num))
      (hφ.differentiableAt (by norm_num))]
    rfl
  · rw [heq.iteratedDeriv_eq 2, iteratedDeriv_comp_two hh hφ]
    dsimp only [Function.comp_apply]
    ring

end HolomorphicAnosov.Ghys
