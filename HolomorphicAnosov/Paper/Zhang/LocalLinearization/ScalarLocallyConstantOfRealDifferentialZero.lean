import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.MeanValue

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_scalar_locally_constant_of_real_differential_zero
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (realModel d) ∞ M]
    (V : TopologicalSpace.Opens M) (g : M → ℂ)
    (hg : ContMDiffOn (realModel d) 𝓘(ℝ, ℂ) ∞ g V)
    (hzero : ∀ y ∈ V, QuotientLineConnection.realDifferential (d := d) g y = 0)
    (x : M) (hx : x ∈ V) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ ∀ y ∈ W, g y = g x := by
  let c := chartAt (ComplexModel d) x
  have hc : c ∈ IsManifold.maximalAtlas (realModel d) ∞ M := IsManifold.chart_mem_maximalAtlas x
  let T : Set (ComplexModel d) := c.target ∩ c.symm ⁻¹' (V : Set M)
  have hT : IsOpen T := c.continuousOn_symm.isOpen_inter_preimage c.open_target V.isOpen
  have hcx : c x ∈ T := ⟨c.map_source (mem_chart_source _ x), by
    change c.symm (c x) ∈ V
    rw [c.left_inv (mem_chart_source _ x)]
    exact hx⟩
  have hq : ContMDiffOn (realModel d) 𝓘(ℝ, ℂ) ∞ (g ∘ c.symm) T :=
    hg.comp ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono inter_subset_left)
      (fun y hy ↦ hy.2)
  have hd : ∀ y ∈ T, fderiv ℝ (g ∘ c.symm) y = 0 := by
    intro y hy
    have hgy := (hg (c.symm y) hy.2).contMDiffAt (V.isOpen.mem_nhds hy.2)
    have hcy := contMDiffAt_symm_of_mem_maximalAtlas hc hy.1
    have hgz : mfderiv (realModel d) 𝓘(ℝ, ℂ) g (c.symm y) = 0 := by
      ext v
      have hh := congrArg (fun A ↦ A v) (hzero (c.symm y) hy.2)
      change mfderiv (realModel d) 𝓘(ℝ, ℂ) g (c.symm y) v = 0 at hh ⊢
      exact hh
    rw [← mfderiv_eq_fderiv, mfderiv_comp y (hgy.mdifferentiableAt (by simp))
      (hcy.mdifferentiableAt (by simp)), hgz, ContinuousLinearMap.zero_comp]
    rfl
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hcx)
  have hdiff := hq.contDiffOn.differentiableOn (by simp)
  obtain ⟨a, ha⟩ := Metric.isOpen_ball.exists_is_const_of_fderiv_eq_zero
    (convex_ball (c x) r).isPreconnected (hdiff.mono hrT) (fun y hy ↦ hd y (hrT hy))
  let W : Set M := c.source ∩ c ⁻¹' Metric.ball (c x) r
  have hW : IsOpen W := c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  refine ⟨W, hW, ⟨mem_chart_source _ x, Metric.mem_ball_self hr⟩, ?_, ?_⟩
  · intro y hy
    have hh := (hrT hy.2).2
    simpa only [Set.mem_preimage, c.left_inv hy.1] using hh
  · intro y hy
    have hya := ha (c y) hy.2
    have hxa := ha (c x) (Metric.mem_ball_self hr)
    simpa only [Function.comp_apply, c.left_inv hy.1, c.left_inv (mem_chart_source _ x)]
      using hya.trans hxa.symm


end
end HolomorphicAnosov.Paper.Zhang
