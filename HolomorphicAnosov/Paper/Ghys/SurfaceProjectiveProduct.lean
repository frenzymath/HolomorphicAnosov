import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveDevelopmentExists
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveCompleteLeaves
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveLiftComponent
import HolomorphicAnosov.Paper.Ghys.CompleteAffineLeafHolomorphicLift
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundleFinrank
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.NoSurjectiveOriginalMetricContraction
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Paper.Ghys.ProjectiveDeveloping
import HolomorphicAnosov.Paper.Ghys.Proposition31
import HolomorphicAnosov.Paper.Ghys.Proposition41
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Ghys.SurfaceHolomorphicProductCharts
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import Mathlib.Topology.Connected.Basic

/-!
# The ordered projective product of a holomorphic Anosov surface

This file constructs the ordered projective product atlas and its development for a compact holomorphic Anosov surface, including the biholomorphic images of complete lifted leaves (Ghys, §§2–5).
-/

noncomputable section

open Set _root_.Topology
open scoped ContDiff Bundle

namespace HolomorphicAnosov.Ghys

universe u v

attribute [local instance] complex_isManifold_real

/-- The universal set of a compact complex surface is connected and nonempty. -/
theorem compactComplexSurface_univ_connected_nonempty
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S] :
    IsConnected (Set.univ : Set S) ∧ (Set.univ : Set S).Nonempty := by
  exact ⟨isConnected_univ, Set.univ_nonempty⟩

/-- A compact complex surface is nontrivial. -/
theorem compactComplexSurface_nontrivial
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S] : Nontrivial S := by
  obtain ⟨x⟩ : Nonempty S := inferInstance
  let e := chartAt (ComplexModel 2) x
  have he : Preperfect e.target := e.open_target.preperfect
  obtain ⟨z, hz, hzne⟩ := (preperfect_iff_nhds.mp he) (e x)
      (mem_chart_target (ComplexModel 2) x) Set.univ (by simp)
  let y : S := e.symm z
  have hxy : x ≠ y := by
    intro hxy
    apply hzne
    rw [← e.right_inv hz.2]
    exact congrArg e hxy.symm
  exact ⟨⟨x, y, hxy⟩⟩

/-- Every point of a compact complex surface is a limit point. -/
theorem compactComplexSurface_no_isolated
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S] (x : S) :
    Filter.NeBot (𝓝[≠] x) := by
  have : Nontrivial S := compactComplexSurface_nontrivial (S := S)
  infer_instance

/-- Every neighborhood of a point on a compact complex surface contains a distinct point. -/
theorem compactComplexSurface_exists_ne_mem_nhds
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S] (x : S) {U : Set S} (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, y ≠ x := by
  have hx : x ∈ closure ({y : S | y ≠ x}) := by
    rw [mem_closure_iff_nhdsWithin_neBot]
    change Filter.NeBot (𝓝[({x}ᶜ : Set S)] x)
    exact compactComplexSurface_no_isolated (S := S) x
  rw [mem_closure_iff_nhds'] at hx
  obtain ⟨y, hyU⟩ := hx U hU
  exact ⟨y, hyU, y.property⟩

/-- A compact connected holomorphic Anosov surface admits an ordered projective product atlas whose development maps complete lifted stable and unstable leaves biholomorphically onto punctured projective coordinate lines (Ghys, pp. 588–590 and 597–599). -/
theorem surface_projective_product
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f) :
    ∃ A : OrderedProjectiveProductAtlas.{u, u} f a,
      ∀ (U : Type v) [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
        [IsManifold (complexModel 2) ∞ U] (p : U → S),
        IsCoveringMap p → Function.Surjective p → SimplyConnectedSpace U →
        IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ p →
        ∃ D : OrderedProjectiveProductDevelopment A p,
          letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
          (∀ u : U,
            let L := A.stableLeaf (p u)
            letI := L.native.topology
            letI := L.complexCharts
            ∃ lift : StableAsymptoticLeaf f.toHomeomorph (p u) → U,
              ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
              Function.Injective lift ∧
              (∀ z, p (lift z) = z.val) ∧
              Set.range lift = connectedComponentIn
                {v : U | (D.developingMap v).2 = (D.developingMap u).2} u ∧
              ∃ (pole : ComplexProjectiveLine)
                (e : OpenPartialHomeomorph
                  (StableAsymptoticLeaf f.toHomeomorph (p u)) ComplexProjectiveLine),
                e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
                (∀ z, e z = (D.developingMap (lift z)).1) ∧
                ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
                ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target ∧
                Set.range (fun z ↦ D.developingMap (lift z)) =
                  {q | q.1 ≠ pole ∧ q.2 = (D.developingMap u).2}) ∧
          (∀ u : U,
            let L := A.unstableLeaf (p u)
            letI := L.native.topology
            letI := L.complexCharts
            ∃ lift : UnstableAsymptoticLeaf f.toHomeomorph (p u) → U,
              ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
              Function.Injective lift ∧
              (∀ z, p (lift z) = z.val) ∧
              Set.range lift = connectedComponentIn
                {v : U | (D.developingMap v).1 = (D.developingMap u).1} u ∧
              ∃ (pole : ComplexProjectiveLine)
                (e : OpenPartialHomeomorph
                  (UnstableAsymptoticLeaf f.toHomeomorph (p u)) ComplexProjectiveLine),
                e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
                (∀ z, e z = (D.developingMap (lift z)).2) ∧
                ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
                ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target ∧
                Set.range (fun z ↦ D.developingMap (lift z)) =
                  {q | q.1 = (D.developingMap u).1 ∧ q.2 ≠ pole}) := by
  let : Nontrivial S := compactComplexSurface_nontrivial (S := S)
  let : Bundle.RiemannianBundle (fun x : S ↦ TangentSpace (realModel 2) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (ComplexModel 2)
      (fun x : S ↦ TangentSpace (realModel 2) x) :=
    ⟨a.metric.inner, a.metric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  obtain ⟨C, lam, hC, hlam, hlam1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
  have hlim : Filter.Tendsto (fun n : ℕ ↦ C * lam ^ n) Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hlam.le hlam1).const_mul C
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.mp hlim).2 1 zero_lt_one)
  have hq : 0 < C * lam ^ N := mul_pos hC (pow_pos hlam _)
  have hq1 : C * lam ^ N < 1 := hN N le_rfl
  classical
  by_cases hstable_full : ∀ x, a.splitting.stable.toDistribution x = ⊤
  · exfalso
    apply Proposition29Length.no_surjective_original_metric_contraction
      ((f : S → S)^[N])
      ((f.toReal.contMDiff_toFun.of_le (by simp)).iterate N)
      (f.surjective.iterate N) (C * lam ^ N) hq hq1
    intro x v
    exact hs N x v (by rw [hstable_full x]; trivial)
  by_cases hunstable_full : ∀ x, a.splitting.unstable.toDistribution x = ⊤
  · exfalso
    apply Proposition29Length.no_surjective_original_metric_contraction
      ((f.symm : S → S)^[N])
      ((f.toReal.symm.contMDiff_toFun.of_le (by simp)).iterate N)
      (f.symm.surjective.iterate N) (C * lam ^ N) hq hq1
    intro x v
    exact hu N x v (by rw [hunstable_full x]; trivial)
  obtain ⟨h, hh⟩ := OneFormBundle.original_smooth_tangent_metric_exists (d := 2) (M := S)
  obtain ⟨C', rate, hC', hrate, hs', hu'⟩ :=
    OneFormBundle.original_all_iterates_hermitian f a h hh
  let : TopologicalSpace.MetrizableSpace S := Manifold.metrizableSpace (realModel 2) S
  let : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  obtain ⟨s, t, hst, Es, Eu, hrank, hEs, hEu, _⟩ :=
    stableFoliations f h hh a.splitting C' rate hC' hrate hs' hu'
  have hs0 : s ≠ 0 := by
    intro hs0
    apply hunstable_full
    intro x
    have he : Es.toDistribution x = ⊥ :=
      Submodule.finrank_eq_zero.mp ((hrank x).1.trans hs0)
    have hz : a.splitting.stable.toDistribution x = ⊥ := by
      rw [← hEs x, he]
      simp
    simpa [hz] using (a.splitting.isCompl x).sup_eq_top
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hstable_full
    intro x
    have he : Eu.toDistribution x = ⊥ :=
      Submodule.finrank_eq_zero.mp ((hrank x).2.trans ht0)
    have hz : a.splitting.unstable.toDistribution x = ⊥ := by
      rw [← hEu x, he]
      simp
    simpa [hz] using (a.splitting.isCompl x).sup_eq_top
  have hs1 : s = 1 := by omega
  have ht1 : t = 1 := by omega
  have hstable : HasComplexRankOne a.splitting.stable.toDistribution := by
    intro x
    exact ⟨Es.toDistribution x, (hrank x).1.trans hs1, hEs x⟩
  have hunstable : HasComplexRankOne a.splitting.unstable.toDistribution := by
    intro x
    exact ⟨Eu.toDistribution x, (hrank x).2.trans ht1, hEu x⟩
  obtain ⟨A, _⟩ := surface_projective_g3_holomorphic_product_charts f a hstable hunstable
  refine ⟨A, ?_⟩
  intro U _ _ _ p hp hsurj hsimply hhol
  obtain ⟨D⟩ := ordered_projective_product_development_exists A hp hsurj hsimply hhol
  exact ⟨D, ordered_projective_complete_leaves A D⟩

end HolomorphicAnosov.Ghys
