import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment

/-!
# Assembly of an ordered projective product atlas from local box germs

This file assembles an ordered projective product atlas from local chart germs and their uniqueness and cocycle properties (Ghys, §5, pp. 597–598).
-/

noncomputable section

namespace HolomorphicAnosov.Ghys

open Set _root_.Topology
open scoped ContDiff Manifold

universe u

attribute [local instance] complex_isManifold_real

abbrev OrderedProjectiveTransition :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ×
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ


def OrderedProjectiveProductGerm
    {S : Type u} [TopologicalSpace S]
    (ι : Type u)
    (chart : ι → OpenPartialHomeomorph S
      (ComplexProjectiveLine × ComplexProjectiveLine))
    (i j : ι) (x : S) (g : OrderedProjectiveTransition) : Prop :=
  ∃ N : Set S, IsOpen N ∧ x ∈ N ∧
    N ⊆ (chart i).source ∩ (chart j).source ∧
    ∀ y ∈ N, chart j y =
      (g.1 • (chart i y).1, g.2 • (chart i y).2)


structure OrderedProjectiveProductGermData
    {S : Type u} [t : TopologicalSpace S]
    [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f) where
  metric : MetricSpace S
  metric_topology : t = metric.toUniformSpace.toTopologicalSpace
  stableLeaf : letI := metric.replaceTopology metric_topology
    ∀ x : S, NativeCompleteAffineAsymptoticLeaf f.toHomeomorph
      a.splitting.stable.toDistribution x
  unstableLeaf : letI := metric.replaceTopology metric_topology
    ∀ x : S, NativeCompleteAffineAsymptoticLeaf f.toHomeomorph.symm
      a.splitting.unstable.toDistribution x
  index : Type u
  chart : index → OpenPartialHomeomorph S
    (ComplexProjectiveLine × ComplexProjectiveLine)
  cover : ∀ x : S, ∃ i : index, x ∈ (chart i).source
  holomorphic : ∀ i : index,
    ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞
        (chart i) (chart i).source ∧
      ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞
        (chart i).symm (chart i).target
  local_germ : ∀ i j : index, ∀ x : S,
    x ∈ (chart i).source ∩ (chart j).source →
    ∃ g : OrderedProjectiveTransition,
      OrderedProjectiveProductGerm index chart i j x g
  local_unique : ∀ i j : index, ∀ x : S,
    x ∈ (chart i).source ∩ (chart j).source →
    ∀ g h : OrderedProjectiveTransition,
      OrderedProjectiveProductGerm index chart i j x g →
      OrderedProjectiveProductGerm index chart i j x h → g = h
  stable_kernel : ∀ (i : index) (x : S), x ∈ (chart i).source →
    LinearMap.ker (mfderiv (realModel 2) (realModel 1)
      (fun y ↦ (chart i y).2) x).toLinearMap =
        a.splitting.stable.toDistribution x
  unstable_kernel : ∀ (i : index) (x : S), x ∈ (chart i).source →
    LinearMap.ker (mfderiv (realModel 2) (realModel 1)
      (fun y ↦ (chart i y).1) x).toLinearMap =
        a.splitting.unstable.toDistribution x
  stable_affine : letI := metric.replaceTopology metric_topology
    ∀ (x : S) (i : index),
      let L := stableLeaf x
      letI := L.native.topology
      letI := L.complexCharts
      ∀ y : StableAsymptoticLeaf f.toHomeomorph x, y.val ∈ (chart i).source →
        ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
          y ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
            ∀ᶠ z in 𝓝 y, z ∈ c.source ∧ z.val ∈ (chart i).source ∧
              (chart i z.val).1 = g • complexProjectiveLineFinite (c z) ∧
              (chart i z.val).2 = (chart i y.val).2
  unstable_affine : letI := metric.replaceTopology metric_topology
    ∀ (x : S) (i : index),
      let L := unstableLeaf x
      letI := L.native.topology
      letI := L.complexCharts
      ∀ y : UnstableAsymptoticLeaf f.toHomeomorph x, y.val ∈ (chart i).source →
        ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
          y ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
            ∀ᶠ z in 𝓝 y, z ∈ c.source ∧ z.val ∈ (chart i).source ∧
              (chart i z.val).2 = g • complexProjectiveLineFinite (c z) ∧
              (chart i z.val).1 = (chart i y.val).1

/-!
The local projective germs determine locally constant transitions, the identity and cocycle laws, and the resulting ordered projective product atlas (Ghys, §5, pp. 597–598).
-/
noncomputable def orderedProjectiveProductAtlas_of_germData
    {S : Type u} [t : TopologicalSpace S]
    [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (D : OrderedProjectiveProductGermData f a) :
    OrderedProjectiveProductAtlas.{u, u} f a := by
  classical
  let tr : D.index → D.index → S → OrderedProjectiveTransition :=
    fun i j x ↦ if hx : x ∈ (D.chart i).source ∩ (D.chart j).source then
      Classical.choose (D.local_germ i j x hx) else 1
  have trspec (i j : D.index) (x : S)
      (hx : x ∈ (D.chart i).source ∩ (D.chart j).source) :
      OrderedProjectiveProductGerm D.index D.chart i j x (tr i j x) := by
    dsimp [tr]
    simpa only [dite_eq_left hx] using Classical.choose_spec (D.local_germ i j x hx)
  have trloc (i j : D.index) : IsLocallyConstant
      (fun x : ↥((D.chart i).source ∩ (D.chart j).source) ↦ tr i j x) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨N, hNo, hNx, hNsub, hNformula⟩ := trspec i j x x.property
    refine ⟨Subtype.val ⁻¹' N, hNo.preimage continuous_subtype_val, hNx, ?_⟩
    intro y hy
    have hyover : (y : S) ∈ (D.chart i).source ∩ (D.chart j).source :=
      hNsub hy
    obtain ⟨Ny, hNyo, hNy, hNysub, hNyformula⟩ := trspec i j y hyover
    apply D.local_unique i j y hyover (tr i j y) (tr i j x)
    · exact ⟨Ny, hNyo, hNy, hNysub, hNyformula⟩
    · exact ⟨N, hNo, hy, hNsub, hNformula⟩
  have tragree (i j : D.index) (x : S)
      (hx : x ∈ (D.chart i).source ∩ (D.chart j).source) :
      D.chart j x =
        ((tr i j x).1 • (D.chart i x).1,
          (tr i j x).2 • (D.chart i x).2) := by
    obtain ⟨N, _, hNx, _, hformula⟩ := trspec i j x hx
    exact hformula x hNx
  have trself (i : D.index) (x : S) (hx : x ∈ (D.chart i).source) :
      tr i i x = 1 := by
    apply D.local_unique i i x ⟨hx, hx⟩ (tr i i x) 1
      (trspec i i x ⟨hx, hx⟩)
    refine ⟨(D.chart i).source, (D.chart i).open_source, hx,
      fun y hy ↦ ⟨hy, hy⟩, ?_⟩
    intro y hy
    simp
  have trcomp (i j k : D.index) (x : S)
      (hx : x ∈ (D.chart i).source ∩ (D.chart j).source ∩
        (D.chart k).source) :
      tr i k x = tr j k x * tr i j x := by
    rcases hx with ⟨⟨hxi, hxj⟩, hxk⟩
    obtain ⟨Nij, hNijo, hNijx, hNijsub, hNijformula⟩ :=
      trspec i j x ⟨hxi, hxj⟩
    obtain ⟨Njk, hNjko, hNjkx, hNjksub, hNjkformula⟩ :=
      trspec j k x ⟨hxj, hxk⟩
    apply D.local_unique i k x ⟨hxi, hxk⟩ (tr i k x) (tr j k x * tr i j x)
      (trspec i k x ⟨hxi, hxk⟩)
    refine ⟨Nij ∩ Njk, hNijo.inter hNjko, ⟨hNijx, hNjkx⟩,
      fun y hy ↦ ⟨(hNijsub hy.1).1, (hNjksub hy.2).2⟩, ?_⟩
    intro y hy
    have hij := hNijformula y hy.1
    have hjk := hNjkformula y hy.2
    rw [hij] at hjk
    simpa [mul_smul] using hjk
  refine {
    metric := D.metric
    metric_topology := D.metric_topology
    stableLeaf := D.stableLeaf
    unstableLeaf := D.unstableLeaf
    index := D.index
    chart := D.chart
    cover := D.cover
    holomorphic := D.holomorphic
    transition := tr
    transition_locallyConstant := trloc
    transition_self := trself
    transition_comp := trcomp
    transition_agrees := tragree
    stable_kernel := D.stable_kernel
    unstable_kernel := D.unstable_kernel
    stable_affine := D.stable_affine
    unstable_affine := D.unstable_affine }

end HolomorphicAnosov.Ghys

