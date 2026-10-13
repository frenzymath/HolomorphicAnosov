import HolomorphicAnosov.Topology.CairnsHalfDiskBoundaryTransport

open Set
namespace HolomorphicAnosov.Topology

/-- A self-embedding of the circle is onto. Source: the elementary two-arc
argument in Cairns (1951), §5, pp.866–867. Split the domain at two distinct
points. Each image arc is one of the two directed target arcs. The two image
arcs cannot occupy the same target arc: an interior point would belong to
both, although their intersection consists only of the endpoints. Hence they
occupy opposite arcs and cover the circle. -/
theorem circle_embedding_surjective (f : Circle → Circle) (hf : _root_.Topology.IsEmbedding f) :
    Function.Surjective f := by
  have hne : (1 : Circle) ≠ -1 := by
    intro h
    have := congrArg (fun z : Circle ↦ (z : ℂ)) h
    norm_num at this
  obtain ⟨u, v, hu, hv, huv, a, b, ha, hb, ha0, ha1, hb0, hb1, hcover, hmeet⟩ :=
    circle_split_two_arcs f hf (f 1) (f (-1)) (mem_range_self 1)
      (mem_range_self (-1)) (hf.injective.ne hne)
  have hends : f 1 ≠ f (-1) := hf.injective.ne hne
  have hac := cairns_circle_arc_range a ha
  have hbc := cairns_circle_arc_range b hb
  rw [ha0, ha1] at hac
  rw [hb0, hb1] at hbc
  have hproper (x y : Circle) (hxy : x ≠ y) :
      range (Circle.path x y) ≠ ({x, y} : Set Circle) := by
    let t : unitInterval := ⟨1/2, by norm_num⟩
    intro h
    have ht : Circle.path x y t ∈ ({x, y} : Set Circle) := h ▸ mem_range_self t
    rcases ht with ht | ht
    · have he := Circle.path_injective_of_ne hxy (ht.trans (Circle.path x y).source.symm)
      have he' := congrArg (fun s : unitInterval ↦ (s : ℝ)) he
      norm_num [t] at he'
    · have he := Circle.path_injective_of_ne hxy (ht.trans (Circle.path x y).target.symm)
      have he' := congrArg (fun s : unitInterval ↦ (s : ℝ)) he
      norm_num [t] at he'
  have hall : range f = univ := by
    rw [← hcover]
    rcases hac with hac | hac <;> rcases hbc with hbc | hbc
    · rw [hac, hbc]
      exact Circle.range_path_union_range_path hends
    · have hsame : range a = range b := hac.trans hbc.symm
      rw [← hsame, inter_self, hac] at hmeet
      exact (hproper _ _ hends hmeet).elim
    · have hsame : range a = range b := hac.trans hbc.symm
      rw [← hsame, inter_self, hac] at hmeet
      exact (hproper _ _ hends.symm (by simpa [pair_comm] using hmeet)).elim
    · rw [hac, hbc]
      exact Circle.range_path_union_range_path hends.symm
  exact range_eq_univ.mp hall

/-- Inclusion of two embedded circles in a Hausdorff space forces equality.
Source: Cairns §5 two-arc argument, applied to the induced circle embedding. -/
theorem embedded_circle_range_eq {X : Type*} [TopologicalSpace X] [T2Space X]
    (f g : Circle → X) (hf : _root_.Topology.IsEmbedding f) (hg : _root_.Topology.IsEmbedding g)
    (hsub : range f ⊆ range g) : range f = range g := by
  let k : Circle → Circle := fun z ↦ hg.toHomeomorph.symm ⟨f z, hsub (mem_range_self z)⟩
  have hk : _root_.Topology.IsEmbedding k := hg.toHomeomorph.symm.isEmbedding.comp
    (hf.codRestrict _ (fun z ↦ hsub (mem_range_self z)))
  apply Subset.antisymm hsub
  rintro x ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := circle_embedding_surjective k hk z
  refine ⟨w, ?_⟩
  have hh := congrArg (fun t : Circle ↦ (hg.toHomeomorph t : X)) hw
  change (hg.toHomeomorph (hg.toHomeomorph.symm ⟨f w, _⟩) : X) = g z at hh
  simpa only [hg.toHomeomorph.apply_symm_apply] using hh

end HolomorphicAnosov.Topology
