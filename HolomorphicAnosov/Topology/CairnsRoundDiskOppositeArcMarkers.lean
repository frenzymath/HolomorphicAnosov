import HolomorphicAnosov.Topology.WhyburnCircleSplit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UnitInterval

/-! # Opposite circle-arc markers for a round-disk crosscut

Source: Cairns (1951), Lemma 5.1, p.866; the circle is split at the two crosscut
endpoints into its two directed arcs.
DAG node: `topo.cairns_round_disk_opposite_arc_markers_g20`.
-/

open Set Metric

namespace HolomorphicAnosov

/-- Select points on the two distinct open circle arcs between the crosscut endpoints.
The points avoid the endpoints and lie in different connected components of the
punctured unit circle.

The arc decomposition is supplied by `Topology.circle_split_two_arcs`. Choose the
parameter midpoint of each injective arc; injectivity excludes both marked endpoints.
If both markers lay in one component of the punctured circle, that preconnected
component would meet both closed arc images. The closed-cover characterization of
preconnectedness forces it to meet their intersection, which is exactly the deleted
endpoint pair. Component containment contradicts this. This is the elementary
punctured-circle argument underlying the choice in Cairns p.866. -/
theorem cairns_round_disk_opposite_arc_markers
    (g : unitInterval → closedBall (0 : ℂ) 1) (_hg : Topology.IsEmbedding g)
    (h0 : (g 0 : ℂ) ∈ sphere (0 : ℂ) 1)
    (h1 : (g 1 : ℂ) ∈ sphere (0 : ℂ) 1) (h01 : g 0 ≠ g 1) :
    ∃ a b : ℂ,
      a ∈ sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ) ∧
      b ∈ sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ) ∧
      b ∉ connectedComponentIn
        (sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ)) a := by
  have hj : Topology.IsEmbedding (fun z : Circle ↦ (z : ℂ)) :=
    Topology.IsEmbedding.subtypeVal
  have h0' : (g 0 : ℂ) ∈ Set.range (fun z : Circle ↦ (z : ℂ)) := by
    rw [Set.mem_range]
    exact ⟨⟨(g 0 : ℂ), h0⟩, rfl⟩
  have h1' : (g 1 : ℂ) ∈ Set.range (fun z : Circle ↦ (z : ℂ)) := by
    rw [Set.mem_range]
    exact ⟨⟨(g 1 : ℂ), h1⟩, rfl⟩
  obtain ⟨u, v, hu, hv, huv, e₂, e₃, he₂, he₃, he₂0, he₂1,
      he₃0, he₃1, heunion, heint⟩ :=
    Topology.circle_split_two_arcs (fun z : Circle ↦ (z : ℂ)) hj
      (g 0 : ℂ) (g 1 : ℂ) h0' h1' (fun h ↦ h01 (Subtype.ext h))
  let m : unitInterval := ⟨1 / 2, by norm_num⟩
  have hm0 : m ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [m] at this
  have hm1 : m ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [m] at this
  have hrange : range (fun z : Circle ↦ (z : ℂ)) = sphere (0 : ℂ) 1 := by
    ext z
    exact ⟨fun ⟨w, hw⟩ ↦ hw ▸ w.property, fun hz ↦ ⟨⟨z, hz⟩, rfl⟩⟩
  have ha : e₂ m ∈ sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ) := by
    refine ⟨hrange ▸ heunion ▸ Or.inl (mem_range_self m), ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h ↦ hm0 (he₂.injective (h.trans he₂0.symm)),
      fun h ↦ hm1 (he₂.injective (h.trans he₂1.symm))⟩
  have hb : e₃ m ∈ sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ) := by
    refine ⟨hrange ▸ heunion ▸ Or.inr (mem_range_self m), ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h ↦ hm1 (he₃.injective (h.trans he₃1.symm)),
      fun h ↦ hm0 (he₃.injective (h.trans he₃0.symm))⟩
  refine ⟨e₂ m, e₃ m, ha, hb, ?_⟩
  intro hsame
  let C := connectedComponentIn
    (sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ)) (e₂ m)
  have hsub : C ⊆ range e₂ ∪ range e₃ := by
    rw [heunion, hrange]
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  obtain ⟨z, hzC, hz₂, hz₃⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_connectedComponentIn (F := sphere (0 : ℂ) 1 \ {↑(g 0), ↑(g 1)})
      (x := e₂ m)) (range e₂) (range e₃)
    (isCompact_range he₂.continuous).isClosed
    (isCompact_range he₃.continuous).isClosed hsub
    ⟨e₂ m, mem_connectedComponentIn ha, mem_range_self m⟩
    ⟨e₃ m, hsame, mem_range_self m⟩
  exact (connectedComponentIn_subset _ _ hzC).2 (heint ▸ ⟨hz₂, hz₃⟩)

end HolomorphicAnosov

