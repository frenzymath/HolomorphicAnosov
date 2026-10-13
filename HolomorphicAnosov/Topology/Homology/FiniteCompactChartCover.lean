import Mathlib.Geometry.Manifold.ChartedSpace

/-!
Finite compact pieces inside chart domains. (Hatcher, Lemma 3.27)
-/

open Set
namespace HolomorphicAnosov

/-- Every compact subset of a Hausdorff space locally homeomorphic to a locally compact model is a finite union of compact pieces contained in chart domains. (Hatcher, Lemma 3.27) -/
theorem finite_compact_chart_cover {M H : Type*} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace H] [LocallyCompactSpace H]
    (hM : ∀ x : M, ∃ e : OpenPartialHomeomorph M H, x ∈ e.source)
    (K : Set M) (hK : IsCompact K) :
    ∃ s : Finset K, ∃ F : K → Set M,
      (∀ x ∈ s, IsCompact (F x) ∧ F x ⊆ K ∧
        ∃ e : OpenPartialHomeomorph M H, F x ⊆ e.source) ∧
      K = ⋃ x ∈ s, F x := by
  classical
  choose e he using hM
  let : ChartedSpace H M := {
    atlas := Set.univ
    chartAt := e
    mem_chart_source := he
    chart_mem_atlas := fun _ ↦ Set.mem_univ _ }
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hn (x : K) : ∃ C : Set M, IsCompact C ∧ x.val ∈ interior C ∧ C ⊆ (e x.val).source :=
    exists_compact_subset (e x.val).open_source (he x.val)
  choose C hCc hxC hCe using hn
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ interior (C x))
    (fun _ ↦ isOpen_interior) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x,hx⟩, hxC ⟨x,hx⟩⟩)
  refine ⟨s, fun x ↦ K ∩ C x, ?_, ?_⟩
  · intro x hx
    exact ⟨hK.inter_right (hCc x).isClosed, Set.inter_subset_left,
      e x.val, Set.inter_subset_right.trans (hCe x)⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Set.mem_iUnion₂.mpr ⟨y, hy, hx, interior_subset hxy⟩
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact hxy.1

end HolomorphicAnosov

