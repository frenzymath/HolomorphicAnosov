import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set

namespace HolomorphicAnosov

/-- A finite open partial homeomorphism cover of a compact Hausdorff space admits compact source cores with a uniform coordinate slice buffer (Ghys, Lemma 3.3, p.593). -/
theorem compact_flowbox_slice_buffers
    {X E T J : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [PseudoMetricSpace E] [PseudoMetricSpace T] [Finite J]
    (c : J → OpenPartialHomeomorph X (E × T))
    (hc : ∀ x : X, ∃ j, x ∈ (c j).source) :
    ∃ (K : J → Set X) (δ : J → ℝ),
      (∀ j, IsCompact (K j)) ∧ (∀ j, K j ⊆ (c j).source) ∧
      (Set.univ : Set X) ⊆ ⋃ j, interior (K j) ∧
      (∀ j, 0 < δ j) ∧
      ∀ j x, x ∈ K j → Metric.closedBall ((c j x).1) (δ j) ⊆
        {z : E | (z, (c j x).2) ∈ (c j).target} := by
  classical
  have hcover : (Set.univ : Set X) ⊆ ⋃ j, (c j).source := by
    intro x _
    obtain ⟨j, hj⟩ := hc x
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨V, hVcover, hVopen, hVclosure, hVcompact⟩ :=
    exists_subset_iUnion_closure_subset_t2space
      (s := (Set.univ : Set X)) isCompact_univ
      (fun j ↦ (c j).open_source) (fun _ _ ↦ Set.toFinite _) hcover
  have hcores : (Set.univ : Set X) ⊆ ⋃ j, interior (closure (V j)) := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hVcover hx)
    exact Set.mem_iUnion.mpr
      ⟨j, (hVopen j).subset_interior_iff.mpr subset_closure hj⟩
  have hbuffer (j : J) : ∃ δ : ℝ, 0 < δ ∧
      Metric.cthickening δ ((c j) '' closure (V j)) ⊆ (c j).target := by
    have hcompact := (hVcompact j).image_of_continuousOn
      ((c j).continuousOn.mono (hVclosure j))
    apply hcompact.exists_cthickening_subset_open (c j).open_target
    rintro _ ⟨x, hx, rfl⟩
    exact (c j).map_source (hVclosure j hx)
  choose δ hδpos hδtarget using hbuffer
  refine ⟨fun j ↦ closure (V j), δ, hVcompact, hVclosure, hcores, hδpos, ?_⟩
  intro j x hx z hz
  apply hδtarget j
  apply Metric.closedBall_subset_cthickening (Set.mem_image_of_mem (c j) hx) (δ j)
  change dist (z, (c j x).2) (c j x) ≤ δ j
  rw [← Prod.eta (c j x), dist_prod_same_right]
  exact hz

end HolomorphicAnosov

