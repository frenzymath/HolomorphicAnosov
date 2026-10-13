import HolomorphicAnosov.Topology.FiniteCoverIntersectionChain
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Variation bounds from finite closed covers

Agent-written weighted intersection-chain and disjoint-core packing refinements
of Ghys, *Holomorphic Anosov systems* (1995), §4 p.596, Fact 1.
DAG node: `topo.finite_closed_cover_variation_g17`.
-/

open Set
namespace HolomorphicAnosov

private theorem walk_variation {ι α β : Type*} [PseudoMetricSpace β]
    (s : ι → Set α) (f : α → β) (w : ι → ℝ)
    (hw : ∀ i, ∀ x ∈ s i, ∀ y ∈ s i, dist (f x) (f y) ≤ w i)
    (G : SimpleGraph ι) (hG : ∀ i j, G.Adj i j → (s i ∩ s j).Nonempty)
    {i j : ι} (p : G.Walk i j) :
    ∀ x ∈ s i, ∀ y ∈ s j, dist (f x) (f y) ≤ (p.support.map w).sum := by
  induction p with
  | nil =>
    intro x hx y hy
    simpa using hw _ x hx y hy
  | @cons i j k hij p ih =>
    intro x hx y hy
    obtain ⟨z, hzi, hzj⟩ := hG i j hij
    calc
      dist (f x) (f y) ≤ dist (f x) (f z) + dist (f z) (f y) := dist_triangle _ _ _
      _ ≤ w i + (p.support.map w).sum := add_le_add (hw i x hx z hzi) (ih z hzj y hy)
      _ = _ := by simp

/-- A finite closed cover of a preconnected set bounds the variation of any map
by the sum of nonnegative bounds for its variation on each cover member.

Agent-written weighted form of Ghys, Holomorphic Anosov systems (1995), §4
p.596, Fact 1, used in the Markov-free replacement proof of Proposition 4.1.
The cover members need not be connected. The intersection graph is connected
by preconnectedness of the covered core. Choose a simple path in that graph
between members containing the endpoints. Choose points in consecutive
intersections and apply the triangle inequality. The path visits each member
at most once, so nonnegative weights bound its cost by the total cover weight.
No continuity of the map is required once its within-member bounds are given. -/
theorem finite_closed_cover_variation
    {ι α β : Type*} [Fintype ι] [TopologicalSpace α] [PseudoMetricSpace β]
    (K : Set α) (s : ι → Set α) (f : α → β) (w : ι → ℝ)
    (hclosed : ∀ i, IsClosed (s i)) (hmeets : ∀ i, (K ∩ s i).Nonempty)
    (hpre : IsPreconnected K) (hcover : K ⊆ ⋃ i, s i)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, ∀ x ∈ s i, ∀ y ∈ s i, dist (f x) (f y) ≤ w i)
    {x y : α} (hx : x ∈ K) (hy : y ∈ K) :
    dist (f x) (f y) ≤ ∑ i, w i := by
  classical
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hy)
  let G : SimpleGraph ι := {
    Adj := fun i j ↦ i ≠ j ∧ (s i ∩ s j).Nonempty
    symm := ⟨by intro i j h; exact ⟨h.1.symm, by simpa [inter_comm] using h.2⟩⟩
    loopless := ⟨by intro i h; exact h.1 rfl⟩ }
  have hreach : G.Reachable i j := by
    clear hyj
    have h := finite_cover_intersection_chain K s hclosed hmeets hpre hcover i j
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c h hbc ih =>
      by_cases he : b = c
      · simpa [he] using ih
      · exact ih.trans (SimpleGraph.Adj.reachable (show G.Adj b c from ⟨he, hbc⟩))
  obtain ⟨p, hp, _⟩ := hreach.exists_path_of_dist
  have hdist := walk_variation s f w hw G (fun _ _ h ↦ h.2) p x hxi y hyj
  apply hdist.trans
  rw [← List.sum_toFinset _ hp.support_nodup]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hw0 i)

/-- If each member of a finite closed cover meets at most one of a finite
family of preconnected cores, and the map varies by at least `η` between
specified endpoints in each core, the total cover weight is at least the
number of cores times `η`.

This is the path-packing step of the agent-written Markov-free argument for
Ghys Proposition 4.1. Apply the preceding estimate separately to the cover
members meeting each core. Sum these estimates. Interchanging the finite
sums shows that a weight occurs at most once, by the meeting hypothesis;
nonnegativity absorbs weights occurring zero times. Empty families and zero
weights require no exception. -/
theorem finite_closed_cover_packing_variation
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    [TopologicalSpace α] [PseudoMetricSpace β]
    (K : κ → Set α) (s : ι → Set α) (f : α → β) (w : ι → ℝ)
    (hclosed : ∀ i, IsClosed (s i))
    (hpre : ∀ k, IsPreconnected (K k)) (hcover : ∀ k, K k ⊆ ⋃ i, s i)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, ∀ x ∈ s i, ∀ y ∈ s i, dist (f x) (f y) ≤ w i)
    (honly : ∀ i k l, (K k ∩ s i).Nonempty → (K l ∩ s i).Nonempty → k = l)
    (x y : κ → α) (hx : ∀ k, x k ∈ K k) (hy : ∀ k, y k ∈ K k)
    (η : ℝ) (hgap : ∀ k, η ≤ dist (f (x k)) (f (y k))) :
    (Fintype.card κ : ℝ) * η ≤ ∑ i, w i := by
  classical
  let meets := fun k i ↦ (K k ∩ s i).Nonempty
  have hlocal (k : κ) : η ≤ ∑ i, if meets k i then w i else 0 := by
    have hc : K k ⊆ ⋃ i : {i // meets k i}, s i := by
      intro z hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover k hz)
      exact mem_iUnion.mpr ⟨⟨i, z, hz, hi⟩, hi⟩
    have h := finite_closed_cover_variation (K k) (fun i : {i // meets k i} ↦ s i)
      f (fun i ↦ w i) (fun i ↦ hclosed i) (fun i ↦ i.property)
      (hpre k) hc (fun i ↦ hw0 i) (fun i ↦ hw i) (hx k) (hy k)
    have hh := (hgap k).trans h
    rw [← Finset.sum_subtype (Finset.univ.filter (meets k)) (by simp) w] at hh
    simpa only [Finset.sum_filter] using hh
  calc
    (Fintype.card κ : ℝ) * η = ∑ k : κ, η := by simp
    _ ≤ ∑ k : κ, ∑ i : ι, if meets k i then w i else 0 := Finset.sum_le_sum (fun k _ ↦ hlocal k)
    _ = ∑ i : ι, ∑ k : κ, if meets k i then w i else 0 := Finset.sum_comm
    _ ≤ ∑ i : ι, w i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : ∃ k, meets k i
      · obtain ⟨k, hk⟩ := h
        rw [Finset.sum_eq_single k]
        · simp [hk]
        · intro l _ hl
          have hnot : ¬ meets l i := fun hlm ↦ hl (honly i l k hlm hk)
          simp [hnot]
        · simp
      · have hn : ∀ k, ¬ meets k i := not_exists.mp h
        simpa [hn] using hw0 i

end HolomorphicAnosov
