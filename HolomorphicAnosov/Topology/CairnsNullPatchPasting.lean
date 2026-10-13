import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Homeomorph.Lemmas

open Set Filter
open scoped Topology
namespace HolomorphicAnosov

/-- A sequential null family has only finitely many members above any
positive size. Otherwise an injective sequence of such members contradicts
convergence to zero. This is the finite-large-gap argument in Cairns §4(C). -/
theorem null_family_finite_large {ι : Type*} (size : ι → ℝ)
    (hnull : ∀ j : ℕ → ι, Function.Injective j → Tendsto (size ∘ j) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) : {i | ε ≤ size i}.Finite := by
  classical
  by_contra hi
  let e := Set.Infinite.natEmbedding {i | ε ≤ size i} hi
  have he : Function.Injective (fun n ↦ (e n).val) :=
    Subtype.val_injective.comp e.injective
  have hh := (hnull _ he).eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := hh.exists
  exact (not_lt_of_ge (e n).property) hn

/-- Null patches based on a closed set are locally finite off that set.
Source: Cairns §4(C), pp.864–865. Around a point away from the base choose a
ball whose radius is smaller than its distance from the base. Every patch
meeting the half-sized ball must have size at least half that radius, and
there are only finitely many such patches. -/
theorem null_patch_locallyFinite_off_base
    {E ι : Type*} [MetricSpace E]
    (B : Set E) (hB : IsClosed B) (K : ι → Set E)
    (anchor : ι → E) (ha : ∀ i, anchor i ∈ B) (size : ι → ℝ)
    (hsize : ∀ i x, x ∈ K i → dist x (anchor i) ≤ size i)
    (hnull : ∀ j : ℕ → ι, Function.Injective j → Tendsto (size ∘ j) atTop (nhds 0)) :
    LocallyFinite (fun i ↦ {x : ↥(Bᶜ) | (x : E) ∈ K i}) := by
  intro x
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hB.isOpen_compl x.val x.property
  refine ⟨Metric.ball x (r / 2), Metric.ball_mem_nhds _ (half_pos hr),
    (null_family_finite_large size hnull (r / 2) (half_pos hr)).subset ?_⟩
  rintro i ⟨y,hyK,hyball⟩
  have hax : r ≤ dist (anchor i) x.val := by
    by_contra hh
    exact hball (show anchor i ∈ Metric.ball x.val r from lt_of_not_ge hh) (ha i)
  have hyx : dist y.val x.val < r / 2 := hyball
  have hxy := dist_triangle (anchor i) y.val x.val
  rw [dist_comm (anchor i) y.val] at hxy
  have hs := hsize i y.val hyK
  change r / 2 ≤ size i
  linarith

/-- A null family of individually bounded patches, based on a bounded set,
has bounded union. All but finitely many patches lie in the unit thickening
of the base; the exceptional finite union is bounded as well. -/
theorem null_patch_union_isBounded
    {E ι : Type*} [PseudoMetricSpace E]
    (B : Set E) (hB : Bornology.IsBounded B) (K : ι → Set E)
    (hK : ∀ i, Bornology.IsBounded (K i))
    (anchor : ι → E) (ha : ∀ i, anchor i ∈ B) (size : ι → ℝ)
    (hsize : ∀ i x, x ∈ K i → dist x (anchor i) ≤ size i)
    (hnull : ∀ j : ℕ → ι, Function.Injective j → Tendsto (size ∘ j) atTop (nhds 0)) :
    Bornology.IsBounded (B ∪ ⋃ i, K i) := by
  have hf := null_family_finite_large size hnull 1 zero_lt_one
  have he : Bornology.IsBounded (⋃ i ∈ {i | 1 ≤ size i}, K i) :=
    (Bornology.isBounded_biUnion hf).mpr (fun i _ ↦ hK i)
  apply (hB.thickening.union he).subset
  rintro x (hx | hx)
  · exact Or.inl (Metric.self_subset_thickening zero_lt_one B hx)
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    by_cases hh : 1 ≤ size i
    · exact Or.inr (mem_iUnion₂.mpr ⟨i,hh,hi⟩)
    · exact Or.inl (Metric.mem_thickening_iff.mpr
        ⟨anchor i,ha i,(hsize i x hi).trans_lt (lt_of_not_ge hh)⟩)

/-- A bounded union of compact patches is compact if distinct patches shrink
uniformly toward marked points in a compact base. Source: the accumulation
argument in Cairns (1951), §4(B,C), pp.864–865. A convergent sequence either uses
finitely many patches, or has a subsequence of distinct patches whose distance
to the compact base tends to zero. Both alternatives keep its limit in the union. -/
theorem null_patch_union_isCompact
    {E ι : Type*} [MetricSpace E] [ProperSpace E]
    (B : Set E) (hB : IsCompact B) (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (anchor : ι → E) (ha : ∀ i, anchor i ∈ B) (size : ι → ℝ)
    (hsize : ∀ i x, x ∈ K i → dist x (anchor i) ≤ size i)
    (hnull : ∀ j : ℕ → ι, Function.Injective j → Tendsto (size ∘ j) atTop (nhds 0))
    : IsCompact (B ∪ ⋃ i, K i) := by
  classical
  have hbounded := null_patch_union_isBounded B hB.isBounded K
    (fun i ↦ (hK i).isBounded) anchor ha size hsize hnull
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, hbounded⟩
  apply IsSeqClosed.isClosed
  intro x z hx hz
  by_cases hzb : z ∈ B
  · exact Or.inl hzb
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hz.eventually (hB.isClosed.isOpen_compl.mem_nhds hzb))
  have hm (n : ℕ) : ∃ i, x (n + N) ∈ K i :=
    mem_iUnion.mp ((hx (n + N)).resolve_left (hN _ (Nat.le_add_left _ _)))
  choose j hj using hm
  have hlim : Tendsto (fun n ↦ x (n + N)) atTop (nhds z) :=
    hz.comp (tendsto_add_atTop_nat N)
  by_cases hf : (range j).Finite
  · have hc := hf.isClosed_biUnion (fun i _ ↦ (hK i).isClosed)
    have hzK : z ∈ ⋃ i ∈ range j, K i :=
      hc.mem_of_tendsto hlim (Eventually.of_forall (fun n ↦
        mem_iUnion₂.mpr ⟨j n, mem_range_self n, hj n⟩))
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hzK
    exact Or.inr (mem_iUnion.mpr ⟨i,hzi⟩)
  · let e := Set.Infinite.natEmbedding (range j) hf
    choose k hk using (fun n ↦ (e n).property)
    have hki : Function.Injective k := by
      intro n m hnm
      apply e.injective
      apply Subtype.ext
      rw [← hk n, ← hk m, hnm]
    have hji : Function.Injective (j ∘ k) := by
      intro n m hnm
      apply e.injective
      apply Subtype.ext
      simpa only [Function.comp_apply, hk] using hnm
    have hclose : Tendsto (fun n ↦ dist (x (k n + N)) (anchor (j (k n))))
        atTop (nhds 0) :=
      squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ hsize _ _ (hj (k n)))
        (hnull (j ∘ k) hji)
    have hpz := (hlim.comp hki.nat_tendsto_atTop).congr_dist hclose
    exact (hzb (hB.isClosed.mem_of_tendsto hpz
      (Eventually.of_forall (fun n ↦ ha (j (k n)))))).elim

/-- A function with compact graph over a Hausdorff domain is continuous.
The first projection of its graph is a continuous bijection from a compact
space to a Hausdorff space, hence a homeomorphism. The second projection after
its inverse is the original function. -/
theorem continuousOn_of_compact_graph
    {E F : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace F]
    (S : Set E) (f : E → F)
    (hg : IsCompact ((fun x ↦ (x, f x)) '' S)) : ContinuousOn f S := by
  classical
  let G := (fun x ↦ (x, f x)) '' S
  let : CompactSpace G := isCompact_iff_compactSpace.mp hg
  let π : G → S := fun w ↦ ⟨w.1.1, by
    rcases w.2 with ⟨x, hx, he⟩
    exact he ▸ hx⟩
  have hc : Continuous π :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective π := by
    rintro ⟨w, x, hx, rfl⟩ ⟨z, y, hy, rfl⟩ he
    apply Subtype.ext
    have hxy : x = y := congrArg Subtype.val he
    simp only [hxy]
  have hs : Function.Surjective π := fun x ↦
    ⟨⟨(x, f x), x, x.property, rfl⟩, rfl⟩
  let e := Equiv.ofBijective π ⟨hi, hs⟩
  let H : G ≃ₜ S := Continuous.homeoOfEquivCompactToT2 (f := e) hc
  have hsymm (x : S) : H.symm x = ⟨(x, f x), x, x.property, rfl⟩ := by
    apply H.injective
    exact H.apply_symm_apply x
  rw [continuousOn_iff_continuous_domRestrict]
  have hh := (continuous_snd.comp continuous_subtype_val).comp H.symm.continuous
  convert hh using 1
  funext x
  simp only [Function.comp_apply, hsymm]
  rfl

/-- Pasting over a null family of compact patches preserves continuity.
Source: Cairns (1951), §4(B,C), pp.864–865. The graph on the base is compact;
the graphs on distinct patches approach marked points on that base graph.
Thus the full graph is compact, and its first projection gives continuity. -/
theorem null_patch_continuousOn
    {E F ι : Type*} [MetricSpace E] [ProperSpace E]
    [MetricSpace F] [ProperSpace F]
    (B : Set E) (hB : IsCompact B) (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (f : E → F) (hfB : ContinuousOn f B) (hfK : ∀ i, ContinuousOn f (K i))
    (anchor : ι → E) (ha : ∀ i, anchor i ∈ B) (size : ι → ℝ)
    (hsize : ∀ i x, x ∈ K i → dist x (anchor i) ≤ size i ∧
      dist (f x) (f (anchor i)) ≤ size i)
    (hnull : ∀ j : ℕ → ι, Function.Injective j → Tendsto (size ∘ j) atTop (nhds 0)) :
    ContinuousOn f (B ∪ ⋃ i, K i) := by
  let g := fun x ↦ (x, f x)
  apply continuousOn_of_compact_graph
  have hgraph : g '' (B ∪ ⋃ i, K i) = g '' B ∪ ⋃ i, g '' K i := by
    rw [image_union, image_iUnion]
  rw [hgraph]
  apply null_patch_union_isCompact (g '' B)
    (hB.image_of_continuousOn (continuousOn_id.prodMk hfB))
    (fun i ↦ g '' K i)
    (fun i ↦ (hK i).image_of_continuousOn (continuousOn_id.prodMk (hfK i)))
    (g ∘ anchor) (fun i ↦ mem_image_of_mem g (ha i)) size ?_ hnull
  rintro i w ⟨x, hx, rfl⟩
  exact max_le (hsize i x hx).1 (hsize i x hx).2

end HolomorphicAnosov


