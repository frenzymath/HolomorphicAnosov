import HolomorphicAnosov.Topology.CairnsRoundDiskCrosscutSeparation
import HolomorphicAnosov.Topology.DiskChartOpenInteriorBoundary
import Mathlib.Topology.Homeomorph.Lemmas

open Set Metric
namespace HolomorphicAnosov

/-- Transport the two closed crosscut cells through a supplied closed-disk chart.
Source: Cairns (1951), §5, pp.866–867. The inverse chart is a closed embedding;
it carries relative closures to ambient closures. On the open disk it is an
open embedding by planar invariance of domain. Consequently the two transported
cells are open and connected, cover the cut complement, and their closures meet
in precisely the full crosscut. Restricting the inverse chart to either closed
cell transports its disk chart as well. -/
theorem cairns_disk_chart_crosscut
    (U : Set ℂ) (hU : IsOpen U)
    (F : closure U ≃ₜ closedBall (0 : ℂ) 1)
    (hF : ∀ z : closure U, (z : ℂ) ∈ U ↔ (F z : ℂ) ∈ ball (0 : ℂ) 1)
    (b : unitInterval → ℂ) (hb : Topology.IsEmbedding b)
    (hbc : range b ⊆ closure U)
    (h0 : b 0 ∈ frontier U) (h1 : b 1 ∈ frontier U)
    (hi : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → b t ∈ U) :
    ∃ V : Fin 2 → Set ℂ,
      (∀ i, (V i).Nonempty ∧ IsConnected (V i) ∧ IsOpen (V i) ∧
        Bornology.IsBounded (V i) ∧
        frontier (V i) ⊆ range b ∪ frontier U ∧
        range b ⊆ frontier (V i) ∧
        ∃ G : closure (V i) ≃ₜ closedBall (0 : ℂ) 1,
          ∀ z : closure (V i), (z : ℂ) ∈ V i ↔ (G z : ℂ) ∈ ball (0 : ℂ) 1) ∧
      Disjoint (V 0) (V 1) ∧ (V 0 ∪ V 1) = U \ range b ∧
      closure (V 0) ∩ closure (V 1) = range b ∧
      closure (V 0) ∪ closure (V 1) = closure U := by
  let v : closedBall (0 : ℂ) 1 → ℂ := Subtype.val
  let f : closedBall (0 : ℂ) 1 → ℂ := fun z ↦ (F.symm z : ℂ)
  have hf : Topology.IsClosedEmbedding f :=
    (continuous_subtype_val.comp F.symm.continuous).isClosedEmbedding
      (fun x y h ↦ F.symm.injective (Subtype.ext h))
  let L : Set ℂ → Set ℂ := fun s ↦ f '' (v ⁻¹' s)
  have hLmem (s : Set ℂ) (z : closure U) : (z : ℂ) ∈ L s ↔ (F z : ℂ) ∈ s := by
    constructor
    · rintro ⟨w, hw, he⟩
      have : F.symm w = z := Subtype.ext he
      simpa only [← this, F.apply_symm_apply] using (show (w : ℂ) ∈ s from hw)
    · intro hz
      exact ⟨F z, hz, congrArg Subtype.val (F.symm_apply_apply z)⟩
  have hLsub (s : Set ℂ) : L s ⊆ closure U := by
    rintro z ⟨w, hw, rfl⟩
    exact (F.symm w).property
  have hLmono : Monotone L := fun s t h ↦ image_mono (preimage_mono h)
  have hLunion (s t : Set ℂ) : L (s ∪ t) = L s ∪ L t := by
    simp only [L, preimage_union, image_union]
  have hLinter (s t : Set ℂ) : L (s ∩ t) = L s ∩ L t := by
    simp only [L, preimage_inter, Set.image_inter hf.injective]
  have hLdiff (s t : Set ℂ) : L (s \ t) = L s \ L t := by
    simp only [L, preimage_sdiff, Set.image_sdiff hf.injective]
  have hLcl {s : Set ℂ} (hs : s ⊆ closedBall (0 : ℂ) 1) :
      closure (L s) = L (closure s) := by
    dsimp only [L]
    rw [hf.closure_image_eq,
      Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have hv : v '' (v ⁻¹' s) = s :=
      image_preimage_eq_of_subset (by simpa only [v, Subtype.range_val] using hs)
    rw [hv]
  have hLball : L (ball (0 : ℂ) 1) = U := by
    ext z
    constructor
    · intro hz
      exact (hF ⟨z, hLsub _ hz⟩).mpr ((hLmem _ _).mp hz)
    · intro hz
      exact (hLmem _ ⟨z, subset_closure hz⟩).mpr ((hF _).mp hz)
  have hLclosed : L (closedBall (0 : ℂ) 1) = closure U := by
    rw [← closure_ball (0 : ℂ) one_ne_zero, ← hLcl ball_subset_closedBall, hLball]
  have hLsphere : L (sphere (0 : ℂ) 1) = frontier U := by
    rw [← closedBall_sdiff_ball, hLdiff, hLclosed, hLball, hU.frontier_eq]
  let g : unitInterval → closedBall (0 : ℂ) 1 :=
    fun t ↦ F ⟨b t, hbc (mem_range_self t)⟩
  have hg : Topology.IsEmbedding g :=
    F.isEmbedding.comp (hb.codRestrict _ (fun t ↦ hbc (mem_range_self t)))
  have hg0 : (g 0 : ℂ) ∈ sphere (0 : ℂ) 1 := by
    apply (hLmem _ ⟨b 0, hbc (mem_range_self 0)⟩).mp
    rwa [hLsphere]
  have hg1 : (g 1 : ℂ) ∈ sphere (0 : ℂ) 1 := by
    apply (hLmem _ ⟨b 1, hbc (mem_range_self 1)⟩).mp
    rwa [hLsphere]
  have hgi (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
      (g t : ℂ) ∈ ball (0 : ℂ) 1 := (hF _).mp (hi t ht0 ht1)
  let δ : unitInterval → ℂ := fun t ↦ (g t : ℂ)
  have hLK : L (range δ) = range b := by
    ext z
    constructor
    · rintro ⟨w, ⟨t, ht⟩, hz⟩
      have htw : g t = w := Subtype.ext ht
      refine ⟨t, ?_⟩
      rw [← htw] at hz
      simpa only [f, g, F.symm_apply_apply] using hz
    · rintro ⟨t, rfl⟩
      exact (hLmem _ ⟨b t, hbc (mem_range_self t)⟩).mpr (mem_range_self t)
  obtain ⟨W, hW, hdis, hcover, hcomp, hfront, hinter, hcharts, hext⟩ :=
    cairns_round_disk_crosscut_separation g hg hg0 hg1
      (hg.injective.ne zero_ne_one) hgi
  obtain ⟨_, _, _, _, hcut, _, _⟩ :=
    roundDiskCrosscutGeometry δ (continuous_subtype_val.comp hg.continuous) hg0 hg1 hgi
  have hcover' : W 0 ∪ W 1 = ball (0 : ℂ) 1 \ range δ := by
    rw [← hcut, ← hcover]
    ext z
    simp only [mem_union, mem_iUnion]
    constructor
    · exact fun h ↦ h.elim (fun hz ↦ ⟨0, hz⟩) (fun hz ↦ ⟨1, hz⟩)
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
  have hWsub (i : Fin 2) : W i ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hz' : z ∈ ⋃ i, W i := mem_iUnion.mpr ⟨i, hz⟩
    rw [hcover] at hz'
    exact hz'.1
  have hWcl (i : Fin 2) : closure (W i) ⊆ closedBall (0 : ℂ) 1 :=
    closure_minimal ((hWsub i).trans ball_subset_closedBall) isClosed_closedBall
  have hLopen (i : Fin 2) : IsOpen (L (W i)) := by
    let k : W i → ℂ := fun z ↦ f ⟨z, ball_subset_closedBall (hWsub i z.property)⟩
    have hr : range k = L (W i) := by
      ext z
      exact ⟨fun ⟨w, hw⟩ ↦ ⟨_, w.property, hw⟩,
        fun ⟨w, hw, hz⟩ ↦ ⟨⟨w, hw⟩, hz⟩⟩
    rw [← hr]
    apply complex_planar_open_range _ (hW i).2.2 k
    · fun_prop
    · intro x y h
      exact Subtype.ext (congrArg (fun z : closedBall (0 : ℂ) 1 ↦ (z : ℂ))
        (hf.injective h))
  have hLfront (i : Fin 2) : frontier (L (W i)) = L (frontier (W i)) := by
    rw [(hLopen i).frontier_eq, hLcl ((hWsub i).trans ball_subset_closedBall),
      ← hLdiff, (hW i).2.2.frontier_eq]
  refine ⟨fun i ↦ L (W i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hne : (L (W i)).Nonempty := by
      obtain ⟨w, hw⟩ := (hW i).1
      exact ⟨f ⟨w, ball_subset_closedBall (hWsub i hw)⟩, ⟨_, hw, rfl⟩⟩
    have hconn : IsConnected (L (W i)) := by
      apply IsConnected.image _ f hf.continuous.continuousOn
      refine ⟨?_, ?_⟩
      · obtain ⟨z, hz⟩ := (hW i).1
        exact ⟨⟨z, ball_subset_closedBall (hWsub i hz)⟩, hz⟩
      · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        rw [image_preimage_eq_of_subset (show W i ⊆ range v by
          simpa only [v, Subtype.range_val] using (hWsub i).trans ball_subset_closedBall)]
        exact (hW i).2.1.isPreconnected
    have hbdd : Bornology.IsBounded (L (W i)) :=
      (isCompact_range hf.continuous).isBounded.subset (image_subset_range _ _)
    refine ⟨hne, hconn, hLopen i, hbdd, ?_, ?_, ?_⟩
    · rw [hLfront, hfront i, hLunion, hLK]
      apply union_subset_union_right
      rw [← hLsphere]
      apply hLmono
      exact fun z hz ↦ hz.1
    · rw [hLfront, hfront i, hLunion, hLK]
      exact subset_union_left
    · obtain ⟨G, hG, _⟩ := hcharts i
      let k : closure (W i) → ℂ := fun z ↦ f ⟨z, hWcl i z.property⟩
      have hk : Topology.IsEmbedding k := hf.isEmbedding.comp
        (Topology.IsEmbedding.subtypeVal.codRestrict _ (fun z ↦ hWcl i z.property))
      have hr : range k = closure (L (W i)) := by
        rw [hLcl ((hWsub i).trans ball_subset_closedBall)]
        ext z
        exact ⟨fun ⟨w, hw⟩ ↦ ⟨_, w.property, hw⟩,
          fun ⟨w, hw, hz⟩ ↦ ⟨⟨w, hw⟩, hz⟩⟩
      let T : closure (W i) ≃ₜ closure (L (W i)) :=
        hk.toHomeomorph.trans (Homeomorph.setCongr hr)
      refine ⟨T.symm.trans G, ?_⟩
      intro z
      change (z : ℂ) ∈ L (W i) ↔ (G (T.symm z) : ℂ) ∈ ball (0 : ℂ) 1
      rw [← hG]
      have hz : (z : ℂ) = k (T.symm z) :=
        (congrArg Subtype.val (T.apply_symm_apply z)).symm
      rw [hz]
      change f _ ∈ L (W i) ↔ _
      exact hf.injective.mem_set_image
  · rw [disjoint_iff_inter_eq_empty, ← hLinter, disjoint_iff_inter_eq_empty.mp hdis]
    simp [L]
  · rw [← hLunion, hcover', hLdiff, hLball, hLK]
  · rw [hLcl ((hWsub 0).trans ball_subset_closedBall),
      hLcl ((hWsub 1).trans ball_subset_closedBall), ← hLinter, hinter, hLK]
  · have hfull : closure (W 0) ∪ closure (W 1) = closedBall (0 : ℂ) 1 := by
      apply Subset.antisymm (union_subset (hWcl 0) (hWcl 1))
      rw [← closure_ball (0 : ℂ) one_ne_zero]
      apply closure_minimal _ (isClosed_closure.union isClosed_closure)
      intro z hz
      by_cases hk : z ∈ range δ
      · left
        apply frontier_subset_closure
        rw [hfront 0]
        exact Or.inl hk
      · have hm : z ∈ W 0 ∪ W 1 := hcover'.symm ▸ ⟨hz, hk⟩
        exact hm.elim (fun h ↦ Or.inl (subset_closure h))
          (fun h ↦ Or.inr (subset_closure h))
    rw [hLcl ((hWsub 0).trans ball_subset_closedBall),
      hLcl ((hWsub 1).trans ball_subset_closedBall), ← hLunion, hfull, hLclosed]

end HolomorphicAnosov
