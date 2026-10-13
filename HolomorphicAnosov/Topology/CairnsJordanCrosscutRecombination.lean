import HolomorphicAnosov.Topology.CairnsSimplePolygonSchoenflies
import HolomorphicAnosov.Topology.CairnsDiskChartCrosscut
import HolomorphicAnosov.Topology.CircleEmbeddingSurjective
import HolomorphicAnosov.Topology.DiskChartExterior

open Set Metric
namespace HolomorphicAnosov

/-!
# Cairns Section 5 crosscut recombination

Source: S. S. Cairns, *An Elementary Proof of the Jordan–Schoenflies Theorem*
(1951), §5, printed pp. 866–867, with the polygon and two crosscut constructions
using preliminary §2(A,B), p. 860 and Lemma 5.1, p. 866.

The polygon chart transports the two arcs of the embedded circle to crosscuts.
The first cut has two disk cells, and the connected interior of the second arc
lies in one of them. Cut that cell again. The connected interior of the first
arc lies in one of the second pair of closed cells, because it avoids their
intersection, which is the second arc. Density adjoins its endpoints, so that
cell frontier contains the whole original circle. Its disk chart makes its
frontier another embedded circle. The two-arc surjectivity argument identifies
the two circles exactly. The exterior of this closed cell is connected by the
independent Hatcher disk-complement theorem; the open-image theorem makes the
cell regular open, hence gives the identical exterior frontier. Compactness
makes the inner cell bounded and forces its complement to be unbounded.

The two-cut construction follows Cairns. The nested-circle equality and the
Hatcher exterior shortcut are agent-written replacements of the final explicit
three-cell recombination. No arbitrary Jordan separation theorem is used.
-/

/-- Two successive crosscuts produce the Jordan regions for an embedded circle
inside an extreme-contact polygon. Source and complete proof: the module
account above, Cairns (1951), §5 pp.866–867, with independent Hatcher
Proposition 2B.1(a) and Theorem 2B.3 for the exterior. -/
theorem cairns_jordan_crosscut_recombination
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    {n : ℕ} (p : Polygon ℂ (n + 1)) (P₁ P₂ : ℂ)
    (hp : IsSimpleClosedPolygon p)
    (hP₁ : P₁ ∈ Set.range γ) (hP₂ : P₂ ∈ Set.range γ) (hP₁₂ : P₁ ≠ P₂)
    (hB : ∃ B : Set ℂ, Bornology.IsBounded B ∧ IsConnected B ∧ IsOpen B ∧
      (∃ z : ℂ, B = connectedComponentIn (p.boundary ℝ)ᶜ z) ∧
      Set.range γ \ {P₁, P₂} ⊆ B)
    (hcontact : p.boundary ℝ ∩ Set.range γ = {P₁, P₂}) :
    ∃ Q E : Set ℂ,
      Q.Nonempty ∧ E.Nonempty ∧
      IsConnected Q ∧ IsConnected E ∧ IsOpen Q ∧ IsOpen E ∧
      Bornology.IsBounded Q ∧ ¬ Bornology.IsBounded E ∧
      Q ∪ E = (Set.range γ)ᶜ ∧ Disjoint Q E ∧
      frontier Q = Set.range γ ∧ frontier E = Set.range γ := by
  obtain ⟨u, v, hu, hv, huv, e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃,
      hcover, hmeet⟩ :=
    Topology.circle_split_two_arcs γ hγ P₁ P₂ hP₁ hP₂ hP₁₂
  have hpoly := cairns_simple_polygon_schoenflies p hp
  rcases hpoly with ⟨D, O, hDne, hOne, hDneq, hDunion, hDdis, hDcomp,
    hDconn, hOconn, hDopen, hOopen, hDb, hOb, hDfront, hOfront, hDcl,
    hDhomeo, hDboundary, hDcross, hDdelete⟩
  obtain ⟨B, hBb, hBc, hBo, ⟨z, hBz⟩, hBsub⟩ := hB
  let tmid : unitInterval := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have htmid : e₂ tmid ∈ Set.range γ \ {P₁, P₂} := by
    rw [← hcover]
    refine ⟨Or.inl (mem_range_self tmid), ?_⟩
    intro ht
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · have heq := he₂.injective (ht.trans h0₂.symm)
      have hv := congrArg (fun s : unitInterval ↦ (s : ℝ)) heq
      norm_num [tmid] at hv
    · have heq := he₂.injective ((Set.mem_singleton_iff.mp ht).trans h1₂.symm)
      have hv := congrArg (fun s : unitInterval ↦ (s : ℝ)) heq
      norm_num [tmid] at hv
  have hBne : B.Nonempty := by
    exact ⟨e₂ tmid, hBsub htmid⟩
  have hzcomp : z ∈ (p.boundary ℝ)ᶜ := by
    by_contra hz
    rw [hBz, connectedComponentIn_eq_empty hz] at hBb
    exact hBne.ne_empty (hBz.trans (connectedComponentIn_eq_empty hz))
  have hBmem : B ∈ ({D, O} : Set (Set ℂ)) := by
    rw [← hDcomp]
    exact ⟨z, hzcomp, hBz.symm⟩
  have hBD : B = D := by
    rcases Set.mem_insert_iff.mp hBmem with h | h
    · exact h
    · have hBO : B = O := Set.mem_singleton_iff.mp h
      exact False.elim (hOb (hBO ▸ hBb))
  have hγD : Set.range γ \ {P₁, P₂} ⊆ D := by
    intro x hx
    exact hBD ▸ hBsub hx
  have he₂D : ∀ t : unitInterval, (t : ℝ) ≠ 0 → (t : ℝ) ≠ 1 → e₂ t ∈ D := by
    intro t ht0 ht1
    apply hγD
    refine ⟨?_, ?_⟩
    · exact hcover ▸ Or.inl ⟨t, rfl⟩
    · intro h
      rcases Set.mem_insert_iff.mp h with h | h
      · exact ht0 (by
          have heq := he₂.injective (h.trans h0₂.symm)
          exact congrArg (fun s : unitInterval ↦ (s : ℝ)) heq)
      · exact ht1 (by
          have heq := he₂.injective ((Set.mem_singleton_iff.mp h).trans h1₂.symm)
          exact congrArg (fun s : unitInterval ↦ (s : ℝ)) heq)
  have hP₁bd : P₁ ∈ p.boundary ℝ := by
    have hm : P₁ ∈ p.boundary ℝ ∩ Set.range γ := by
      rw [hcontact]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    exact hm.1
  have hP₂bd : P₂ ∈ p.boundary ℝ := by
    have hm : P₂ ∈ p.boundary ℝ ∩ Set.range γ := by
      rw [hcontact]
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton P₂))
    exact hm.1
  have he₂cl (t : unitInterval) : e₂ t ∈ closure D := by
    rw [hDcl]
    by_cases ht0 : (t : ℝ) = 0
    · right
      have ht : t = 0 := Subtype.ext ht0
      rw [ht, h0₂]
      exact hP₁bd
    by_cases ht1 : (t : ℝ) = 1
    · right
      have ht : t = 1 := Subtype.ext ht1
      rw [ht, h1₂]
      exact hP₂bd
    · exact Or.inl (he₂D t ht0 ht1)
  obtain ⟨H, hHp⟩ := hDhomeo
  have hDcomponent : ∃ z : ℂ, z ∈ (p.boundary ℝ)ᶜ ∧
      D = connectedComponentIn (p.boundary ℝ)ᶜ z := by
    obtain ⟨x, hx⟩ := hDne
    have hxc : x ∈ (p.boundary ℝ)ᶜ := by
      rw [← hDunion]
      exact Or.inl hx
    have hm : connectedComponentIn (p.boundary ℝ)ᶜ x ∈ ({D, O} : Set (Set ℂ)) := by
      rw [← hDcomp]
      exact ⟨x, hxc, rfl⟩
    rcases Set.mem_insert_iff.mp hm with hm | hm
    · exact ⟨x, hxc, hm.symm⟩
    · have hm' : connectedComponentIn (p.boundary ℝ)ᶜ x = O :=
        Set.mem_singleton_iff.mp hm
      exfalso
      exact (Set.disjoint_left.mp hDdis) hx (hm' ▸ mem_connectedComponentIn hxc)
  have hclb : Bornology.IsBounded (closure D) := by
    rw [hDcl]
    exact hDb.union p.isCompact_boundary.isBounded
  have hDcompact : IsCompact (closure D) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hclb⟩
  have hHDbounded : Bornology.IsBounded (H '' D) :=
    (hDcompact.image H.continuous).isBounded.subset (Set.image_mono subset_closure)
  have hExt : ¬ Bornology.IsBounded ((closedBall (0 : ℂ) 1)ᶜ) := by
    intro hE
    apply NormedSpace.unbounded_univ ℝ ℂ
    have hb := (isCompact_closedBall (0 : ℂ) 1).isBounded.union hE
    have hall : closedBall (0 : ℂ) 1 ∪ (closedBall (0 : ℂ) 1)ᶜ = (Set.univ : Set ℂ) := by
      simp
    rwa [hall] at hb
  have hHD : H '' D = ball (0 : ℂ) 1 := by
    obtain ⟨z, hzc, hz⟩ := hDcomponent
    have himage : H '' (p.boundary ℝ)ᶜ = (sphere (0 : ℂ) 1)ᶜ := by
      rw [H.image_compl, hHp]
    have hcomp : H '' D = connectedComponentIn (sphere (0 : ℂ) 1)ᶜ (H z) := by
      rw [hz, H.image_connectedComponentIn hzc, himage]
    have hm : connectedComponentIn (sphere (0 : ℂ) 1)ᶜ (H z) ∈
        ({ball (0 : ℂ) 1, (closedBall (0 : ℂ) 1)ᶜ} : Set (Set ℂ)) := by
      have hcircle := circle_complement_regions
      dsimp at hcircle
      rcases hcircle with ⟨_, _, _, _, _, _, hcomponents, _, _, _⟩
      rw [← hcomponents]
      exact ⟨H z, by simpa [← himage] using hzc, rfl⟩
    rcases Set.mem_insert_iff.mp hm with hm | hm
    · exact hcomp.trans hm
    · exfalso
      have hm' : connectedComponentIn (sphere (0 : ℂ) 1)ᶜ (H z) =
          (closedBall (0 : ℂ) 1)ᶜ := Set.mem_singleton_iff.mp hm
      exact hExt (hm' ▸ hcomp ▸ hHDbounded)
  have hHDcl : H '' closure D = closedBall (0 : ℂ) 1 := by
    rw [H.image_closure, hHD, closure_ball (0 : ℂ) one_ne_zero]
  let F : closure D ≃ₜ closedBall (0 : ℂ) 1 :=
    H.subtype (fun z ↦ by rw [← hHDcl]; exact H.injective.mem_set_image.symm)
  have hF (z : closure D) : (z : ℂ) ∈ D ↔ (F z : ℂ) ∈ ball (0 : ℂ) 1 := by
    change (z : ℂ) ∈ D ↔ H (z : ℂ) ∈ ball (0 : ℂ) 1
    rw [← hHD]
    exact H.injective.mem_set_image.symm
  have hclarc (a : unitInterval → ℂ) (ha : Topology.IsEmbedding a) :
      closure (a '' Ioo 0 1) = range a := by
    rw [(ha.continuous.isClosedEmbedding ha.injective).closure_image_eq]
    have hI : closure (Ioo (0 : unitInterval) 1) = univ := by
      rw [closure_Ioo zero_ne_one]
      ext t
      simp only [mem_Icc, mem_univ, iff_true]
      exact ⟨t.property.1, t.property.2⟩
    rw [hI, image_univ]
  have hηin (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
      e₂ t ∈ D := he₂D t (ne_of_gt ht0) (ne_of_lt ht1)
  obtain ⟨V, hV, hVdis, hVcover, hVmeet, hVclcover⟩ :=
    cairns_disk_chart_crosscut D hDopen F hF e₂ he₂
      (by rintro z ⟨t, rfl⟩; exact he₂cl t)
      (hDfront.symm ▸ hP₁bd |> fun h ↦ h0₂.symm ▸ h)
      (hDfront.symm ▸ hP₂bd |> fun h ↦ h1₂.symm ▸ h) hηin
  let S₂ := e₂ '' Ioo (0 : unitInterval) 1
  let S₃ := e₃ '' Ioo (0 : unitInterval) 1
  have hS₃ : S₃ ⊆ D \ range e₂ := by
    rintro z ⟨t, ht, rfl⟩
    have hnotends : e₃ t ∉ ({P₁, P₂} : Set ℂ) := by
      intro h
      rcases h with h | h
      · exact ht.2.ne (he₃.injective (h.trans h1₃.symm))
      · exact ht.1.ne' (he₃.injective (h.trans h0₃.symm))
    refine ⟨hγD ⟨hcover ▸ Or.inr (mem_range_self t), hnotends⟩, ?_⟩
    intro h
    exact hnotends (hmeet ▸ ⟨h, mem_range_self t⟩)
  have hS₃conn : IsPreconnected S₃ :=
    isPreconnected_Ioo.image e₃ he₃.continuous.continuousOn
  have hS₃cover : S₃ ⊆ V 0 ∪ V 1 := hVcover.symm ▸ hS₃
  have hVi : ∃ i : Fin 2, S₃ ⊆ V i := by
    rcases hS₃conn.subset_or_subset (hV 0).2.2.1 (hV 1).2.2.1 hVdis hS₃cover with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hVi
  have hVsub (j : Fin 2) : V j ⊆ D \ range e₂ := by
    intro z hz
    apply hVcover ▸ (show z ∈ V 0 ∪ V 1 from ?_)
    fin_cases j
    · exact Or.inl hz
    · exact Or.inr hz
  have he₃cl : range e₃ ⊆ closure (V i) := by
    rw [← hclarc e₃ he₃]
    exact closure_mono hi
  have he₃0 : e₃ 0 ∈ frontier (V i) := by
    rw [h0₃, ← h1₂]
    exact (hV i).2.2.2.2.2.1 (mem_range_self 1)
  have he₃1 : e₃ 1 ∈ frontier (V i) := by
    rw [h1₃, ← h0₂]
    exact (hV i).2.2.2.2.2.1 (mem_range_self 0)
  obtain ⟨G, hG⟩ := (hV i).2.2.2.2.2.2
  obtain ⟨W, hW, hWdis, hWcover, hWmeet, hWclcover⟩ :=
    cairns_disk_chart_crosscut (V i) (hV i).2.2.1 G hG e₃ he₃ he₃cl he₃0 he₃1
      (fun t ht0 ht1 ↦ hi ⟨t, ⟨ht0, ht1⟩, rfl⟩)
  have hS₂cl : S₂ ⊆ closure (W 0) ∪ closure (W 1) := by
    rw [hWclcover]
    exact (image_subset_range _ _).trans
      ((hV i).2.2.2.2.2.1.trans frontier_subset_closure)
  have hS₂avoid : S₂ ∩ (closure (W 0) ∩ closure (W 1)) = ∅ := by
    rw [hWmeet]
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨⟨t, ht, rfl⟩, hz⟩
    have hm : e₂ t ∈ ({P₁, P₂} : Set ℂ) := hmeet ▸ ⟨mem_range_self t, hz⟩
    rcases hm with hm | hm
    · exact ht.1.ne' (he₂.injective (hm.trans h0₂.symm))
    · exact ht.2.ne (he₂.injective (hm.trans h1₂.symm))
  have hS₂conn : IsPreconnected S₂ :=
    isPreconnected_Ioo.image e₂ he₂.continuous.continuousOn
  have hWj : ∃ j : Fin 2, S₂ ⊆ closure (W j) := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS₂conn
      (closure (W 0)) (closure (W 1)) isClosed_closure isClosed_closure hS₂cl hS₂avoid with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨j, hj⟩ := hWj
  have hWsub (k : Fin 2) : W k ⊆ V i \ range e₃ := by
    intro z hz
    apply hWcover ▸ (show z ∈ W 0 ∪ W 1 from ?_)
    fin_cases k
    · exact Or.inl hz
    · exact Or.inr hz
  have he₂W : range e₂ ⊆ frontier (W j) := by
    have hcl : range e₂ ⊆ closure (W j) := by
      rw [← hclarc e₂ he₂]
      exact closure_minimal hj isClosed_closure
    intro z hz
    rw [(hW j).2.2.1.frontier_eq]
    exact ⟨hcl hz, fun h ↦ (hVsub i (hWsub j h).1).2 hz⟩
  have hΓW : range γ ⊆ frontier (W j) := by
    rw [← hcover]
    exact union_subset he₂W (hW j).2.2.2.2.2.1
  obtain ⟨J, hJ⟩ := (hW j).2.2.2.2.2.2
  have hboundary (z : closure (W j)) :
      (z : ℂ) ∈ frontier (W j) ↔ (J z : ℂ) ∈ sphere (0 : ℂ) 1 := by
    rw [(hW j).2.2.1.frontier_eq]
    simp only [mem_sdiff, z.property, true_and, hJ]
    have hz := (J z).property
    simp only [mem_ball, mem_sphere, mem_closedBall] at hz ⊢
    exact ⟨fun h ↦ le_antisymm hz (not_lt.mp h), fun h ↦ by rw [h]; exact lt_irrefl _⟩
  have hJimage (A B : Set ℂ) (hAB : ∀ z : closure (W j), (z : ℂ) ∈ A ↔ (J z : ℂ) ∈ B) :
      J '' {z : closure (W j) | (z : ℂ) ∈ A} =
        {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ B} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hAB z).mp hz
    · intro hw
      exact ⟨J.symm w, (hAB _).mpr (by simpa using hw), J.apply_symm_apply w⟩
  obtain ⟨_, β, hβ, hrβ⟩ := disk_chart_open_interior_boundary
    (closure (W j)) (W j) (frontier (W j)) subset_closure frontier_subset_closure J
    (hJimage _ _ hJ) (hJimage _ _ hboundary)
  have hfront : frontier (W j) = range γ := by
    rw [← hrβ]
    exact (Topology.embedded_circle_range_eq γ β hγ hβ (hrβ.symm ▸ hΓW)).symm
  obtain ⟨hEconn, hEbound, hEfront⟩ := disk_chart_exterior (W j) (hW j).2.2.1 J hJ
  refine ⟨W j, (closure (W j))ᶜ, (hW j).1, hEconn.nonempty,
    (hW j).2.1, hEconn, (hW j).2.2.1, isClosed_closure.isOpen_compl,
    (hW j).2.2.2.1, hEbound, ?_, ?_, hfront, hEfront.trans hfront⟩
  · rw [← hfront, (hW j).2.2.1.frontier_eq]
    ext z
    simp only [mem_union, mem_compl_iff, mem_sdiff]
    have hz : z ∈ W j → z ∈ closure (W j) := fun h ↦ subset_closure h
    tauto
  · exact disjoint_compl_right.mono_left subset_closure

end HolomorphicAnosov
