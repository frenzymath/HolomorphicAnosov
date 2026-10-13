import HolomorphicAnosov.Topology.CairnsGapParameter
import HolomorphicAnosov.Topology.CairnsExponentialIntervalFrontier

namespace HolomorphicAnosov.Topology.Plane.CairnsCircleGap
open Set

/-- The angular subgap cut out by two ordered parameters of a proper gap. -/
noncomputable def subgap (g : CairnsCircleGap) (l u : unitInterval) (hlu : l < u) :
    CairnsCircleGap where
  start := g.start + (g.stop - g.start) * (l : ℝ)
  stop := g.start + (g.stop - g.start) * (u : ℝ)
  start_lt_stop := by
    have hh : (l : ℝ) < u := hlu
    nlinarith [g.start_lt_stop]
  shorter_than_turn := by
    nlinarith [g.start_lt_stop, g.shorter_than_turn, l.property.1, u.property.2]

@[simp] theorem subgap_first (g : CairnsCircleGap) (l u : unitInterval) (hlu : l < u) :
    (g.subgap l u hlu).first = g.parameter l := rfl

@[simp] theorem subgap_last (g : CairnsCircleGap) (l u : unitInterval) (hlu : l < u) :
    (g.subgap l u hlu).last = g.parameter u := rfl

/-- The actual open subarc agrees with the interval between the two original
parameters, including when one parameter is an original endpoint. -/
theorem subgap_openArc (g : CairnsCircleGap) (l u : unitInterval) (hlu : l < u) :
    (g.subgap l u hlu).openArc =
      g.parameter '' {t : unitInterval | l < t ∧ t < u} := by
  have hL : 0 < g.stop - g.start := sub_pos.mpr g.start_lt_stop
  ext z
  constructor
  · rintro ⟨θ,hθ,rfl⟩
    change g.start + (g.stop - g.start) * (l : ℝ) < θ ∧
      θ < g.start + (g.stop - g.start) * (u : ℝ) at hθ
    let t : unitInterval := ⟨(θ - g.start) / (g.stop - g.start), by
      constructor
      · apply div_nonneg _ hL.le
        nlinarith [hθ.1,l.property.1]
      · apply (div_le_one hL).mpr
        nlinarith [hθ.2,u.property.2]⟩
    refine ⟨t,⟨?_,?_⟩,?_⟩
    · change (l : ℝ) < (θ - g.start) / (g.stop - g.start)
      apply (lt_div_iff₀ hL).mpr
      linarith [hθ.1]
    · change (θ - g.start) / (g.stop - g.start) < (u : ℝ)
      apply (div_lt_iff₀ hL).mpr
      linarith [hθ.2]
    · unfold parameter
      congr 1
      dsimp only [t]
      rw [mul_div_cancel₀ _ hL.ne']
      ring
  · rintro ⟨t,⟨hlt,htu⟩,rfl⟩
    refine ⟨g.start + (g.stop - g.start) * (t : ℝ),⟨?_,?_⟩,rfl⟩
    · change g.start + (g.stop - g.start) * (l : ℝ) < _
      have hlt' : (l : ℝ) < t := hlt
      nlinarith
    · change _ < g.start + (g.stop - g.start) * (u : ℝ)
      have htu' : (t : ℝ) < u := htu
      nlinarith

/-- A proper arc with retained endpoints and no retained interior point is
an actual complementary component. Its connected interior lies in one
component; that component cannot cross the arc's frontier, whose two points
are excluded from the complement. -/
theorem isGapOf_of_endpoints (g : CairnsCircleGap) (S : Set Circle)
    (hf : g.first ∈ S) (hl : g.last ∈ S) (havoid : g.openArc ⊆ Sᶜ) : g.IsGapOf S := by
  have hopen : IsOpen g.openArc :=
    isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo
  have hpre : IsPreconnected g.openArc :=
    isPreconnected_Ioo.image Circle.exp Circle.exp.continuous.continuousOn
  have hfront : frontier g.openArc ⊆ S := by
    rw [openArc, cairns_exp_interval_frontier g.start g.stop g.start_lt_stop
      g.shorter_than_turn.le]
    exact pair_subset hf hl
  obtain ⟨t,ht⟩ := nonempty_Ioo.mpr g.start_lt_stop
  let x := Circle.exp t
  have hx : x ∈ g.openArc := ⟨t,ht,rfl⟩
  refine ⟨hf,hl,x,havoid hx,Subset.antisymm ?_ ?_⟩
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hopen
      ⟨x,mem_connectedComponentIn (havoid hx),hx⟩
    rintro y ⟨hyc,hycomp⟩
    by_contra hya
    have hyfront : y ∈ frontier g.openArc := by
      rw [hopen.frontier_eq]
      exact ⟨hyc,hya⟩
    exact connectedComponentIn_subset Sᶜ x hycomp (hfront hyfront)
  · exact hpre.subset_connectedComponentIn hx havoid

/-- If all contacts lie on a proper closed arc and its endpoints are retained,
the opposite open arc is an actual complementary gap. The two closed arcs
meet only at their endpoints, which the opposite open arc excludes. -/
theorem opposite_isGapOf_of_subset_closedArc (g : CairnsCircleGap) (S : Set Circle)
    (hsub : S ⊆ g.closedArc) (hf : g.first ∈ S) (hl : g.last ∈ S) :
    ∃ gg : CairnsCircleGap, gg.IsGapOf S ∧ gg.first = g.last ∧ gg.last = g.first := by
  let gg : CairnsCircleGap := {
    start := g.stop
    stop := g.start + 2 * Real.pi
    start_lt_stop := by linarith [g.shorter_than_turn]
    shorter_than_turn := by linarith [g.start_lt_stop] }
  have hlast : gg.last = g.first := Circle.periodic_exp g.start
  refine ⟨gg,?_,rfl,hlast⟩
  apply isGapOf_of_endpoints _ _ hl (hlast.symm ▸ hf)
  intro t ht hts
  have hm := (opposite_parameter_cover_inter g gg rfl rfl rfl hlast).2
  have htG : t ∈ range g.parameter := (parameter_embedding_range g).2.1.symm ▸ hsub hts
  have htOpp : t ∈ range gg.parameter := by
    rw [(parameter_embedding_range gg).2.1]
    obtain ⟨θ,hθ,rfl⟩ := ht
    exact ⟨θ,⟨hθ.1.le,hθ.2.le⟩,rfl⟩
  have he : t = g.first ∨ t = g.last := by
    have hmem : t ∈ range g.parameter ∩ range gg.parameter := ⟨htG,htOpp⟩
    rw [hm] at hmem
    exact hmem
  obtain ⟨θ,hθ,hθt⟩ := ht
  rcases he with he | he
  · have hh : Circle.exp θ = Circle.exp gg.stop := hθt.trans (he.trans hlast.symm)
    exact hθ.2.ne (Circle.exp_injOn_Icc gg.shorter_than_turn
      ⟨hθ.1.le,hθ.2.le⟩ ⟨gg.start_lt_stop.le,le_rfl⟩ hh)
  · have hh : Circle.exp θ = Circle.exp gg.start := hθt.trans he
    exact hθ.1.ne' (Circle.exp_injOn_Icc gg.shorter_than_turn
      ⟨hθ.1.le,hθ.2.le⟩ ⟨le_rfl,gg.start_lt_stop.le⟩ hh)

/-- A closed angular arc consists of its open arc and its two endpoints. -/
theorem closedArc_subset_openArc_union_endpoints (g : CairnsCircleGap) :
    g.closedArc ⊆ g.openArc ∪ {g.first,g.last} := by
  rintro z ⟨θ,hθ,rfl⟩
  by_cases hf : θ = g.start
  · subst θ; exact Or.inr (Or.inl rfl)
  by_cases hl : θ = g.stop
  · subst θ; exact Or.inr (Or.inr rfl)
  exact Or.inl ⟨θ,⟨lt_of_le_of_ne hθ.1 (fun hh ↦ hf hh.symm),lt_of_le_of_ne hθ.2 hl⟩,rfl⟩

end HolomorphicAnosov.Topology.Plane.CairnsCircleGap
