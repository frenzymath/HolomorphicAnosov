import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import HolomorphicAnosov.Topology.CairnsGapParameter

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-!
# Cairns residual-sector invariant for actual recurrence stages

Source: Cairns (1951), §4(B,C), printed pp.863–865, equations (4.3),(4.4)
and recurrent Hypothesis (1)–(5).

The earlier arbitrary-stage statement was false: take the standard unit circle,
its bounded complementary component a = ball 0 1, and the filled stage region
ball 0 (1/2). Its closure misses the circle, so its contact set is empty. The
whole circle is then a residual component, whereas a proper gap must have its
endpoints in the contact set. Nonemptiness, openness and inclusion in a alone
therefore cannot imply the asserted invariant.

This corrected statement concerns an actual recurrence and assumes that its
successor region is contained in a. It does not construct the recurrence.
-/

/-- For a recorded recurrence step, retain its chosen gap and outside sector.
Parametrize the opposite angular interval [stop, start + 2π] in reverse to
obtain the complementary arc with the same endpoint order. The two proper
intervals cover one turn and intersect at their endpoints, giving the asserted
circle cover and overlap. Equation (4.3) puts each old open chord into the next
region, so successor inclusion puts it in a. The recorded star choice and
outside condition give the component witness, frontier bound and disjointness.
Source: Cairns (1951), §4(C), pp.864–865. -/
theorem cairns_residual_sector_invariant
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle} {h : (range σ) ≃ₜ Circle}
    (d : Data σ a p q h) (j : ℕ) (hnext : (d.stages (j + 1)).region ⊆ a) :
    ∀ i : ResidualComponent ((d.stages j).contacts σ),
      ∃ (g : CairnsCircleGap) (α' : I → Circle) (β : Set ℂ),
        g.IsGapOf ((d.stages j).contacts σ) ∧ g.openArc = i.val ∧
        Topology.IsEmbedding α' ∧
        α' ⟨0, by simp⟩ = g.first ∧ α' ⟨1, by simp⟩ = g.last ∧
        range g.parameter ∪ range α' = univ ∧
        range g.parameter ∩ range α' = {g.first, g.last} ∧
        openSegment ℝ (σ g.first) (σ g.last) ⊆ a ∧
        (∃ x ∈ a \ openSegment ℝ (σ g.first) (σ g.last),
          connectedComponentIn (a \ openSegment ℝ (σ g.first) (σ g.last)) x = β) ∧
        frontier β ⊆ segment ℝ (σ g.first) (σ g.last) ∪ σ '' g.closedArc ∧
        Disjoint β (d.stages j).region := by
  intro i
  let g := (d.steps j).gap i
  let g' : CairnsCircleGap :=
    { start := g.stop
      stop := g.start + 2 * Real.pi
      start_lt_stop := by linarith [g.shorter_than_turn]
      shorter_than_turn := by linarith [g.start_lt_stop] }
  have hfirst : g'.first = g.last := rfl
  have hlast : g'.last = g.first := Circle.periodic_exp g.start
  obtain ⟨_, hemb, _, _, hzero, hone, hcover, hinter⟩ :=
    CairnsCircleGap.opposite_parameter_chord_arc_data g g' rfl rfl hfirst hlast
  refine ⟨g, (fun t ↦ g'.parameter (unitInterval.symm t)),
    ((d.steps j).star i).sector, (d.steps j).gap_isGap i, (d.steps j).gap_arc i,
    hemb, hzero, hone, hcover, hinter, ?_, ((d.steps j).star i).component,
    ((d.steps j).star i).frontier_subset, (d.steps j).outside i⟩
  intro z hz
  apply hnext
  rw [d.next_eq j]
  exact Or.inr (mem_iUnion.mpr ⟨i, Or.inr hz⟩)

end HolomorphicAnosov.Topology.Plane

