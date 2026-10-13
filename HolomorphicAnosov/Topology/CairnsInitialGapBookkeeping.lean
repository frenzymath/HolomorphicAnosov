import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap

namespace HolomorphicAnosov.Topology.Plane

open Set

/-!
# Initial opposite-gap bookkeeping

Source: Cairns (1951), §3(D,E), pp.862–863.  Once the prescribed chord
endpoints are represented by real lifts of the parameter circle, the two
oriented arcs are complementary and their lift endpoints satisfy the displayed
full-turn equations.  This bookkeeping is independent of the first-contact
sector geometry.

DAG node: topo.cairns_initial_gap_bookkeeping_g20.
-/
theorem cairns_initial_gap_bookkeeping_source_obligation
    (p q : Circle) (hpq : p ≠ q) :
    ∃ g₁ g₂ : CairnsCircleGap,
      g₁.first = p ∧ g₁.last = q ∧
      g₂.first = q ∧ g₂.last = p ∧
      g₂.start = g₁.stop ∧ g₂.stop = g₁.start + 2 * Real.pi := by
  let x : ℝ := (p : ℂ).arg
  let y : ℝ := (q : ℂ).arg
  have hxlo : -Real.pi < x := by
    simpa [x] using (Complex.arg_mem_Ioc (p : ℂ)).1
  have hxhi : x ≤ Real.pi := by
    simpa [x] using (Complex.arg_mem_Ioc (p : ℂ)).2
  have hylo : -Real.pi < y := by
    simpa [y] using (Complex.arg_mem_Ioc (q : ℂ)).1
  have hyhi : y ≤ Real.pi := by
    simpa [y] using (Complex.arg_mem_Ioc (q : ℂ)).2
  have hxy : x ≠ y := by
    intro hxy
    apply hpq
    have hp : Circle.exp x = p := by simp [x]
    have hq : Circle.exp y = q := by simp [y]
    exact hp.symm.trans (by rw [hxy]; exact hq)
  by_cases hxylt : x < y
  · let g₁ : CairnsCircleGap :=
      { start := x, stop := y, start_lt_stop := hxylt,
        shorter_than_turn := by
          linarith [Real.pi_pos] }
    let g₂ : CairnsCircleGap :=
      { start := y, stop := x + 2 * Real.pi, start_lt_stop := by linarith,
        shorter_than_turn := by
          linarith [Real.pi_pos] }
    refine ⟨g₁, g₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp [g₁, CairnsCircleGap.first, x]
    · simp [g₁, CairnsCircleGap.last, y]
    · simp [g₂, CairnsCircleGap.first, y]
    · have hp : Circle.exp (x + 2 * Real.pi) = Circle.exp x := by
        simp
      have hxexp : Circle.exp x = p := by simp [x]
      simp [g₂, CairnsCircleGap.last, x]
    · simp [g₁, g₂]
  · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxylt) (Ne.symm hxy)
    let g₁ : CairnsCircleGap :=
      { start := x, stop := y + 2 * Real.pi, start_lt_stop := by linarith,
        shorter_than_turn := by
          linarith [Real.pi_pos] }
    let g₂ : CairnsCircleGap :=
      { start := y + 2 * Real.pi, stop := x + 2 * Real.pi, start_lt_stop := by linarith,
        shorter_than_turn := by
          linarith [Real.pi_pos] }
    refine ⟨g₁, g₂, ?_, ?_, ?_, ?_, ?_⟩
    · have hp : Circle.exp x = p := by simp [x]
      simp [g₁, CairnsCircleGap.first, x]
    · have hqexp : Circle.exp (y + 2 * Real.pi) = Circle.exp y := by
        simp
      have hq : Circle.exp y = q := by simp [y]
      simp [g₁, CairnsCircleGap.last, y]
    · have hqexp : Circle.exp (y + 2 * Real.pi) = Circle.exp y := by
        simp
      have hq : Circle.exp y = q := by simp [y]
      simp [g₂, CairnsCircleGap.first, y]
    · have hpexp : Circle.exp (x + 2 * Real.pi) = Circle.exp x := by
        simp
      have hp : Circle.exp x = p := by simp [x]
      simp [g₂, CairnsCircleGap.last, x]
    · simp [g₁, g₂]

end HolomorphicAnosov.Topology.Plane
