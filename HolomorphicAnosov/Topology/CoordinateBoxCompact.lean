import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

namespace HolomorphicAnosov
open Set Topology _root_.Topology

/-- Every finite-dimensional closed coordinate box is compact.

Source: Hatcher, *Algebraic Topology*, Appendix A.2 and A.7, pp.521 and
525--526.  The selected dyadic cells and all of their coordinate faces are
closed boxes in the original Euclidean topology.  This reusable leaf records
the finite-product compactness argument for arbitrary ordered corners; it does
not assert any CW structure or cell selection.
-/
theorem coordinate_box_compact {N : ℕ} {a b : Fin N → ℝ}
    (_hab : ∀ j, a j ≤ b j) :
    IsCompact {x : EuclideanSpace ℝ (Fin N) | ∀ j, a j ≤ x j ∧ x j ≤ b j} := by
  let e := EuclideanSpace.equiv (Fin N) ℝ
  let B : Set (Fin N → ℝ) := Set.Icc a b
  have hB : IsCompact B := by
    dsimp [B]
    rw [← pi_univ_Icc]
    exact isCompact_univ_pi fun j ↦
      ConditionallyCompleteLinearOrder.isCompact_Icc (a j) (b j)
  have hmap : IsCompact (e.symm '' B) := hB.image e.symm.continuous
  have heq : (e.symm : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) '' B =
      {x : EuclideanSpace ℝ (Fin N) | ∀ j, a j ≤ x j ∧ x j ≤ b j} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp [B] at hy
      rw [← pi_univ_Icc] at hy
      change ∀ j, a j ≤ y j ∧ y j ≤ b j
      simpa only [Set.mem_univ_pi, Set.mem_Icc] using hy
    · intro hx
      have hx' : e x ∈ B := by
        dsimp [B]
        rw [← pi_univ_Icc]
        apply Set.mem_univ_pi.mpr
        intro j
        apply Set.mem_Icc.mpr
        exact hx j
      exact ⟨e x, hx', e.symm_apply_apply x⟩
  rw [← heq]
  exact hmap

end HolomorphicAnosov
