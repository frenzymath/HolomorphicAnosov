import Mathlib.Topology.MetricSpace.Contracting

/-!
# Unique intersection of two quarter-Lipschitz graph maps

This file proves the unique-intersection statement for two quarter-Lipschitz graph maps on a complete invariant subset (Fisher–Hasselblatt, Lemma 12.5.18).
-/

open Set

namespace HolomorphicAnosov.Ghys

/-- Two quarter-Lipschitz graph maps whose composition preserves a nonempty complete set have a unique common fixed point in that set (Fisher–Hasselblatt, Lemma 12.5.18). -/
theorem surface_graph_intersection_of_quarter_lipschitz
    {E F : Type*} [MetricSpace E] [MetricSpace F]
    (D : Set E) (hD : IsComplete D) (hD0 : D.Nonempty)
    (U : E → F) (S : F → E)
    (hmap : ∀ x ∈ D, S (U x) ∈ D)
    (hU : ∀ x ∈ D, ∀ y ∈ D,
      dist (U x) (U y) ≤ (1 / 4 : ℝ) * dist x y)
    (hS : ∀ x ∈ D, ∀ y ∈ D,
      dist (S (U x)) (S (U y)) ≤ (1 / 4 : ℝ) * dist (U x) (U y)) :
    ∃! x : E, x ∈ D ∧ x = S (U x) := by
  let inst : CompleteSpace D := hD.completeSpace_coe
  let T : D → D := fun x => ⟨S (U x), hmap x x.property⟩
  have hT : ContractingWith (⟨1 / 16, by norm_num⟩ : NNReal) T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
    · change (1 / 16 : NNReal) < 1
      norm_num
    intro x y
    change dist (S (U x.val)) (S (U y.val)) ≤
      (1 / 16 : ℝ) * dist x.val y.val
    calc
      dist (S (U x.val)) (S (U y.val)) ≤
          (1 / 4 : ℝ) * dist (U x.val) (U y.val) :=
        hS x.val x.property y.val y.property
      _ ≤ (1 / 4 : ℝ) * ((1 / 4 : ℝ) * dist x.val y.val) :=
        mul_le_mul_of_nonneg_left (hU x.val x.property y.val y.property) (by norm_num)
      _ = (1 / 16 : ℝ) * dist x.val y.val := by ring
  obtain ⟨x, hx, _, _⟩ :=
    hT.exists_fixedPoint (⟨hD0.choose, hD0.choose_spec⟩ : D) (edist_ne_top _ _)
  refine ⟨x.val, ⟨x.property, ?_⟩, ?_⟩
  · exact (congrArg Subtype.val hx.eq).symm
  · intro y hy
    have hyT : Function.IsFixedPt T (⟨y, hy.1⟩ : D) := by
      exact Subtype.ext hy.2.symm
    exact congrArg Subtype.val (hT.fixedPoint_unique' hyT hx)

end HolomorphicAnosov.Ghys
