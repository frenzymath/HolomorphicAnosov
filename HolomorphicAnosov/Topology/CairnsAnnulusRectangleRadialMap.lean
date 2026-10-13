import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Connected.PathConnected
import HolomorphicAnosov.Topology.CairnsAnnulusRectangleRadialFormula
import HolomorphicAnosov.Topology.CairnsAnnulusRectangleRadialSurjective
import HolomorphicAnosov.Topology.CairnsAnnulusRectangleFiber

/-!
# Radial map from the rectangle cylinder to the round annulus

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
preliminary 2(B), printed p.860, and the standard quotient-cylinder formula
`(t,r) ↦ r (cos(2πt), sin(2πt))`. The proposition records continuity,
surjectivity, and the exact endpoint fibers before quotient descent.
-/

open Set

namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The explicit radial map on `[0,1]×[1,2]` is a quotient presentation of the
closed round annulus: its only nontrivial fibers identify the two vertical
endpoints at equal radius. -/
theorem cairns_annulus_rectangle_radial_map :
    ∃ F : (Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) →
      {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      Continuous F ∧ Function.Surjective F ∧
        (∀ x y, F x = F y ↔
          x.1.2 = y.1.2 ∧
            (x.1.1 = y.1.1 ∨
              (x.1.1 = 0 ∧ y.1.1 = 1) ∨
              (x.1.1 = 1 ∧ y.1.1 = 0))) := by
  let f : (Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) → Plane :=
    cairns_annulus_rectangle_radial_formula
  have hnorm (x : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) :
      ‖f x‖ = x.1.2 := by
    have hsq := EuclideanSpace.norm_sq_eq (f x)
    have hsq' : ‖f x‖ ^ 2 = x.1.2 ^ 2 := by
      calc
        ‖f x‖ ^ 2 = ∑ i, ‖(f x).ofLp i‖ ^ 2 := hsq
        _ = x.1.2 ^ 2 * (Real.cos (2 * Real.pi * x.1.1) ^ 2 +
            Real.sin (2 * Real.pi * x.1.1) ^ 2) := by
          simp [f, cairns_annulus_rectangle_radial_formula, Fin.sum_univ_two, sq]
          ring_nf
        _ = x.1.2 ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    have hx : 0 ≤ x.1.2 := le_trans (by norm_num) x.2.2.1
    nlinarith [norm_nonneg (f x)]
  let F : (Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2) →
      {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    fun x => ⟨f x, by
      change 1 ≤ ‖f x‖ ∧ ‖f x‖ ≤ 2
      rw [hnorm]
      exact ⟨x.2.2.1, x.2.2.2⟩⟩
  have hcont : Continuous F := by
    apply Continuous.subtype_mk
    change Continuous (fun x : Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2 =>
      cairns_annulus_rectangle_radial_formula x)
    unfold cairns_annulus_rectangle_radial_formula
    fun_prop
  refine ⟨F, hcont, ?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := cairns_annulus_rectangle_radial_formula_surjective z
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  · intro x y
    constructor
    · intro h
      exact (cairns_annulus_rectangle_radial_formula_fiber x y).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((cairns_annulus_rectangle_radial_formula_fiber x y).mpr h)

end HolomorphicAnosov.Topology

