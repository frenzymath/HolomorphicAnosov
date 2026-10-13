import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.BoundedRepresentativeStructure

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
/-- Structural obligation for the little-o submodule, HPS p. 27.
For sums use epsilon/2 for each term and intersect the eventual sets. For a
nonzero scalar use epsilon/|a| and `norm_smul`; a zero scalar gives the zero
map. These estimates also hold on the bottom punctured filter. -/
theorem littleORepresentative_submodule_axioms :
    IsLittleORepresentative X Y (0 : BoundedRepresentative X Y) ∧
    (∀ q r : BoundedRepresentative X Y, IsLittleORepresentative X Y q →
      IsLittleORepresentative X Y r → IsLittleORepresentative X Y (q + r)) ∧
    (∀ (a : ℝ) (q : BoundedRepresentative X Y), IsLittleORepresentative X Y q →
      IsLittleORepresentative X Y (a • q)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    exact Filter.Eventually.of_forall fun x ↦ by
      change ‖(0 : Y)‖ ≤ ε * ‖x‖
      simpa only [norm_zero] using mul_nonneg hε.le (norm_nonneg x)
  · intro q r hq hr ε hε
    filter_upwards [hq (ε / 2) (by positivity), hr (ε / 2) (by positivity)] with x hx hy
    change ‖(q : X → Y) x + (r : X → Y) x‖ ≤ _
    exact (norm_add_le _ _).trans (by nlinarith)
  · intro a q hq ε hε
    by_cases ha : a = 0
    · subst a
      exact Filter.Eventually.of_forall fun x ↦ by
        change ‖(0 : ℝ) • (q : X → Y) x‖ ≤ ε * ‖x‖
        simp [mul_nonneg hε.le (norm_nonneg x)]
    · have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
      filter_upwards [hq (ε / ‖a‖) (div_pos hε hapos)] with x hx
      change ‖a • (q : X → Y) x‖ ≤ _
      rw [norm_smul]
      calc
        _ ≤ ‖a‖ * ((ε / ‖a‖) * ‖x‖) := mul_le_mul_of_nonneg_left hx hapos.le
        _ = _ := by field_simp

/-- The little-o submodule inside the bounded representatives, HPS pp. 26–27. -/
def littleORepresentatives (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : Submodule ℝ (BoundedRepresentative X Y) where
  carrier := {q | IsLittleORepresentative X Y q}
  zero_mem' := (littleORepresentative_submodule_axioms X Y).1
  add_mem' := fun hq hr => (littleORepresentative_submodule_axioms X Y).2.1 _ _ hq hr
  smul_mem' := fun a _ hq => (littleORepresentative_submodule_axioms X Y).2.2 a _ hq

/-- HPS's entire bounded-jet quotient J_b, before assigning its norm. -/
abbrev BoundedJet := BoundedRepresentative X Y ⧸ littleORepresentatives X Y

/-- The class of a bounded representative, HPS pp. 26–27. -/
def jetClass (q : BoundedRepresentative X Y) : BoundedJet X Y :=
  Submodule.Quotient.mk q


end HolomorphicAnosov.BoundedLipschitzJets

