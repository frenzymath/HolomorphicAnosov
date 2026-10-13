import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.RepresentativePredicates

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
/-- Structural obligation for the bounded-representative submodule, HPS p. 27.
The zero map has bound zero. For addition intersect the two eventual sets and
use the norm triangle inequality, with bound C+D. For scalar multiplication
use `norm_smul` and bound |a|C. Zero values are preserved in each operation. -/
theorem boundedRepresentative_submodule_axioms :
    IsBoundedRepresentative X Y 0 ∧
    (∀ q r : X → Y, IsBoundedRepresentative X Y q →
      IsBoundedRepresentative X Y r → IsBoundedRepresentative X Y (q + r)) ∧
    (∀ (a : ℝ) (q : X → Y), IsBoundedRepresentative X Y q →
      IsBoundedRepresentative X Y (a • q)) := by
  refine ⟨⟨rfl, 0, le_rfl, ?_⟩, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x ↦ by simp
  · intro q r hq hr
    obtain ⟨hq0, C, hC, hq⟩ := hq
    obtain ⟨hr0, D, hD, hr⟩ := hr
    refine ⟨by simp [hq0, hr0], C + D, add_nonneg hC hD, ?_⟩
    filter_upwards [hq, hr] with x hx hy
    exact (norm_add_le _ _).trans (by simpa [add_mul] using add_le_add hx hy)
  · intro a q hq
    obtain ⟨hq0, C, hC, hq⟩ := hq
    refine ⟨by simp [hq0], ‖a‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    filter_upwards [hq] with x hx
    simpa only [Pi.smul_apply, norm_smul, mul_assoc] using
      mul_le_mul_of_nonneg_left hx (norm_nonneg a)

/-- The actual pointwise linear subspace of bounded representatives, HPS p. 27. -/
def boundedRepresentatives : Submodule ℝ (X → Y) where
  carrier := {q | IsBoundedRepresentative X Y q}
  zero_mem' := (boundedRepresentative_submodule_axioms X Y).1
  add_mem' := fun hq hr => (boundedRepresentative_submodule_axioms X Y).2.1 _ _ hq hr
  smul_mem' := fun a _ hq => (boundedRepresentative_submodule_axioms X Y).2.2 a _ hq

/-- A bounded representative with its genuine pointwise function data, HPS p. 27. -/
abbrev BoundedRepresentative := ↥(boundedRepresentatives X Y)


end HolomorphicAnosov.BoundedLipschitzJets

