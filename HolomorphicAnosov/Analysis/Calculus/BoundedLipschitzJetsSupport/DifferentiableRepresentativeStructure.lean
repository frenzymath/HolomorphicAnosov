import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.ContinuousRepresentativeStructure

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Differentiable jets form a linear subspace, HPS (3.3), pp. 27,29.
The zero representative is differentiable. Sums of representatives have
derivative the sum, and scalar multiples have the scaled derivative.
Boundedness and quotient operations are already supplied by their concrete
representative submodule; these derivative rules give carrier closure. -/
theorem differentiableRepresentative_submodule_axioms :
    HasDifferentiableRepresentative X Y 0 ∧
    (∀ j k : BoundedJet X Y, HasDifferentiableRepresentative X Y j →
      HasDifferentiableRepresentative X Y k → HasDifferentiableRepresentative X Y (j + k)) ∧
    (∀ (a : ℝ) (j : BoundedJet X Y), HasDifferentiableRepresentative X Y j →
      HasDifferentiableRepresentative X Y (a • j)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, rfl, differentiableAt_const _⟩
  · rintro j k ⟨q, rfl, hq⟩ ⟨r, rfl, hr⟩
    exact ⟨q + r, rfl, hq.add hr⟩
  · rintro a j ⟨q, rfl, hq⟩
    exact ⟨a • q, rfl, hq.const_smul a⟩

/-- The concrete subspace J_d of differentiable-representative classes, HPS p. 27. -/
def differentiableJets : Submodule ℝ (BoundedJet X Y) where
  carrier := {j | HasDifferentiableRepresentative X Y j}
  zero_mem' := (differentiableRepresentative_submodule_axioms X Y).1
  add_mem' := fun hj hk => (differentiableRepresentative_submodule_axioms X Y).2.1 _ _ hj hk
  smul_mem' := fun a _ hj => (differentiableRepresentative_submodule_axioms X Y).2.2 a _ hj


end HolomorphicAnosov.BoundedLipschitzJets

