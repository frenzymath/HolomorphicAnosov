import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.NormCore

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Continuous jets form a linear subspace, HPS (3.3), pp. 27–28.
The zero representative is continuous. For sums intersect the two open
neighborhoods and add the continuous maps; scalar multiplication preserves
continuity on the same neighborhood. The quotient class respects these
pointwise operations, giving the asserted carrier closure. -/
theorem continuousRepresentative_submodule_axioms :
    HasContinuousRepresentative X Y 0 ∧
    (∀ j k : BoundedJet X Y, HasContinuousRepresentative X Y j →
      HasContinuousRepresentative X Y k → HasContinuousRepresentative X Y (j + k)) ∧
    (∀ (a : ℝ) (j : BoundedJet X Y), HasContinuousRepresentative X Y j →
      HasContinuousRepresentative X Y (a • j)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, rfl, Set.univ, isOpen_univ, Set.mem_univ _, continuousOn_const⟩
  · rintro j k ⟨q, rfl, U, hU, h0U, hq⟩ ⟨r, rfl, V, hV, h0V, hr⟩
    refine ⟨q + r, rfl, U ∩ V, hU.inter hV, ⟨h0U, h0V⟩, ?_⟩
    exact (hq.mono Set.inter_subset_left).add (hr.mono Set.inter_subset_right)
  · rintro a j ⟨q, rfl, U, hU, h0U, hq⟩
    exact ⟨a • q, rfl, U, hU, h0U, hq.const_smul a⟩

/-- The concrete subspace J_c of continuous-representative classes, HPS p. 27. -/
def continuousJets : Submodule ℝ (BoundedJet X Y) where
  carrier := {j | HasContinuousRepresentative X Y j}
  zero_mem' := (continuousRepresentative_submodule_axioms X Y).1
  add_mem' := fun hj hk => (continuousRepresentative_submodule_axioms X Y).2.1 _ _ hj hk
  smul_mem' := fun a _ hj => (continuousRepresentative_submodule_axioms X Y).2.2 a _ hj


end HolomorphicAnosov.BoundedLipschitzJets

