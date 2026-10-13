import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockAssignment

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- In a pairwise disjoint block family the assignment records exactly block
membership. A chosen block and the requested block sharing the label must be
equal by disjointness. The empty family and unused labels are allowed. -/
theorem blockAssignment_mem {A K : Type*} (S : K → Finset A)
    (hdis : Pairwise fun i j ↦ Disjoint (S i) (S j)) (a : A) (k : K) :
    blockAssignment S a = some k ↔ a ∈ S k := by
  classical
  unfold blockAssignment
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro hk
      have hk' := Option.some.inj hk
      simpa only [hk'] using hc
    · intro ha
      congr 1
      by_contra hne
      exact Finset.disjoint_left.mp (hdis hne) hc ha
  · simp only [false_iff]
    exact fun ha ↦ h ⟨k, ha⟩

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
