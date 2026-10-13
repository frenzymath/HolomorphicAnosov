import Mathlib.Data.Finset.Basic

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical
noncomputable section

/-- Encode a label by one block containing it, or by none when it is unused.
For pairwise disjoint blocks the choice is unique. This is the finite assignment
encoding in Manning's fibre-count bound (1971), pp.218–219. -/
def blockAssignment {A K : Type*} (S : K → Finset A) (a : A) : Option K :=
  if h : ∃ k, a ∈ S k then some (Classical.choose h) else none

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
