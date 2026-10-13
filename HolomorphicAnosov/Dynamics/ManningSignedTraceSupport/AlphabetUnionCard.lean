import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The disjoint blocks of an alphabet symbol contain exactly the total number
of labels specified by its composition. This is the finite-set count in Manning
1971, p. 217, before passing to the maximal common overlap. -/
theorem alphabet_union_card {Λ : Type u} {N r : ℕ} (R : Fin N → Set Λ)
    (c : Composition r) (s : Alphabet R c) :
    (Finset.univ.biUnion fun k : Fin c.length ↦ s.val k).card = r := by
  classical
  have hdisj : ((Finset.univ : Finset (Fin c.length)) : Set (Fin c.length)).PairwiseDisjoint
      (fun k ↦ s.val k) := by
    intro k _ l _ hkl
    exact s.property.2.2.1 k l hkl
  rw [Finset.card_biUnion hdisj]
  simpa only [s.property.2.1] using c.sum_blocksFun


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
