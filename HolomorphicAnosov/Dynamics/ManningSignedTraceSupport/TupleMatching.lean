import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.218: every ordered block must admit its own bijective T-matching. -/
def TupleMatching {Λ : Type u} {N r : ℕ} (R : Fin N → Set Λ)
    (T : Matrix (Fin N) (Fin N) ℤ) (c : Composition r)
    (s t : Alphabet R c) : Prop := ∀ k, BlockMatching T (s.val k) (t.val k)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
