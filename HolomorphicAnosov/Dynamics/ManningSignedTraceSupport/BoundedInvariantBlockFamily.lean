import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open scoped Classical

/-- Ordered nonempty disjoint invariant block families, tagged by their positive
length at most q. The zero-length tag is present in the finite ambient index but
has no inhabitants. Source: Manning (1971), pp.218–219, ordered invariant families. -/
abbrev BoundedInvariantBlockFamily {A : Type*} [DecidableEq A] (g : A ≃ A) (q : ℕ) :=
  Σ k : Fin (q + 1), {S : Fin k.val → Finset A // 0 < k.val ∧
    (∀ i, (S i).Nonempty) ∧ (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
    ∀ i, (S i).image g = S i}

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
