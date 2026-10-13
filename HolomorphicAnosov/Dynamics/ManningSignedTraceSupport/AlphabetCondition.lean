import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Blocks
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CommonPoint

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning pp.217–218: exact sizes, nonempty pairwise disjoint blocks and a common point. -/
def AlphabetCondition {Λ : Type u} {N r : ℕ} (R : Fin N → Set Λ)
    (c : Composition r) (s : Blocks N c) : Prop :=
  (∀ k, (s k).Nonempty) ∧ (∀ k, (s k).card = c.blocksFun k) ∧
    (∀ k l, k ≠ l → Disjoint (s k) (s l)) ∧ CommonPoint R s


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
