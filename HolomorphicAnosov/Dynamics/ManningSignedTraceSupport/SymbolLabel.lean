import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OneComposition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Manning p.218: retrieve the single actual label of a one-block alphabet symbol. -/
noncomputable def symbolLabel {Λ : Type u} {N : ℕ} (R : Fin N → Set Λ)
    (s : Alphabet R oneComposition) : Fin N :=
  Classical.choose (Finset.card_eq_one.mp ((s.property.2.1 (0 : Fin 1)).trans
    (Composition.single_blocksFun (n := 1) (by decide) (0 : Fin 1))))


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
