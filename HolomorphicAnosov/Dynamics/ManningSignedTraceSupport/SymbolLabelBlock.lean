import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OneComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabel

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The singleton alphabet really stores the singleton of its extracted label.
This is the finite-set calculation behind Manning's identification on p.218. -/
theorem symbolLabel_block {Λ : Type u} {N : ℕ} (R : Fin N → Set Λ)
    (s : Alphabet R oneComposition) (k : Fin oneComposition.length) :
    s.val k = {symbolLabel R s} := by
  have : Subsingleton (Fin oneComposition.length) := by
    simpa only [oneComposition, Composition.single_length] using
      (inferInstance : Subsingleton (Fin 1))
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  exact Classical.choose_spec (Finset.card_eq_one.mp ((s.property.2.1 (0 : Fin 1)).trans
    (Composition.single_blocksFun (n := 1) (by decide) (0 : Fin 1))))


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
