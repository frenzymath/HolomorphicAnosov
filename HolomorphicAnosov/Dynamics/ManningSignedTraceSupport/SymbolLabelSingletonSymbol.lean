import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabel
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabelBlock
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SingletonSymbol

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Extracting the label of the corresponding singleton returns that label. -/
@[simp] theorem symbolLabel_singletonSymbol {Λ : Type u} {N : ℕ}
    (R : Fin N → Set Λ) (hne : ∀ i, (R i).Nonempty) (i : Fin N) :
    symbolLabel R (singletonSymbol R hne i) = i := by
  have h := symbolLabel_block R (singletonSymbol R hne i) (0 : Fin 1)
  change {i} = {symbolLabel R (singletonSymbol R hne i)} at h
  exact (Finset.singleton_injective h).symm


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
