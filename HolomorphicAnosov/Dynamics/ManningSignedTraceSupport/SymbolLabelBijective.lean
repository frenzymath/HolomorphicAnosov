import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabel
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabelBlock
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SingletonSymbol
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabelSingletonSymbol

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- Nonempty rectangles make the one-block alphabet bijective to the original
labels, including an empty label type. No coding or trace identity is assumed. -/
theorem symbolLabel_bijective {Λ : Type u} {N : ℕ} (R : Fin N → Set Λ)
    (hne : ∀ i, (R i).Nonempty) : Function.Bijective (symbolLabel R) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    funext k
    rw [symbolLabel_block, symbolLabel_block, hst]
  · intro i
    exact ⟨singletonSymbol R hne i, symbolLabel_singletonSymbol R hne i⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
