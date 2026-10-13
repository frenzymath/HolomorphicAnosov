import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OneComposition

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- A label with a point in its rectangle determines a literal singleton symbol.
Manning p.218: the one-block alphabet is the original rectangle alphabet. -/
def singletonSymbol {Λ : Type u} {N : ℕ} (R : Fin N → Set Λ)
    (hne : ∀ i, (R i).Nonempty) (i : Fin N) : Alphabet R oneComposition :=
  ⟨fun _ ↦ {i}, by
    have : Subsingleton (Fin oneComposition.length) := by
      simpa only [oneComposition, Composition.single_length] using
        (inferInstance : Subsingleton (Fin 1))
    refine ⟨fun _ ↦ Finset.singleton_nonempty _, ?_, ?_, ?_⟩
    · intro k
      simp [oneComposition, Composition.single_blocksFun]
    · intro k l hkl
      exact False.elim (hkl (Subsingleton.elim _ _))
    · obtain ⟨x, hx⟩ := hne i
      exact ⟨x, fun _ j hj ↦ (Finset.mem_singleton.mp hj) ▸ hx⟩⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
