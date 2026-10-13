import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Homeomorph.Defs
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- The relation of physical points fixed by the `m`-th iterate and lying in every rectangle prescribed by a finite periodic word. (de Jong, §3.2, pp. 2464–2465) -/
def periodicPhysicalPoints {Λ : Type u} {N r m : ℕ} (R : Fin N → Set Λ)
    (T : Matrix (Fin N) (Fin N) ℤ) (c : Composition r) (F : Λ → Λ) (hm : 0 < m)
    (w : PeriodicWord R T c hm) : Set Λ :=
  {x | (F^[m]) x = x ∧ ∀ t : Fin m, ∀ k, ∀ i ∈ (w.val t).val k,
    (F^[t.val]) x ∈ R i}


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
