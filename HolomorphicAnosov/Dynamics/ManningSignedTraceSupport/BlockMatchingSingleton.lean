import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators Classical
noncomputable section

/-- A matching of singleton blocks is exactly its single matrix edge.
This is Manning's p.218 singleton-matrix calculation, without a dynamical premise. -/
theorem blockMatching_singleton {N : ℕ} (T : Matrix (Fin N) (Fin N) ℤ)
    (i j : Fin N) : BlockMatching T {i} {j} ↔ T i j = 1 := by
  constructor
  · rintro ⟨e, he⟩
    have h := he ⟨i, Finset.mem_singleton_self i⟩
    have hj : (e ⟨i, Finset.mem_singleton_self i⟩).val = j :=
      Finset.mem_singleton.mp (e ⟨i, Finset.mem_singleton_self i⟩).property
    simpa only [hj] using h
  · intro h
    let e : ↥({i} : Finset (Fin N)) ≃ ↥({j} : Finset (Fin N)) :=
      { toFun := fun _ ↦ ⟨j, Finset.mem_singleton_self j⟩
        invFun := fun _ ↦ ⟨i, Finset.mem_singleton_self i⟩
        left_inv := fun x ↦ Subtype.ext (Finset.mem_singleton.mp x.property).symm
        right_inv := fun x ↦ Subtype.ext (Finset.mem_singleton.mp x.property).symm }
    refine ⟨e, fun x ↦ ?_⟩
    change T x.val j = 1
    simpa only [Finset.mem_singleton.mp x.property] using h


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
