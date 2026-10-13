import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SignedTraceSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SignedTraceOfLocalCount
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped BigOperators Classical
noncomputable section

/-- If every periodic word has a unique physical image, local signed fibre counts imply the global signed trace formula. (Manning, pp. 218–219) -/
theorem signedTrace_of_physical_fibre_counts {X : Type*} {N m q : ℕ}
    (F : X → X) (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ) (hm : 0 < m)
    (hfinite : Set.Finite {x : X | (F^[m]) x = x})
    (himage : ∀ c : PositiveComposition q, ∀ w : PeriodicWord R T c.2 hm,
      ∃ x, x ∈ periodicPhysicalPoints R T c.2 F hm w)
    (hunique : ∀ c : PositiveComposition q, ∀ w : PeriodicWord R T c.2 hm,
      (periodicPhysicalPoints R T c.2 F hm w).Subsingleton)
    (hlocal : ∀ x, (F^[m]) x = x → ∑ c : PositiveComposition q,
      (-1 : ℤ) ^ (c.2.length + 1) * Nat.card {w : PeriodicWord R T c.2 hm //
        x ∈ periodicPhysicalPoints R T c.2 F hm w} = 1) :
    (Nat.card {x : X // (F^[m]) x = x} : ℤ) = signedTraceSum R T q m := by
  classical
  let Y := {x : X // (F^[m]) x = x}
  let : Finite Y := hfinite.to_subtype
  let : Fintype Y := Fintype.ofFinite Y
  let p : ∀ c : PositiveComposition q, PeriodicWord R T c.2 hm → Y :=
    fun c w ↦ ⟨(himage c w).choose, (himage c w).choose_spec.1⟩
  apply signedTrace_of_local_count R T hm p
  intro y
  have h := hlocal y.val y.property
  apply Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  apply congrArg (fun n : ℕ ↦ (n : ℤ))
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro w
  constructor
  · intro hp
    have hh := (himage c w).choose_spec
    have hv : (himage c w).choose = y.val := congrArg Subtype.val hp
    exact hv ▸ hh
  · intro hy
    apply Subtype.ext
    exact hunique c w (himage c w).choose_spec hy

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
