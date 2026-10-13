import Mathlib.Data.Int.Init
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Convert

/-!
# Paths through integer-indexed equivalences

Source context: Manning (1971), pp.218–219. The dependent interface and explicit
integer recursion argument are agent-written.
DAG node: `dynamics.manning_integer_equivalence_path_g15`.
-/

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
noncomputable section

/-- Follow a sequence of bijections in both integer directions from a prescribed
vertex at a prescribed time. Forward recursion uses the bijections and backward recursion
uses their inverses. The two recursions agree at that time and satisfy every successor
edge, so no periodicity or uniqueness of the chosen bijections is assumed.
This is the elementary path construction in Manning's matching argument,
Manning (1971), pp.218–219; the exact dependent interface is agent-written. -/
theorem integer_equivalence_path {A : ℤ → Type*}
    (E : ∀ j, A j ≃ A (j + 1)) (j₀ : ℤ) (a₀ : A j₀) :
    ∃ a : ∀ j, A j, a j₀ = a₀ ∧ ∀ j, E j (a j) = a (j + 1) := by
  let a : ∀ j, A j := fun j ↦ Int.inductionOn' j j₀ a₀
    (fun k _ v ↦ E k v)
    (fun k _ v ↦ (E (k - 1)).symm (by simpa using v))
  refine ⟨a, ?_, ?_⟩
  · simp only [a, Int.inductionOn'_self]
  · intro j
    by_cases hj : j₀ ≤ j
    · simp only [a, Int.inductionOn'_add_one hj]
    · have hj' : j + 1 ≤ j₀ := by omega
      have ha := Int.inductionOn'_sub_one (z := j + 1) (b := j₀)
        (zero := a₀) (succ := fun k _ v ↦ E k v)
        (pred := fun k _ v ↦ (E (k - 1)).symm (by simpa using v)) hj'
      have hh := congrArg (E (j + 1 - 1)) ha
      convert hh using 1 <;> simp [a, Int.add_sub_cancel]
      exact Eq.rec (motive := fun l _ ↦ HEq (E j (a j)) (E l (a l)))
        (HEq.refl _) (show j = j + 1 - 1 by omega)


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter
