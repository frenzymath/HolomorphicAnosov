import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic

namespace HolomorphicAnosov

open Set

/--
An injective self-map carries every point of a finite forward-invariant set to a periodic point.
The proof is the finite pigeonhole argument: two iterates coincide, and injectivity cancels the
common initial iterate. This is a general finite-dynamics lemma independent of the Manning setting.
-/
theorem periodic_point_of_finite_invariant
    {X : Type*} (F : X → X) (hinj : Function.Injective F)
    (K : Set X) (hfinite : K.Finite) (hforward : MapsTo F K K)
    (x : X) (hx : x ∈ K) : ∃ r : ℕ, 1 ≤ r ∧ F^[r] x = x := by
  classical
  let := hfinite.fintype
  let FK : K → K := fun y ↦ ⟨F y, hforward y.property⟩
  let xK : K := ⟨x, hx⟩
  have hFK : Function.Injective FK := by
    intro y z hyz
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hyz)
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ ↦ FK^[k] xK)
  have hrep : ∃ r : ℕ, 1 ≤ r ∧ FK^[r] xK = xK := by
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨j - i, by omega, Function.iterate_cancel hFK heq.symm⟩
    · exact ⟨i - j, by omega, Function.iterate_cancel hFK heq⟩
  obtain ⟨r, hr, hfix⟩ := hrep
  have hval : ∀ k : ℕ, (FK^[k] xK).val = F^[k] x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change F (FK^[k] xK).val = F (F^[k] x)
      rw [ih]
  refine ⟨r, hr, ?_⟩
  rw [← hval, hfix]

end HolomorphicAnosov
