import Mathlib.Topology.Homeomorph.Lemmas

namespace HolomorphicAnosov

/-- A one-step semiconjugacy through a homeomorphism gives the target recurrence
at every integer source time. Source: Manning Lemma 6, Step 3. -/
theorem factor_integer_recurrence
    {X Y : Type*} [TopologicalSpace X] (F : X ≃ₜ X) (g : Y → Y) (h : X → Y)
    (hsem : ∀ x, h (F x) = g (h x)) (x : X) (j : ℤ) :
    h ((F ^ (j + 1)) x) = g (h ((F ^ j) x)) := by
  rw [show j + 1 = 1 + j by omega, zpow_add, zpow_one, Homeomorph.mul_apply, hsem]

end HolomorphicAnosov
