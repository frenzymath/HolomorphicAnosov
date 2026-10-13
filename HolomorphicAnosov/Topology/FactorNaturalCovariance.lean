import Mathlib.Topology.Homeomorph.Lemmas

namespace HolomorphicAnosov

/-- A semiconjugacy intertwining a homeomorphism with a self-map commutes with
all natural iterates. Source: Manning Lemma 6 Steps 2 and 5; induction uses the
homeomorphism power and the given one-step semiconjugacy. -/
theorem factor_natural_covariance
    {X Y : Type*} [TopologicalSpace X] (F : X ≃ₜ X) (g : Y → Y) (h : X → Y)
    (hsem : ∀ x, h (F x) = g (h x)) (n : ℕ) (x : X) :
    h ((F ^ n) x) = g^[n] (h x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Homeomorph.mul_apply, ih, hsem, Function.iterate_succ_apply]

end HolomorphicAnosov
