import HolomorphicAnosov.Dynamics.Bowen.BracketCovarianceRadius

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- Finite-prefix covariance at one common radius, as used to refine the iterate
partition to the original map. Source: Bowen (1970), Lemma 11(a) and its use in
Lemma 23, p.738. Every intermediate pair is guarded; the proof claims no covariance
of an arbitrary totalized bracket outside that domain. -/
theorem exists_bracket_finite_prefix_radius
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.closeRadius ∧
      ∀ (m : ℕ) (x y : X),
        (∀ k ≤ m, dist ((f : X → X)^[k] x) ((f : X → X)^[k] y) ≤ r) →
        (f : X → X)^[m] (H.bracket x y) =
          H.bracket ((f : X → X)^[m] x) ((f : X → X)^[m] y) := by
  obtain ⟨r, hr, hrcore, hcov⟩ := exists_bracket_covariance_radius f γ lam H
  refine ⟨r, hr, hrcore, ?_⟩
  intro m
  induction m with
  | zero => intro x y hxy; rfl
  | succ m ih =>
      intro x y hxy
      rw [Function.iterate_succ_apply', ih x y (fun k hk ↦ hxy k (by omega))]
      simp only [Function.iterate_succ_apply']
      apply hcov _ _ (hxy m (by omega))
      simpa only [Function.iterate_succ_apply'] using hxy (m + 1) (le_refl _)

end HolomorphicAnosov.Dynamics.Bowen
