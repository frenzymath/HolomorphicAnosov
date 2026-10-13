import HolomorphicAnosov.Analysis.MatherFiniteEnergyContraction

namespace HolomorphicAnosov

/-- The finite-energy choice in Hirsch–Pugh's adaptation: for C≥1 and 0<λ<1,
choose a positive iterate q with C λ^q<1, and the resulting quadratic-energy
coefficient c lies strictly between zero and one.

Source: Hirsch–Pugh, *Stable Manifolds and Hyperbolic Sets* (1969), Theorem 3.1,
printed p.148. The proof combines geometric convergence of powers with the
explicit coefficient bounds for the shifted finite sum. -/
theorem hirsch_pugh_contraction_parameters
    {C rate : ℝ} (hC : 1 ≤ C) (hrate_pos : 0 < rate) (hrate_lt_one : rate < 1) :
    ∃ q : ℕ, 0 < q ∧ C * rate ^ q < 1 ∧
      0 < 1 - (1 - (C * rate ^ q) ^ 2) / ((q : ℝ) * C ^ 2) ∧
      1 - (1 - (C * rate ^ q) ^ 2) / ((q : ℝ) * C ^ 2) < 1 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hCpos) hrate_lt_one
  have hsmall : C * rate ^ q < 1 := by
    have := (lt_div_iff₀ hCpos).mp hq
    nlinarith
  have hqpos : 0 < q := by
    by_contra hn
    have hzero : q = 0 := by omega
    simp only [hzero, pow_zero, mul_one] at hsmall
    exact (not_lt_of_ge hC) hsmall
  obtain ⟨hc0, hc1⟩ := FactOneFiniteEnergy.contraction_coefficient_bounds
    C rate hC hrate_pos q hqpos hsmall
  exact ⟨q, hqpos, hsmall, hc0, hc1⟩

end HolomorphicAnosov
