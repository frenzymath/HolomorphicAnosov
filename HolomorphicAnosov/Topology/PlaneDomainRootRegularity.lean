import HolomorphicAnosov.Analysis.Complex.ConnectedComplementPolynomialApproximation
import HolomorphicAnosov.Analysis.Complex.PolynomialApproximationPrimitiveG2
open Set Filter Topology _root_.Topology
open Complex

namespace HolomorphicAnosov.Topology

/-- A continuous nonvanishing square root of a holomorphic function is holomorphic. -/
theorem continuous_root_differentiableOn
    {U : Set ℂ} (hU : IsOpen U) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hg : ContinuousOn g U)
    (hsq : ∀ z ∈ U, g z ^ 2 = f z)
    (hgn : ∀ z ∈ U, g z ≠ 0) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hfd := (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hgc : Tendsto g (𝓝 z) (𝓝 (g z)) :=
    (hg z hz).continuousAt (hU.mem_nhds hz) |>.tendsto
  have hsum : Tendsto (fun w => g w + g z) (𝓝 z) (𝓝 (g z + g z)) :=
    (hgc.add tendsto_const_nhds)
  have hsum0 : g z + g z ≠ 0 := by
    simpa [two_mul] using
      (mul_ne_zero (show (2 : ℂ) ≠ 0 by norm_num) (hgn z hz))
  have hden : {w | g w + g z ≠ 0} ∈ 𝓝 z :=
    hsum (isOpen_compl_singleton.mem_nhds hsum0)
  have hquot : Tendsto (fun w => slope f z w / (g w + g z))
      (nhdsWithin z {z}ᶜ) (𝓝 ((deriv f z) / (g z + g z))) := by
    exact hfd.tendsto_slope.div
      (hsum.mono_left (nhdsWithin_le_nhds)) hsum0
  have hder : HasDerivAt g (deriv f z / (g z + g z)) z :=
    hasDerivAt_iff_tendsto_slope.mpr (by
      apply hquot.congr'
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz),
        mem_nhdsWithin_of_mem_nhds hden] with w hw hwU hdenw
      unfold slope
      by_cases hwz : w = z
      · exact False.elim (hw hwz)
      · field_simp [hwz]
        rw [← hsq w hwU, ← hsq z hz]
        simp only [vsub_eq_sub]
        field_simp [hwz, hdenw]
        ring)
  exact hder.differentiableAt.differentiableWithinAt

/-- A connected spherical complement supplies holomorphic square roots on a plane domain.

Source: Conway, *Functions of One Complex Variable*, vol. I, VIII Theorem 2.2,
pp. 202–204, implications (d) through (h), with the polynomial approximation
theorem of Rudin XIII.6–7 as the named analytic provider.

Proof: approximate `f'/f` uniformly on compact subsets by polynomials. The named
primitive theorem normalizes entire polynomial primitives at one point, propagates
their Cauchy property across the connected domain, and differentiates their limit H.
Then `H'=f'/f`, so `f*exp(-H)` has zero derivative and is a constant c. It is nonzero
by evaluating at any point of the nonempty domain. Set
`g=exp(log(c)/2)*exp(H/2)`. This is holomorphic and exponential addition gives
`g^2=c*exp(H)=f`. -/
theorem conway_square_root_of_connected_complement
    {U : Set ℂ} (hUopen : IsOpen U) (hUconnected : IsConnected U)
    (hcompl : IsConnected ((fun z : ℂ ↦ (z : OnePoint ℂ)) '' U)ᶜ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (hfn : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z := by
  classical
  have hlogd : DifferentiableOn ℂ (fun z ↦ deriv f z / f z) U :=
    (hf.deriv hUopen).div hf hfn
  obtain ⟨p, hp⟩ :=
    HolomorphicAnosov.Analysis.Complex.conway_connected_complement_polynomial_approximation
      U hUopen hcompl _ hlogd
  obtain ⟨H, hH⟩ :=
    HolomorphicAnosov.Analysis.Complex.primitive_of_polynomial_approximation_g2
      hUopen hUconnected _ p hp
  have hdH : DifferentiableOn ℂ H U := fun z hz ↦
    (hH z hz).differentiableAt.differentiableWithinAt
  let q : ℂ → ℂ := fun z ↦ f z * Complex.exp (-H z)
  have hq (z : ℂ) (hz : z ∈ U) : HasDerivAt q 0 z := by
    convert ((hf.differentiableAt (hUopen.mem_nhds hz)).hasDerivAt.mul
      ((hH z hz).neg.cexp)) using 1
    field_simp [hfn z hz]
    ring
  obtain ⟨c, hc⟩ := hUopen.exists_is_const_of_deriv_eq_zero hUconnected.isPreconnected
    (fun z hz ↦ (hq z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hq z hz).deriv)
  have hcn : c ≠ 0 := by
    obtain ⟨a, ha⟩ := hUconnected.nonempty
    rw [← hc a ha]
    exact mul_ne_zero (hfn a ha) (Complex.exp_ne_zero _)
  have hcsq : Complex.exp (Complex.log c / 2) ^ 2 = c := by
    rw [pow_two, ← Complex.exp_add]
    convert Complex.exp_log hcn using 1
    congr 1
    ring
  refine ⟨fun z ↦ Complex.exp (Complex.log c / 2) * Complex.exp (H z / 2), ?_, ?_⟩
  · exact (hdH.div_const 2).cexp.const_mul _
  · intro z hz
    have he : Complex.exp (H z / 2) ^ 2 = Complex.exp (H z) := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    rw [mul_pow, hcsq, he, ← hc z hz]
    change (f z * Complex.exp (-H z)) * Complex.exp (H z) = f z
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end HolomorphicAnosov.Topology

