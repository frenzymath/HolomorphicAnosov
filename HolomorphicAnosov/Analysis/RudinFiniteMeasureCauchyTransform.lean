import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Finite-measure Cauchy transforms

The density form of Walter Rudin, *Real and Complex Analysis*, third edition,
Theorems 10.6–10.7, printed pp. 198–200. The domain is an arbitrary measurable
space; neither a topology nor a regular measure on that domain is required.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace HolomorphicAnosov

/-- The Cauchy transform of a pointwise bounded measurable density with respect
to a finite positive measure is analytic off the whole image of its measurable
pole map. Every open disk contained in that complement has the displayed
integral coefficients and their bound, including coefficient zero.

Source: Walter Rudin, *Real and Complex Analysis*, third edition (1987),
Theorems 10.6–10.7, printed pp. 198–200 (PDF pp. 211–213), with the direct
weighted-positive-measure specialization of the written geometric-series proof.
The whole-image disjointness and the all-point density bound are hypotheses;
no support-only or almost-everywhere substitute is made.

Natural-language proof (the current DAG proof, steps R1–R6):

R1. Retain the literal measurable X, finite positive λ, measurable g and φ and all-point |g|≤1.
Write m=λ.real(X), a finite nonnegative real number. For any a∈Ω choose r>0 with D(a,r)⊂Ω; more
generally fix ANY positive r with this disk inclusion. Whole-image disjointness implies
|φ(x)−a|≥r for every x: a strict value below r would put φ(x) inside D(a,r)⊂Ω. Boundary equality
is allowed. For z∈D(a,r), the reverse triangle inequality gives |φ(x)−z|≥r−|z−a|>0. Thus
K_z(x)=g(x)/(φ(x)−z) is measurable (continuous polynomial arithmetic composed with measurable φ
and the named total measurable quotient). The complex target is a second-countable Borel normed
space, so measurable implies strongly measurable and then AE strongly measurable for this SAME
λ. Its norm is at most 1/(r−|z−a|). The finite-measure bounded-integrability leaf therefore
gives genuine Bochner Integrable K_z. Choosing a=z proves the claimed integrability at every
z∈Ω. No topology on X, support separation, positive mass or denominator merely AE separation is
substituted for the hypotheses.

R2. For each n≥0 the measurable coefficient kernel A_n(x)=g(x)/(φ(x)−a)^(n+1) obeys
|A_n(x)|≤r^(−n−1). Strong/AE strong measurability follows as in R1, and the finite bounded-
integrability leaf proves A_n genuinely integrable. Define c_n=∫A_n dλ. The integral norm
inequality with the INTEGRABLE constant real majorant r^(−n−1) gives |c_n|≤m/r^(n+1). That
constant is integrable by finite-measure bounded integrability, and its integral is m/r^(n+1),
by the exact constant restricted integral at X=univ. This proves the bound at n=0 as well as all
higher indices, for the originally chosen arbitrary admissible r. m may be zero; it is never
inverted.

R3. Fix z∈D(a,r), put w=z−a and q=|w|/r∈[0,1). For every x the ratio ξ_x=w/(φ(x)−a) has norm≤q<1.
The exact complex geometric-sum theorem, multiplied by g(x)/(φ(x)−a), gives K_z(x)=sum_(n≥0)
A_n(x) w^n. More explicitly the finite geometric identity gives
K_z(x)−sum_(n<N)A_n(x)w^n=[g(x)/(φ(x)−a)] ξ_x^N/(1−ξ_x). Hence its norm is at most
r^(−1)q^N/(1−q), uniformly in x. Each term has norm≤r^(−1)q^n; the real geometric sum bounds
every partial sum by r^(−1)/(1−q). These estimates include N=0 with the empty sum and q=0 with
its usual zeroth power. As q^N→0 the series converges uniformly on X for THIS fixed z, exactly
as in the printed proof. Uniformity for z in any smaller closed disk follows by replacing q with
that disk’s radius divided by r; no uniform convergence on the whole open D(a,r) is asserted.

R4. Let S_N(x)=sum_(n<N)A_n(x)w^n. Each summand is measurable and genuinely integrable, either by
its bound r^(−1)q^n and the finite bounded-integrability leaf or by scalar multiplication of the
coefficient kernel. Their finite sum is integrable by the existing finite-sum integrability
theorem. The error K_z−S_N is measurable and bounded by the finite constant B_N=r^(−1)q^N/(1−q),
so it too is genuinely Bochner integrable. Finite-sum integration and constant complex
multiplication give ∫S_N dλ=sum_(n<N)c_n w^n (write A_n w^n=w^n A_n in the commutative complex
field). Integral subtraction is used only after K_z and S_N are integrable. The norm-integral
inequality and constant integral evaluation then give |h(z)−sum_(n<N)c_n w^n|=|∫(K_z−S_N)dλ|≤m
B_N→0. To pass from ordered initial sums to Mathlib’s unordered HasSum, R2 gives |c_n
w^n|≤(m/r)q^n. The real geometric series and constant multiplication make this real majorant
summable, and the existing complete-normed-group comparison leaf (target ℂ complete) makes the
literal coefficient series summable. Its finite initial sums tend to its genuine sum; their
already established limit h(z) identifies that sum by uniqueness in ℂ. Equivalently, for ANY
finite index set T containing {0,…,N−1}, its additional terms have norm sum≤(m/r)q^N/(1−q), so
|h(z)−sum_(n∈T)c_n w^n|≤2(m/r)q^N/(1−q). This bound→0 proves the actual net of all finite
subsums has limit h(z). Thus HasSum refers to that unordered net, not an inference of
unconditional summation from ordered convergence alone. The printed interchange of
summation/integration is fully justified by the same uniform tail and finite λ, not by a
totalized nonintegrable integral. No division by m or exchange without a domination bound
occurs.

R5. To express Rudin’s convergent scalar power series as genuine complex analyticity, let
p=FormalMultilinearSeries.ofScalars ℂ c, the actual series of continuous multilinear maps
p_n(v_1,…,v_n)=c_n product_j v_j. Its diagonal value is c_n w^n, including the empty product at
n=0. The exact ofScalars_norm theorem gives ‖p_n‖=|c_n| for EVERY n, not just n>0. R2 therefore
gives ‖p_n‖r^n≤m/r for all n. Treat the positive r as an NNReal and apply the existing radius
lower-bound leaf with constant C=m/r≥0 to obtain r≤p.radius; the leaf requires no positive C.
The actual HasFPowerSeriesOnBall structure has three guards: r≤p.radius, r>0, and for every w in
the radius-r ball about0, HasSum (n↦p_n(w,…,w)) (h(a+w)). The first two have just been proved,
and R4 supplies the third because a+w∈D(a,r). Thus h has this SAME power series on the entire
radius-r ball about a. Unfold HasFPowerSeriesAt by taking this positive radius r and its just-
proved ball certificate; unfold AnalyticAt by taking this same genuine series p. These are
elementary existential witnesses, and give AnalyticAt ℂ h a without a separate conversion node.
The total extension of h outside Ω does not affect any of these local equalities. Repeating at
every a∈Ω proves complex analyticity on Ω. AnalyticAt.contDiffAt at finite order1, with complete
scalar target ℂ, and the nonzero-order differentiability conversion give complex
differentiability at every such a, hence holomorphy on Ω. This is the scalar series⇒holomorphic
interface of Rudin10.6pp198–199, with a full formal multilinear witness and radius guard, not an
unproved named coordinate-series predicate or a Cauchy formula assuming holomorphy.

R6. If λ=0 or X is empty then all coefficient and kernel integrals vanish and every estimate remains
valid; no positive-mass assumption was used. Ω may be empty, making pointwise conclusions
vacuous. Disk boundary points of φ(X) are allowed because only |φ−a|≥r is required. Coefficients
may vanish at arbitrarily many indices, so no coefficient ratio-test division is used. Arbitrary
measurable g and φ remain admissible; none was assumed continuous, compactly supported or
essentially supported away from Ω. The conclusion concerns finite plane points only and says
nothing about analyticity at infinity.

The integrals below are Mathlib's Bochner integrals. Explicit integrability
conclusions prevent reliance on their totalized value at nonintegrable kernels.
`HasSum` states convergence of the net of all finite subsums. The local lets
specify the transform and coefficients without introducing a custom analytic
predicate or an additional definition. The proof is deliberately postponed in
Stage 2; this theorem is the single named `sorry` for the matching DAG node.
-/
theorem rudin_finite_measure_cauchy_transform
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (g φ : X → ℂ) (hg : Measurable g) (hφ : Measurable φ)
    (hg_bound : ∀ x, ‖g x‖ ≤ 1)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (hdisjoint : Disjoint Ω (Set.range φ)) :
    let h : ℂ → ℂ := fun z => ∫ x, g x / (φ x - z) ∂μ
    (∀ z ∈ Ω, Integrable (fun x => g x / (φ x - z)) μ) ∧
    AnalyticOnNhd ℂ h Ω ∧
    (∀ z ∈ Ω, DifferentiableAt ℂ h z) ∧
    (∀ (a : ℂ) (r : ℝ), 0 < r → Metric.ball a r ⊆ Ω →
      let c : ℕ → ℂ := fun n => ∫ x, g x / (φ x - a) ^ (n + 1) ∂μ
      (∀ n, Integrable (fun x => g x / (φ x - a) ^ (n + 1)) μ) ∧
      (∀ n, ‖c n‖ ≤ μ.real Set.univ / r ^ (n + 1)) ∧
      (∀ z ∈ Metric.ball a r, HasSum (fun n => c n * (z - a) ^ n) (h z))) := by
  classical
  dsimp only
  have hsep (a : ℂ) (r : ℝ) (hball : Metric.ball a r ⊆ Ω) (x : X) :
      r ≤ ‖φ x - a‖ := by
    by_contra hx
    exact Set.disjoint_left.mp hdisjoint (hball (by simpa [Metric.mem_ball, dist_eq_norm] using lt_of_not_ge hx))
      (Set.mem_range_self x)
  have hcoeff (a : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.ball a r ⊆ Ω) :
      (∀ n : ℕ, Integrable (fun x ↦ g x / (φ x - a) ^ (n + 1)) μ) ∧
      (∀ n : ℕ, ‖∫ x, g x / (φ x - a) ^ (n + 1) ∂μ‖ ≤ μ.real Set.univ / r ^ (n + 1)) := by
    have hb (n : ℕ) (x : X) : ‖g x / (φ x - a) ^ (n + 1)‖ ≤ 1 / r ^ (n + 1) := by
      rw [norm_div, norm_pow]
      exact (div_le_div_of_nonneg_right (hg_bound x) (by positivity)).trans
        (one_div_le_one_div_of_le (pow_pos hr _) (pow_le_pow_left₀ hr.le (hsep a r hball x) _))
    constructor
    · intro n
      exact Integrable.of_bound (hg.div ((hφ.sub measurable_const).pow_const _)).aestronglyMeasurable
        (1 / r ^ (n + 1)) (Filter.Eventually.of_forall (hb n))
    · intro n
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
        norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall (hb n))
  have hsum (a : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.ball a r ⊆ Ω)
      (z : ℂ) (hz : z ∈ Metric.ball a r) :
      HasSum (fun n : ℕ ↦ (∫ x, g x / (φ x - a) ^ (n + 1) ∂μ) * (z - a) ^ n)
        (∫ x, g x / (φ x - z) ∂μ) := by
    have hz' : ‖z - a‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    let q := ‖z - a‖ / r
    have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hr.le
    have hq1 : q < 1 := (div_lt_one hr).mpr hz'
    have hb (n : ℕ) (x : X) :
        ‖g x / (φ x - a) ^ (n + 1) * (z - a) ^ n‖ ≤ (1 / r) * q ^ n := by
      rw [norm_mul, norm_div, norm_pow, norm_pow]
      calc
        ‖g x‖ / ‖φ x - a‖ ^ (n + 1) * ‖z - a‖ ^ n
            ≤ (1 / r ^ (n + 1)) * ‖z - a‖ ^ n := by
          gcongr
          · exact hg_bound x
          · exact hsep a r hball x
        _ = (1 / r) * q ^ n := by rw [div_pow, pow_succ]; ring
    have hpoint (x : X) : HasSum
        (fun n : ℕ ↦ g x / (φ x - a) ^ (n + 1) * (z - a) ^ n)
        (g x / (φ x - z)) := by
      have hdpos : 0 < ‖φ x - a‖ := hr.trans_le (hsep a r hball x)
      have hd : φ x - a ≠ 0 := norm_pos_iff.mp hdpos
      have hzden : φ x - z ≠ 0 := sub_ne_zero.mpr (by
        intro heq
        exact Set.disjoint_left.mp hdisjoint (hball hz) (heq ▸ Set.mem_range_self x))
      have hratio : ‖(z - a) / (φ x - a)‖ < 1 := by
        rw [norm_div, div_lt_one hdpos]
        exact hz'.trans_le (hsep a r hball x)
      have h := (hasSum_geometric_of_norm_lt_one hratio).mul_left (g x / (φ x - a))
      convert h using 1
      · funext n
        simp only [div_eq_mul_inv, mul_pow, pow_succ, mul_inv_rev, inv_pow]
        ring
      · have hdeneq : (1 : ℂ) - (z - a) / (φ x - a) =
            (φ x - z) / (φ x - a) := by
          field_simp
          ring
        rw [hdeneq, inv_div]
        field_simp [hd, hzden]
    have h := hasSum_integral_of_dominated_convergence
      (μ := μ) (fun n (_ : X) ↦ (1 / r) * q ^ n)
      (fun n ↦ ((hg.div ((hφ.sub measurable_const).pow_const _)).mul measurable_const).aestronglyMeasurable)
      (fun n ↦ Filter.Eventually.of_forall (hb n))
      (Filter.Eventually.of_forall (fun _ ↦ (summable_geometric_of_lt_one hq0 hq1).mul_left (1 / r)))
      (integrable_const _) (Filter.Eventually.of_forall hpoint)
    simpa only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, integral_mul_const] using h
  have hanalytic : AnalyticOnNhd ℂ (fun z ↦ ∫ x, g x / (φ x - z) ∂μ) Ω := by
    intro a ha
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ a ha
    let c : ℕ → ℂ := fun n ↦ ∫ x, g x / (φ x - a) ^ (n + 1) ∂μ
    let p := FormalMultilinearSeries.ofScalars ℂ c
    let R : ℝ≥0 := ⟨r, hr.le⟩
    have hp : HasFPowerSeriesOnBall (fun z ↦ ∫ x, g x / (φ x - z) ∂μ) p a R := by
      constructor
      · apply p.le_radius_of_bound (μ.real Set.univ / r)
        intro n
        change ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * r ^ n ≤ _
        rw [FormalMultilinearSeries.ofScalars_norm]
        calc
          ‖c n‖ * r ^ n ≤ (μ.real Set.univ / r ^ (n + 1)) * r ^ n :=
            mul_le_mul_of_nonneg_right ((hcoeff a r hr hball).2 n) (by positivity)
          _ = μ.real Set.univ / r := by rw [pow_succ]; field_simp
      · exact_mod_cast hr
      · intro y hy
        have hy' : ‖y‖ < r := by
          have hn : ‖y‖ₑ < (R : ℝ≥0∞) := by
            simpa only [Metric.mem_eball, edist_zero_right] using hy
          have hnr : ‖y‖₊ < R := enorm_lt_coe.mp hn
          exact_mod_cast hnr
        have h := hsum a r hr hball (a + y) (by simpa [Metric.mem_ball, dist_eq_norm] using hy')
        simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, add_sub_cancel_left] using h
    exact hp.analyticAt
  refine ⟨?_, hanalytic, fun z hz ↦ (hanalytic z hz).differentiableAt, ?_⟩
  · intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
    simpa using (hcoeff z r hr hball).1 0
  · intro a r hr hball
    exact ⟨(hcoeff a r hr hball).1, (hcoeff a r hr hball).2, hsum a r hr hball⟩

end HolomorphicAnosov

