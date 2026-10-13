import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.FixedSupportFirstDerivativeSections
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ScaledKernelFDerivNeg
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith

/-!
# First derivatives of local distribution mollification

Source: S. Dyatlov, *Lecture notes for 18.155: distributions, elliptic regularity,
and applications to PDEs*, 2 October 2026, Proposition 6.3, pp. 68–69, and
Theorem 6.4, equation (6.10), p. 69. The strict interior domain follows
Demailly, *Complex Analytic and Differential Geometry*, I §2.D.3 (2.23), p. 19.

This module states `analysis.mollifier_first_derivative_g11`. The test functions
use the canonical LF topology and the distribution is complex-linear with
no conjugation. The total representative may be arbitrary outside the strict
interior domain; the conclusion concerns only its germs inside that domain.
-/

open Set TopologicalSpace Filter
open scoped ContDiff ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/-- Local mollification is smooth, and each first parameter derivative equals
minus the distribution applied to the corresponding spatial test derivative.

Source: Dyatlov, Proposition 6.3 and Theorem 6.4 (6.10), pp. 68–69;
Demailly, I §2.D.3 (2.23), p. 19.

Proof: Fix x in the strict interior. Choose ε < r < dist(x,Uᶜ), where the
extended distance is infinite if Uᶜ is empty. Set P = B(x,r-ε) and
K = closedBall(x,r). Then K is compact and lies in U. For
H(p,y) = ε⁻ᵐ ρ(ε⁻¹(p-y)), the support assumption gives ‖p-y‖ ≤ ε
at every point of its support. For p in P the triangle inequality puts this
support in K. Affine composition makes H jointly smooth. The fixed-support
family theorem gives test sections, a smooth paired function, and the
parameter derivative formula. The strict interior is open by continuity of
extended distance. On P intersected with that interior, extensionality and hκ
identify these sections with κ, and hF identifies their pairing with F.
Thus F is smooth at x.

For coordinate i, use the multiindex equal to one at i and zero elsewhere.
Its direction list is the singleton [eᵢ], and the first iterated derivative
within the open P is the ordinary Fréchet derivative on eᵢ. For every y,
H(q,y) = κ(x)(x+y-q). The affine reflection has derivative minus the identity
at q=x and value y. The chain rule gives the parameter derivative
−fderiv(κ(x))(y)(eᵢ). At infinite differentiability order,
TestFunction.fderivCLM_apply_of_le and the definition of lineDerivCLM identify
this with the negative of the spatial test derivative. Test-function
extensionality identifies the differentiated section with
−lineDerivCLM(eᵢ)(κ(x)), and complex linearity of T gives the formula.

Empty U yields no evaluation points. For U equal to the whole space the
extended-distance convention admits every x. Zero T or ρ gives zero locally.
No positivity, normalization, or evenness of ρ is required. -/
theorem distribution_mollifier_first_derivative
    {m : ℕ} (hm : 1 ≤ m) (U : Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (ε : ℝ) (hε : 0 < ε)
    (κ : ∀ x, x ∈ {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)} →
      TestFunction U ℂ ⊤)
    (F : EuclideanSpace ℝ (Fin m) → ℂ)
    (hκ : ∀ x hx y, κ x hx y = (((ε⁻¹) ^ m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (x - y)) : ℝ) : ℂ))
    (hF : ∀ x hx, F x = T (κ x hx))
    (x : EuclideanSpace ℝ (Fin m))
    (hx : x ∈ {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)}) :
    ContDiffAt ℝ ∞ F x ∧ ∀ i : Fin m,
      fderiv ℝ F x (EuclideanSpace.single i 1) =
        -T (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single i 1) (κ x hx)) := by
  classical
  obtain ⟨r, hr0, hεr', hr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx.2
  have hεr : ε < r := ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.mp
    ((ENNReal.ofReal_pos.mpr hε).trans hεr')) |>.mp hεr'
  let P : Opens (EuclideanSpace ℝ (Fin m)) :=
    ⟨Metric.ball x (r - ε), Metric.isOpen_ball⟩
  let K : Set (EuclideanSpace ℝ (Fin m)) := Metric.closedBall x r
  let H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℂ :=
    fun p y ↦ (((ε⁻¹) ^ m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ)
  have hKU : K ⊆ U := by
    intro y hy
    by_contra hn
    have hdist : edist x y ≤ ENNReal.ofReal r := by
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      simpa only [K, Metric.mem_closedBall, dist_comm] using hy
    exact (not_le.mpr hr) ((Metric.infEDist_le_edist_of_mem (show y ∈ (U : Set _)ᶜ from hn)).trans hdist)
  have hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)) := by
    apply ContDiff.contDiffOn
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (ρ.contDiff.comp ((contDiff_fst.sub contDiff_snd).const_smul ε⁻¹)))
  have hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K := by
    intro p hp
    apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    have hρ : ρ (ε⁻¹ • (p - y)) ≠ 0 := by
      intro hz
      apply hy
      simp [H, hz]
    have hle := hρ_support (subset_closure hρ)
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)] at hle
    have hpy : ‖p - y‖ ≤ ε := by
      have := mul_le_mul_of_nonneg_left hle hε.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_one] using this
    have hp' : dist p x < r - ε := hp
    change dist y x ≤ r
    calc
      dist y x ≤ dist y p + dist p x := dist_triangle _ _ _
      _ ≤ ε + dist p x := add_le_add (by simpa [dist_eq_norm, norm_sub_rev] using hpy) le_rfl
      _ ≤ r := by linarith
  obtain ⟨sections, hsections, hsmooth, hderiv⟩ := fixed_support_first_derivative_sections
    hm hm U P T K (isCompact_closedBall x r) hKU H hH hSupport
  have hxP : x ∈ P := Metric.mem_ball_self (sub_pos.mpr hεr)
  let S : Set (EuclideanSpace ℝ (Fin m)) :=
    {p | p ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist p (U : Set _)ᶜ}
  have hSopen : IsOpen S :=
    U.isOpen.inter (isOpen_lt continuous_const Metric.continuous_infEDist)
  have heq : F =ᶠ[𝓝 x] (fun p ↦ T (sections p)) := by
    filter_upwards [P.isOpen.mem_nhds hxP, hSopen.mem_nhds hx] with p hp hps
    rw [hF p hps]
    congr 1
    apply TestFunction.ext
    intro y
    exact (hκ p hps y).trans (hsections p hp y).symm
  refine ⟨(hsmooth.contDiffAt (P.isOpen.mem_nhds hxP)).congr_of_eventuallyEq heq, ?_⟩
  intro i
  obtain ⟨θ, hθ, hpair⟩ := hderiv i x hxP
  have htest : θ = -TestFunction.lineDerivCLM ℂ (EuclideanSpace.single i 1) (κ x hx) := by
    apply TestFunction.ext
    intro y
    rw [hθ y]
    change (fderiv ℝ (fun p ↦ H p y) x) (EuclideanSpace.single i 1) =
      -(TestFunction.lineDerivCLM ℂ (EuclideanSpace.single i 1) (κ x hx)) y
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    have hκfun : (κ x hx : EuclideanSpace ℝ (Fin m) → ℂ) = H x :=
      funext (hκ x hx)
    rw [hκfun]
    exact scaled_kernel_fderiv_neg ρ ε x y (EuclideanSpace.single i 1)
  rw [heq.fderiv_eq, hpair, htest, map_neg]

end HolomorphicAnosov.Analysis.Distribution
