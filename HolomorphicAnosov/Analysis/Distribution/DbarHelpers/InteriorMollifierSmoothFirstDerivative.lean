import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.FixedSupportFirstDerivativeSections
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.LocalMollifierFirstDerivativeFromFamily
import HolomorphicAnosov.Analysis.Distribution.MollifierRegularization
import Mathlib.Analysis.Distribution.TestFunction

/-!
# interior_mollifier_smooth_first_derivative

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.
DAG node: `analysis.dbar_helper_interior_mollifier_smooth_first_derivative_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Pairing a scalar current with its supported scaled mollifier tests is smooth on the strict
interior domain, and every first coordinate derivative is the negative pairing with the spatial
test derivative.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.D.3 (2.23),
p.19, regularization on the strict interior; differentiation of translated kernels follows Dyatlov
Theorem6.4 p.69, and local fixed supports are as in its proof and Proposition6.3 pp.68–69.

Proof/construction: At an interior point x choose r strictly between epsilon and the distance to
the complement. The closed ball of radius r around x is compact and contained in the domain.
Restrict parameter points to their strict interior domain intersected with the ball of radius r
minus epsilon. The scaled-kernel support radius epsilon and the triangle inequality put every
section support inside the fixed closed ball. Apply the fixed-support family theorem there for
smoothness and its first-derivative specialization for the derivative identity. These local
smoothness statements cover the entire strict interior domain.
-/
theorem interior_mollifier_smooth_first_derivative {m : ℕ} (hm : 0 < m)
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρsupport : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆ Metric.closedBall 0 1)
    (ε : ℝ) (hε : 0 < ε)
    (κ : ∀ x, x ∈ mollifierDomain U ε → TestFunction U ℂ ⊤)
    (hκ : ∀ x hx y, κ x hx y = (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (x-y)) : ℝ) : ℂ))
    (F : EuclideanSpace ℝ (Fin m) → ℂ)
    (hF : ∀ x hx, F x = T (κ x hx)) :
    ContDiffOn ℝ ∞ F (mollifierDomain U ε) ∧
      ∀ x (hx : x ∈ mollifierDomain U ε) (j : Fin m),
        (fderiv ℝ F x) (EuclideanSpace.single j 1) =
          -T (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single j 1) (κ x hx)) := by
  have hopen : IsOpen (mollifierDomain U ε) :=
    U.isOpen.inter (isOpen_lt continuous_const Metric.continuous_infEDist)
  have hlocal (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ mollifierDomain U ε) :
      ∃ P : Opens (EuclideanSpace ℝ (Fin m)), x ∈ P ∧
        ContDiffOn ℝ ∞ F (P : Set _) ∧
        ∀ j : Fin m, (fderiv ℝ F x) (EuclideanSpace.single j 1) =
          -T (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single j 1) (κ x hx)) := by
    obtain ⟨r, _, hεr', hr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx.2
    have hεr : ε < r := ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.mp
      ((ENNReal.ofReal_pos.mpr hε).trans hεr')) |>.mp hεr'
    let P : Opens (EuclideanSpace ℝ (Fin m)) :=
      ⟨mollifierDomain U ε ∩ Metric.ball x (r-ε), hopen.inter Metric.isOpen_ball⟩
    let K := Metric.closedBall x r
    let H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℂ :=
      fun p y ↦ (((ε⁻¹)^m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (p-y)) : ℝ) : ℂ)
    have hxP : x ∈ P := ⟨hx, Metric.mem_ball_self (sub_pos.mpr hεr)⟩
    have hKU : K ⊆ U := by
      intro y hy
      by_contra hn
      have hd : edist x y ≤ ENNReal.ofReal r := by
        rw [edist_dist]
        apply ENNReal.ofReal_le_ofReal
        simpa only [K, Metric.mem_closedBall, dist_comm] using hy
      exact (not_le.mpr hr) ((Metric.infEDist_le_edist_of_mem
        (show y ∈ (U : Set _)ᶜ from hn)).trans hd)
    have hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (ρ.contDiff.comp ((contDiff_fst.sub contDiff_snd).const_smul ε⁻¹)))).contDiffOn
    have hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K := by
      intro p hp
      apply closure_minimal _ Metric.isClosed_closedBall
      intro y hy
      have hρ : ρ (ε⁻¹ • (p-y)) ≠ 0 := by
        intro hz
        exact hy (by simp [H, hz])
      have hle := hρsupport (subset_closure hρ)
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hε)] at hle
      have hpy : ‖p-y‖ ≤ ε := by
        have hh := mul_le_mul_of_nonneg_left hle hε.le
        simpa only [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_one] using hh
      have hp' : dist p x < r-ε := hp.2
      change dist y x ≤ r
      calc
        dist y x ≤ dist y p + dist p x := dist_triangle _ _ _
        _ ≤ ε + dist p x := add_le_add
          (by simpa [dist_eq_norm, norm_sub_rev] using hpy) le_rfl
        _ ≤ r := by linarith
    obtain ⟨s, hs, hsm, _⟩ := fixed_support_first_derivative_sections
      hm hm U P T K (isCompact_closedBall x r) hKU H hH hSupport
    refine ⟨P, hxP, ?_, ?_⟩
    · apply hsm.congr
      intro p hp
      rw [hF p hp.1]
      congr 1
      ext y
      exact (hκ p hp.1 y).trans (hs p hp y).symm
    · intro j
      exact local_mollifier_first_derivative_from_family hm U P T ρ ε K
        (isCompact_closedBall x r) hKU hSupport (fun p hp ↦ κ p hp.1)
        (fun p hp ↦ hκ p hp.1) F (fun p hp ↦ hF p hp.1) j x hxP
  constructor
  · apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨P, hxP, hsm, _⟩ := hlocal x hx
    exact ⟨P, P.isOpen, hxP, hsm.mono Set.inter_subset_right⟩
  · intro x hx j
    obtain ⟨P, _, _, hd⟩ := hlocal x hx
    exact hd j


end HolomorphicAnosov.Analysis.Distribution
