import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Cauchy–Schwarz for a compactly supported regular pairing

Source: Zhang, Lemma 4.3, printed p.16, concluding passage after equation (31).
This public extraction reuses the existing G7 proof. The explicit compact-support
integrability argument expands the L²-to-distribution implication omitted in the paper.
DAG node: `analysis.regular_pairing_l2_bound_g4`.
-/

open MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.DistributionalSection

/-- A regular pairing is bounded by the two L² norms on the exact support of the test.

Source: agent-written expansion of the concluding implication in Zhang Lemma 4.3,
p.16, after equation (31), reusing G7's existing explicit proof.
The coefficient is continuous on the open domain, hence on the compact test support.
It is bounded there and strongly measurable for restricted volume, so it belongs
first to L∞ and then to L² since this compact support has finite Lebesgue measure.
The smooth compactly supported test is also in L². Outside its support the product
is zero, and outside the open domain the test vanishes, so both pairing integrals
reduce to the same support. The norm of its integral is at most the integral of the
product of the norms. Apply Hölder with exponents 2 and 2, then rewrite the real
half-powers as square roots. A zero test or empty domain gives zero on both sides;
no regularity or integrability of the coefficient outside the domain is assumed. -/
theorem regular_pairing_l2_bound {d : ℕ}
    (Ω : Opens (Fin d → ℂ)) (b : (Fin d → ℂ) → ℂ)
    (hb : ContinuousOn b Ω) (φ : TestFunction Ω ℂ ⊤) :
    ‖regularPairing Ω b φ‖ ≤
      Real.sqrt (∫ z in tsupport φ, ‖b z‖ ^ 2 ∂volume) *
        Real.sqrt (∫ z in tsupport φ, ‖φ z‖ ^ 2 ∂volume) := by
  have hbc := hb.mono φ.tsupport_subset
  obtain ⟨C, hC⟩ := φ.hasCompactSupport.exists_bound_of_continuousOn hbc
  have htop : MemLp b ⊤ (volume.restrict (tsupport φ)) :=
    memLp_top_of_bound (hbc.aestronglyMeasurable (isClosed_tsupport _).measurableSet) C
      ((ae_restrict_mem (isClosed_tsupport _).measurableSet).mono fun z hz ↦ hC z hz)
  have h2b : MemLp b (ENNReal.ofReal 2) (volume.restrict (tsupport φ)) :=
    htop.mono_exponent_of_measure_support_ne_top (s := Set.univ)
      (by simp) (by simpa using φ.hasCompactSupport.measure_lt_top (μ := volume) |>.ne) le_top
  have h2φ : MemLp (φ : (Fin d → ℂ) → ℂ) (ENNReal.ofReal 2)
      (volume.restrict (tsupport φ)) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have heq : regularPairing Ω b φ = ∫ z in tsupport φ, b z * φ z ∂volume := by
    rw [regularPairing, setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · intro z hz
      simp [image_eq_zero_of_notMem_tsupport hz]
    · intro z hz
      simp [φ.zero_on_compl hz]
  rw [heq]
  calc
    _ ≤ ∫ z in tsupport φ, ‖b z * φ z‖ ∂volume := norm_integral_le_integral_norm _
    _ = ∫ z in tsupport φ, ‖b z‖ * ‖φ z‖ ∂volume := by simp only [norm_mul]
    _ ≤ _ := by
      simpa only [ENNReal.ofReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow] using
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two h2b h2φ
end HolomorphicAnosov.DistributionalSection

