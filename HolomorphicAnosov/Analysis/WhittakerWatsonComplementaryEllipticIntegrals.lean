import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import HolomorphicAnosov.Analysis.WhittakerWatsonCentralIntegrable
import HolomorphicAnosov.Analysis.WhittakerWatsonSubstitution
import HolomorphicAnosov.Analysis.IntervalIntegralInteriorEndpointLimit

/-!
# Real complementary complete elliptic integrals

Whittaker and Watson, *A Course of Modern Analysis*, third edition (1920), §22.32,
printed p. 501 (local PDF p. 515), gives the positive-radical substitution proving the
complementary complete elliptic integral identity for `0 < k < 1`. The kernels below have
explicit zero values outside their open carriers, including at their singular endpoints.
The theorem records genuine real-volume integrability, the signed interval-integral
identity, and the corresponding classical improper limits. The proof follows the source positive-radical substitution.
-/

open MeasureTheory Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

noncomputable section

/-- The central positive-radical kernel of Whittaker–Watson §22.32, p. 501, totalized by
zero outside `(0, 1)`. The parameter is the complementary modulus in the theorem below. -/
def whittakerWatsonCentralKernel (c t : ℝ) : ℝ :=
  if 0 < t ∧ t < 1 then 1 / (Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - c ^ 2 * t ^ 2)) else 0

/-- The outer positive-radical kernel of Whittaker–Watson §22.32, p. 501, totalized by
zero outside `(1, 1 / k)`, including both singular endpoints. -/
def whittakerWatsonOuterKernel (k s : ℝ) : ℝ :=
  if 1 < s ∧ s < 1 / k then 1 / (Real.sqrt (s ^ 2 - 1) * Real.sqrt (1 - k ^ 2 * s ^ 2)) else 0

/-- Whittaker–Watson complementary elliptic integral identity, with integrability and
improper-integral interpretation. Source: third edition (1920), §22.32, printed p. 501,
local `literature/Whittaker-Watson-Course-Modern-Analysis-3rd-1920.pdf`, PDF p. 515.

Both integrals use real Lebesgue volume and the signed interval-integral convention. The two
last clauses take the lower cutoff to the left endpoint from above and the upper cutoff to
the right endpoint from below, independently, for the original interior formulas. They
express the classical improper integrals, rather than assigning the endpoint singular limits
the finite totalized values. The real square roots are the source's positive radicals.

Checked proof following the matching DAG node:

For 0<k<1 the complementary modulus c satisfies c²=1-k²<1. Apply the central integrability lemma, which is the inverse semicircle weight multiplied by a continuous nonsingular factor.

Use the source substitution sigma(t)=(1-(1-k²)t²)^(-1/2). Its continuous closed-interval extension, endpoint values, positive interior derivative and exact positive-radical cancellation are given by the substitution lemma.

The derivative-weighted pullback of the outer kernel equals the integrable central kernel on (0,1). The monotone change-of-variables integrability equivalence therefore proves genuine outer integrability on 1..1/k. The monotone integral substitution theorem gives the equality of the two signed integrals. Endpoint totalizations do not affect either application.

Apply the interior endpoint-limit theorem separately to the two integrable kernels and their original interior formulas. The inequalities 0<1 and 1<1/k supply the strict endpoint order. This gives both independent two-cutoff improper limits.
-/
theorem whittakerWatsonComplementaryEllipticIntegrals
    (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    let c := Real.sqrt (1 - k ^ 2)
    IntervalIntegrable (whittakerWatsonCentralKernel c) volume 0 1 ∧
      IntervalIntegrable (whittakerWatsonOuterKernel k) volume 1 (1 / k) ∧
      (∫ t in (0 : ℝ)..1, whittakerWatsonCentralKernel c t ∂volume) =
        (∫ s in (1 : ℝ)..(1 / k), whittakerWatsonOuterKernel k s ∂volume) ∧
      Tendsto
        (fun ab : ℝ × ℝ ↦ ∫ t in ab.1..ab.2,
          1 / (Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - c ^ 2 * t ^ 2)) ∂volume)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ)))
        (𝓝 (∫ t in (0 : ℝ)..1, whittakerWatsonCentralKernel c t ∂volume)) ∧
      Tendsto
        (fun ab : ℝ × ℝ ↦ ∫ s in ab.1..ab.2,
          1 / (Real.sqrt (s ^ 2 - 1) * Real.sqrt (1 - k ^ 2 * s ^ 2)) ∂volume)
        ((𝓝[>] (1 : ℝ)) ×ˢ (𝓝[<] (1 / k)))
        (𝓝 (∫ s in (1 : ℝ)..(1 / k), whittakerWatsonOuterKernel k s ∂volume)) := by
  dsimp only
  have hcpos : 0 < 1 - k ^ 2 := by nlinarith
  have hc2 := Real.sq_sqrt hcpos.le
  have hcentral : IntervalIntegrable
      (whittakerWatsonCentralKernel (Real.sqrt (1 - k ^ 2))) volume 0 1 :=
    whittakerWatsonCentralIntegrable _ (by nlinarith [sq_pos_of_pos hk0])
  let σ := fun t : ℝ ↦ (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2))⁻¹
  let σ' := fun t : ℝ ↦ (1 - k ^ 2) * t /
    (Real.sqrt (1 - (1 - k ^ 2) * t ^ 2)) ^ 3
  obtain ⟨hσ, hσ0, hσ1, hs⟩ := whittakerWatsonSubstitution k hk0 hk1
  change σ 0 = 1 at hσ0
  change σ 1 = 1 / k at hσ1
  have hσc : ContinuousOn σ (Set.uIcc 0 1) := by
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hσ
  have hderiv : ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt σ (σ' t) t := by
    simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using
      fun t ht ↦ (hs t ht).1
  have hnonneg : ∀ t ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ σ' t := by
    simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using
      fun t ht ↦ (hs t ht).2.1
  have hkernel : ∀ t ∈ Set.uIoo (0 : ℝ) 1,
      ((whittakerWatsonOuterKernel k) ∘ σ) t * σ' t =
        whittakerWatsonCentralKernel (Real.sqrt (1 - k ^ 2)) t := by
    intro t ht
    rw [Set.uIoo_of_le zero_le_one] at ht
    have hst := hs t ht
    have hlo : 1 < σ t := hst.2.2.1
    have hhi : σ t < 1 / k := hst.2.2.2.1
    simp only [Function.comp_apply, whittakerWatsonOuterKernel,
      whittakerWatsonCentralKernel, hlo, hhi, ht.1, ht.2, and_self, ite_true]
    exact hst.2.2.2.2
  have hpull : IntervalIntegrable
      (fun t ↦ σ' t • ((whittakerWatsonOuterKernel k) ∘ σ) t) volume 0 1 := by
    apply hcentral.congr_uIoo
    intro t ht
    simpa only [smul_eq_mul, mul_comm] using (hkernel t ht).symm
  have houter : IntervalIntegrable (whittakerWatsonOuterKernel k) volume 1 (1 / k) := by
    have h := (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
      hσc hderiv hnonneg).mp hpull
    simpa only [hσ0, hσ1] using h
  have heq : (∫ t in (0 : ℝ)..1,
      whittakerWatsonCentralKernel (Real.sqrt (1 - k ^ 2)) t) =
      ∫ s in (1 : ℝ)..(1 / k), whittakerWatsonOuterKernel k s := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := whittakerWatsonOuterKernel k) hσc hderiv hnonneg
    rw [hσ0, hσ1] at h
    exact (intervalIntegral.integral_congr_uIoo hkernel).symm.trans h
  refine ⟨hcentral, houter, heq, ?_, ?_⟩
  · apply intervalIntegralInteriorEndpointLimit zero_lt_one hcentral
    intro t ht
    simp only [whittakerWatsonCentralKernel, ht.1, ht.2, and_self, ite_true]
  · apply intervalIntegralInteriorEndpointLimit ((lt_div_iff₀ hk0).2 (by simpa using hk1)) houter
    intro t ht
    simp only [whittakerWatsonOuterKernel, ht.1, ht.2, and_self, ite_true]

end

end HolomorphicAnosov.Analysis
