import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Thickening

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/-- Reflected mollifications of one test function eventually have one compact
support inside its open domain. Neither positivity nor normalization of the
kernel is required for this support assertion.

Source: Dyatlov, *Lecture notes for 18.155*, proof of Theorem 6.7, p.73,
(6.19) and the support condition in (6.25); the compact collar inside an open
set is Mathlib `IsCompact.exists_cthickening_subset_open`.
Proof: take a positive closed collar K of the compact support of φ inside U.
If both factors in the integrand are nonzero, p belongs to the support of φ
and the support bound on ρ gives ‖p-y‖ ≤ ε. For sufficiently small positive
ε this puts y in K. Consequently the integral is zero off K. Since K is
closed, it contains the topological support of each eventual mollification.
The construction also applies to empty supports and dimension zero. -/
theorem testFunction_reflected_mollifier_eventual_support
    {m : ℕ} (U : Opens (EuclideanSpace ℝ (Fin m)))
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (φ : TestFunction U ℂ ⊤) (η : ℝ → TestFunction U ℂ ⊤)
    (hη : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
      η ε y = ∫ p, φ p * ((((ε⁻¹) ^ m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ))) :
    ∃ K : Compacts (EuclideanSpace ℝ (Fin m)),
      (K : Set (EuclideanSpace ℝ (Fin m))) ⊆ U ∧
      tsupport (φ : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        tsupport (η ε : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K := by
  obtain ⟨δ, hδ, hKU⟩ := φ.hasCompactSupport.exists_cthickening_subset_open
    U.isOpen φ.tsupport_subset
  let K : Compacts (EuclideanSpace ℝ (Fin m)) :=
    ⟨Metric.cthickening δ (tsupport (φ : EuclideanSpace ℝ (Fin m) → ℂ)),
      φ.hasCompactSupport.cthickening⟩
  refine ⟨K, hKU, Metric.self_subset_cthickening _, ?_⟩
  filter_upwards [hη, Ioo_mem_nhdsGT hδ] with ε hε hεδ
  apply closure_minimal _ K.isCompact.isClosed
  intro y hy
  by_contra hyK
  have hz : η ε y = 0 := by
    rw [hε y]
    apply integral_eq_zero_of_ae
    filter_upwards [] with p
    by_cases hp : φ p = 0
    · simp [hp]
    have hpL : p ∈ tsupport (φ : EuclideanSpace ℝ (Fin m) → ℂ) :=
      subset_tsupport _ hp
    have hr : ρ (ε⁻¹ • (p - y)) = 0 := by
      by_contra hr
      have hb := hρ_support (subset_tsupport _ hr)
      have hn : ‖p - y‖ ≤ ε := by
        have hb' : ε⁻¹ * ‖p - y‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_eq_abs, abs_of_pos hεδ.1] using hb
        exact (inv_mul_le_iff₀ hεδ.1).mp hb' |>.trans_eq (mul_one ε)
      apply hyK
      exact Metric.mem_cthickening_of_dist_le y p δ _ hpL
        (by simpa [dist_eq_norm, norm_sub_rev] using hn.trans hεδ.2.le)
    simp [hr]
  exact hy hz

end HolomorphicAnosov.Analysis.Distribution
