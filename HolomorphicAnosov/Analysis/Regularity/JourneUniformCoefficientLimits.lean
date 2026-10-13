import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
This file proves convergence and reconstruction bounds for finite coefficient arrays (Journé, 1988).
-/ 

noncomputable section
open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- Uniform geometric coefficient bounds give coefficient limits and bounds for any finite weighted reconstruction. (Journé, 1988) -/
theorem uniform_geometric_coefficient_limits
    {A ι : Type*} [Fintype ι]
    (c : A → ℕ → ι → ℝ) (C r : ι → ℝ)
    (hr : ∀ i, r i < 1)
    (hstep : ∀ a m i, |c a m i - c a (m + 1) i| ≤ C i * r i ^ m) :
    ∃ l : A → ι → ℝ,
      (∀ a i, Tendsto (fun m ↦ c a m i) atTop (𝓝 (l a i))) ∧
      (∀ a m i, |c a m i - l a i| ≤ C i * r i ^ m / (1 - r i)) ∧
      (∀ a m (w : ι → ℝ),
        |∑ i, (c a m i - l a i) * w i| ≤
          ∑ i, (C i * r i ^ m / (1 - r i)) * |w i|) := by
  let l : A → ι → ℝ := fun a i ↦ limUnder atTop (fun m ↦ c a m i)
  have hdist (a : A) (i : ι) (m : ℕ) :
      dist (c a m i) (c a (m + 1) i) ≤ C i * r i ^ m := by
    simpa only [Real.dist_eq] using hstep a m i
  have hlim (a : A) (i : ι) : Tendsto (fun m ↦ c a m i) atTop (𝓝 (l a i)) :=
    (cauchySeq_of_le_geometric (r i) (C i) (hr i) (hdist a i)).tendsto_limUnder
  have htail (a : A) (m : ℕ) (i : ι) :
      |c a m i - l a i| ≤ C i * r i ^ m / (1 - r i) := by
    simpa only [Real.dist_eq] using
      dist_le_of_le_geometric_of_tendsto (r i) (C i) (hr i) (hdist a i) (hlim a i) m
  refine ⟨l, hlim, htail, ?_⟩
  intro a m w
  calc
    |∑ i, (c a m i - l a i) * w i| ≤ ∑ i, |(c a m i - l a i) * w i| :=
      by simpa only [Real.norm_eq_abs] using
        norm_sum_le Finset.univ (fun i ↦ (c a m i - l a i) * w i)
    _ = ∑ i, |c a m i - l a i| * |w i| := by simp only [abs_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (htail a m i) (abs_nonneg _)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
