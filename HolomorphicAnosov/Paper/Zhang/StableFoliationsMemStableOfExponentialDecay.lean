import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped ContDiff Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
namespace StableFoliationsSupport

/-- For complementary stable and unstable subspaces with exponential contraction and inverse
expansion bounds, every exponentially decaying vector lies in the stable subspace. (HPS, Lemma
2.7, p.9; Ghys, Lemma 2.1, p.589) -/
theorem mem_stable_of_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    (S U : Submodule ℝ E) (hcompl : IsCompl S U)
    (D : ∀ n, E →ₗ[ℝ] F n) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : ∀ n, ∀ s ∈ S, ‖D n s‖ ≤ C * r ^ n * ‖s‖)
    (hu : ∀ n, ∀ u ∈ U, ‖u‖ ≤ C * r ^ n * ‖D n u‖)
    (v : E) (hv : ∀ n, ‖D n v‖ ≤ C * r ^ n * ‖v‖) : v ∈ S := by
  obtain ⟨s, u, hsu, _⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
  have hbound : ∀ n, ‖(u : E)‖ ≤
      C * r ^ n * (C * r ^ n * ‖v‖ + C * r ^ n * ‖(s : E)‖) := by
    intro n
    have hDu : D n (u : E) = D n v - D n (s : E) := by
      rw [← hsu, map_add, add_sub_cancel_left]
    calc
      ‖(u : E)‖ ≤ C * r ^ n * ‖D n (u : E)‖ := hu n u u.property
      _ ≤ C * r ^ n * (‖D n v‖ + ‖D n (s : E)‖) := by
        rw [hDu]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (mul_nonneg hC (pow_nonneg hr _))
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hv n) (hs n s s.property))
        (mul_nonneg hC (pow_nonneg hr _))
  have hpow : Tendsto (fun n : ℕ ↦ C * r ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul C
  have hlim : Tendsto (fun n : ℕ ↦
      C * r ^ n * (C * r ^ n * ‖v‖ + C * r ^ n * ‖(s : E)‖)) atTop (𝓝 0) := by
    simpa using hpow.mul ((hpow.mul_const ‖v‖).add (hpow.mul_const ‖(s : E)‖))
  have hu0 : (u : E) = 0 := norm_eq_zero.mp
    (le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)) (norm_nonneg _))
  rw [← hsu, hu0, add_zero]
  exact s.property

end StableFoliationsSupport
end HolomorphicAnosov
