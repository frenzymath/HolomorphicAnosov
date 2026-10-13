import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsMemStableOfExponentialDecay

noncomputable section
open scoped ContDiff Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
namespace StableFoliationsSupport

/-- An operator preserving derivative-growth norms preserves the stable subspace of a complementary
splitting with exponential contraction and inverse expansion bounds. (Ghys, Lemma 2.1) -/
theorem stable_invariant_of_equal_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    (S U : Submodule ℝ E) (hcompl : IsCompl S U)
    (D : ∀ n, E →ₗ[ℝ] F n) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : ∀ n, ∀ s ∈ S, ‖D n s‖ ≤ C * r ^ n * ‖s‖)
    (hu : ∀ n, ∀ u ∈ U, ‖u‖ ≤ C * r ^ n * ‖D n u‖)
    (J : E → E) (hJ : ∀ v, ‖J v‖ = ‖v‖)
    (hDJ : ∀ n v, ‖D n (J v)‖ = ‖D n v‖) :
    ∀ v ∈ S, J v ∈ S := by
  intro v hv
  apply mem_stable_of_exponential_decay S U hcompl D C r hC hr hr1 hs hu (J v)
  intro n
  rw [hDJ, hJ]
  exact hs n v hv

end StableFoliationsSupport
end HolomorphicAnosov
