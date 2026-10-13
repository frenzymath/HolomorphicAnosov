import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Local_cutoff_product_smooth
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Local_cutoff_product_dbar
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernelSupport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffDbarSmoothSupport

/-!
# LocalCutoffBmRepresentation

Source: Demailly, Complex Analytic and Differential Geometry (2012), I §3.E (3.29), p.28, first
displayed cutoff identity, specialized to scalar degree zero; scalar normalization from I
(3.23)–(3.26), pp.26–27.
DAG node: `analysis.dbar_helper_local_cutoff_bm_representation_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
In positive complex dimension, let a smooth test cutoff have support in an open domain Q, and let
f be smooth and antiholomorphically closed on Q. At every point z where the cutoff equals one,
f(z) equals the integral over Q of the normalized scalar cutoff Bochner–Martinelli kernel times f.

Source: Demailly (2012), I §3.E (3.29), p.28, first displayed cutoff identity, specialized to
scalar degree zero; scalar normalization from I (3.23)–(3.26), pp.26–27.

Proof: The cutoff product is globally smooth and compactly supported. Apply the scalar
compact-support Bochner–Martinelli formula to it. Its antiholomorphic derivative equals the cutoff
derivative times f, since the antiholomorphic derivative of f vanishes on Q and the cutoff
vanishes locally outside its support. Factor f from the finite coordinate sum and move the
constant normalization inside the integral. The cutoff equals one at z, giving f(z) on the left.
The separated kernel is supported in the cutoff support, which lies in Q, so the integral over the
whole space equals the integral over Q.
-/
theorem local_cutoff_bm_representation {n : ℕ} (hn : 1 ≤ n)
    (U Q : Opens (Fin n → ℂ)) (ψ : TestFunction U ℂ ⊤)
    (hψQ : tsupport (ψ : (Fin n → ℂ) → ℂ) ⊆ Q)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiffOn ℝ ∞ f (Q : Set _))
    (hbar : ∀ x ∈ Q, ∀ j, antiholomorphicPartial f j x = 0)
    (z : Fin n → ℂ) (hz : ψ z = 1) :
    f z = ∫ y in (Q : Set _),
      bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j) z y * f y := by
  obtain ⟨hsm, hcompact⟩ := local_cutoff_product_smooth U Q ψ hψQ f hf
  obtain ⟨_, _, hformula, _⟩ := scalar_bochnermartinelli_compact_support hn
    (fun x ↦ ψ x * f x) hsm hcompact z
  have hderiv := local_cutoff_product_dbar U Q ψ hψQ f hf hbar
  have hsum (y : Fin n → ℂ) :
      (∑ j : Fin n, scalarBochnerMartinelliKernel j z y *
        antiholomorphicPartial (fun x ↦ ψ x * f x) j y) =
      (∑ j : Fin n, scalarBochnerMartinelliKernel j z y *
        antiholomorphicPartial ψ j y) * f y := by
    simp only [hderiv, Finset.sum_mul, mul_assoc]
  rw [hz, one_mul] at hformula
  calc
    f z = ∫ y, bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j) z y * f y := by
      rw [hformula, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [hsum]
      simp only [bmSeparatedKernel, mul_assoc]
    _ = ∫ y in (Q : Set _),
        bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j) z y * f y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hsupp := bm_separated_kernel_support
        (fun j ↦ antiholomorphicPartial ψ j) _ (isClosed_tsupport ψ)
        (fun j ↦ (cutoff_dbar_smooth_support U ψ j).2) z
      have hzero : bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j) z y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy' ↦ hy (hψQ (hsupp hy')))
      simp only [hzero, zero_mul]


end HolomorphicAnosov.Analysis.Distribution
