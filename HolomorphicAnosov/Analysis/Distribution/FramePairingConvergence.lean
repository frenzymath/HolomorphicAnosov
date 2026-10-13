import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform frame-coefficient convergence implies convergence of regular pairings

Source: Zhang, Codimension-one holomorphic Anosov diffeomorphisms,
Lemma 4.3, printed p.16, final distributional convergence argument.
DAG node: `analysis.frame_pairing_convergence_g7`.
-/

open Bundle Filter MeasureTheory TopologicalSpace Set
open scoped ContDiff Manifold Topology _root_.Topology

namespace HolomorphicAnosov.DistributionalSection

/-- Uniform coefficient error on the support of a test controls its regular pairing.

Source: Zhang, Lemma 4.3, printed p.16.
Proof: Each coefficient is continuous on the original frame domain, by continuity
of the section, inverse chart, and trivialization. Multiplication by the compactly
supported test is therefore integrable. The test vanishes outside the domain,
so the regular pairings are the corresponding whole-space integrals. Their
difference is the integral of the coefficient difference times the test. Its
norm is at most εₙ times the integral of the test norm: use the given estimate
on the support, and zero of the test off that support. This fixed integral is
finite. The upper bound tends to zero, and the squeeze theorem gives convergence
of the difference and hence of the pairings. The zero test and empty domain
are included without assuming positive errors or nonempty support.
-/
theorem frame_regular_pairing_tendsto {d r : ℕ} {X : Type*}
    [TopologicalSpace X] {V : X → Type*}
    [TopologicalSpace (TotalSpace (Fin r → ℂ) V)]
    (sn : ℕ → ∀ x, V x) (s : ∀ x, V x)
    (hsn : ∀ n, Continuous (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (sn n x)))
    (hs : Continuous (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s x)))
    (c : OpenPartialHomeomorph X (Fin d → ℂ))
    (e : Trivialization (Fin r → ℂ) (TotalSpace.proj : TotalSpace (Fin r → ℂ) V → X))
    (k : Fin r) (φ : TestFunction (frameDomain c e) ℂ ⊤)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ z ∈ tsupport φ,
      ‖coefficient (sn n) c e k z - coefficient s c e k z‖ ≤ ε n) :
    Tendsto (fun n ↦ regularPairing (frameDomain c e) (coefficient (sn n) c e k) φ)
      atTop (𝓝 (regularPairing (frameDomain c e) (coefficient s c e k) φ)) := by
  have hcoef (t : ∀ x, V x)
      (ht : Continuous (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (t x))) :
      ContinuousOn (coefficient t c e k) (frameDomain c e) := by
    apply (continuous_apply k).continuousOn.comp
      (continuous_snd.continuousOn.comp (e.continuousOn.comp
        (ht.continuousOn.comp (c.continuousOn_symm.mono inter_subset_left)
          (fun _ _ ↦ mem_univ _)) (fun z hz ↦ ?_)) (fun _ _ ↦ mem_univ _))
      (fun _ _ ↦ mem_univ _)
    exact e.mem_source.mpr hz.2
  have hint (t : ∀ x, V x)
      (ht : Continuous (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (t x))) :
      Integrable (fun z ↦ coefficient t c e k z * φ z) volume := by
    have hi := φ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
      ((hcoef t ht).locallyIntegrableOn (frameDomain c e).isOpen.measurableSet)
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hi
  have heq (t : ∀ x, V x) :
      regularPairing (frameDomain c e) (coefficient t c e k) φ =
        ∫ z, coefficient t c e k z * φ z ∂volume := by
    rw [regularPairing, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    simp [φ.zero_on_compl hz]
  have hφint : Integrable (fun z ↦ ‖φ z‖) volume :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  have hzero : Tendsto
      (fun n ↦ regularPairing (frameDomain c e) (coefficient (sn n) c e k) φ -
        regularPairing (frameDomain c e) (coefficient s c e k) φ) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n ↦ ε n * ∫ z, ‖φ z‖ ∂volume)
    · filter_upwards [hbound] with n hn
      rw [heq, heq, ← integral_sub (hint (sn n) (hsn n)) (hint s hs)]
      calc
        ‖∫ z, coefficient (sn n) c e k z * φ z - coefficient s c e k z * φ z ∂volume‖
            ≤ ∫ z, ε n * ‖φ z‖ ∂volume := by
          apply norm_integral_le_of_norm_le (hφint.const_mul (ε n))
          filter_upwards [] with z
          rw [← sub_mul, norm_mul]
          by_cases hz : z ∈ tsupport φ
          · exact mul_le_mul_of_nonneg_right (hn z hz) (norm_nonneg _)
          · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, mul_zero, mul_zero]
        _ = ε n * ∫ z, ‖φ z‖ ∂volume := integral_const_mul _ _
    · simpa using hε.mul_const (∫ z, ‖φ z‖ ∂volume)
  simpa only [sub_add_cancel, zero_add] using
    hzero.add_const (regularPairing (frameDomain c e) (coefficient s c e k) φ)

end HolomorphicAnosov.DistributionalSection

