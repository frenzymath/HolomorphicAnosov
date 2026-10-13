import HolomorphicAnosov.Analysis.Complex.ConwayBoundedHolomorphicSequenceNormality
import HolomorphicAnosov.Analysis.Complex.HurwitzZeroFreeLimit
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Normality from locally bounded reciprocals

Conway, Functions of One Complex Variable II, XVI §4, Theorem 4.2, p.125,
reciprocal case; Conway I, VII §2, Theorem 2.9 and Corollary 2.6, pp.152–153.
The finite inverse-limit alternative is the elementary extension of that argument.
-/

namespace HolomorphicAnosov

/-- A zero-free holomorphic sequence whose reciprocals are uniformly bounded on every
compact subset has a subsequence converging compact-uniformly to a holomorphic function
or diverging uniformly to infinity on compact subsets.

Source: Conway II, XVI §4, Theorem 4.2, p.125, reciprocal case; Conway I, VII §2,
Theorem 2.9 and Corollary 2.6, pp.152–153. This is an agent-written expansion of
that case, including the alternative where the reciprocal limit has no zero.
Apply bounded holomorphic normality to the reciprocal sequence. Hurwitz makes its
holomorphic limit either identically zero or nowhere zero. In the first case,
uniform convergence below 1/M is exactly divergence of the original norms above M.
In the second, locally uniform convergence is preserved by inversion at the nonzero
continuous limit. The inverse limit is holomorphic, and inversion twice recovers the
original subsequence. Connectedness is used only for Hurwitz; empty domains are allowed.
-/
theorem conway_reciprocal_bounded_normality_g19
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsPreconnected G) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) G)
    (hnz : ∀ n z, z ∈ G → f n z ≠ 0)
    (hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ G →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖(f n z)⁻¹‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ h : ℂ → ℂ, DifferentiableOn ℂ h G ∧
          ∀ K : Set ℂ, IsCompact K → K ⊆ G →
            TendstoUniformlyOn (fun k z ↦ f (φ k) z) h Filter.atTop K) ∨
        (∀ K : Set ℂ, IsCompact K → K ⊆ G →
          ∀ M : ℝ, 0 < M → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
            ∀ z : ℂ, z ∈ K → M < ‖f (φ k) z‖)) := by
  have hinv : ∀ n, DifferentiableOn ℂ (fun z ↦ (f n z)⁻¹) G :=
    fun n ↦ (hf n).inv (hnz n)
  obtain ⟨φ, hφ, g, hg, hconv⟩ :=
    conway_bounded_holomorphic_sequence_normality_g2 hG _ hinv hbound
  have hH := conway_hurwitz_zero_free_limit hG hconn
    (fun n ↦ hinv (φ n)) (fun n z hz ↦ inv_ne_zero (hnz (φ n) z hz))
    (fun K hKG hK ↦ hconv K hK hKG)
  refine ⟨φ, hφ, ?_⟩
  rcases hH.2 with hzero | hnonzero
  · apply Or.inr
    intro K hK hKG M hM
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp (hconv K hK hKG) (M⁻¹) (inv_pos.mpr hM))
    refine ⟨k₀, fun k hk z hz ↦ ?_⟩
    have hsmall := hk₀ k hk z hz
    rw [hzero z (hKG hz), dist_zero_left, norm_inv] at hsmall
    exact (inv_lt_inv₀ (norm_pos_iff.mpr (hnz (φ k) z (hKG hz))) hM).mp hsmall
  · apply Or.inl
    refine ⟨fun z ↦ (g z)⁻¹, hg.inv hnonzero, ?_⟩
    have hlocal := (tendstoLocallyUniformlyOn_iff_forall_isCompact hG).mpr
      (fun K hKG hK ↦ hconv K hK hKG)
    have hi := hlocal.inv₀ hg.continuousOn hnonzero
    have hi' : TendstoLocallyUniformlyOn (fun k z ↦ f (φ k) z)
        (fun z ↦ (g z)⁻¹) Filter.atTop G := by
      change TendstoLocallyUniformlyOn (fun k z ↦ ((f (φ k) z)⁻¹)⁻¹)
        (fun z ↦ (g z)⁻¹) Filter.atTop G at hi
      simpa only [inv_inv] using hi
    intro K hK hKG
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hG).mp hi' K hKG hK

end HolomorphicAnosov

