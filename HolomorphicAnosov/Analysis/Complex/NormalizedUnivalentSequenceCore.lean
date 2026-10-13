import HolomorphicAnosov.Analysis.Complex.NormalizedUnivalentOmittedValue
import HolomorphicAnosov.Analysis.Complex.ConwayMontelCaratheodoryOmittedValues
import HolomorphicAnosov.Analysis.Complex.MinimumModulusOnSphere
import HolomorphicAnosov.Analysis.Complex.PuncturedBallPreconnectedG9
import HolomorphicAnosov.Analysis.Complex.UnivalentNonconstantLimit
import Mathlib.Analysis.Complex.UnitDisc.Basic

namespace HolomorphicAnosov

open Set Metric Filter
open scoped _root_.Topology

/-- Lyubich's compact-open extraction for normalized univalent disk maps.

Source: Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*,
§4.4 Theorem 4.12 and Lemma 4.13, pp.113–114; §4.3 Theorem 4.8, pp.111–112.
The extension agrees with each disk map, including the limiting map.

Proof: choose an omitted unit-circle value for each map and divide by that value.
The resulting maps omit both zero and one on the punctured disk, so Montel gives
finite compact convergence or uniform escape to infinity. Escape is impossible:
the minimum-modulus principle applied to the rotated map minus one supplies a
point on the half-unit circle where its modulus is at most its value one at zero.
In the finite case compact convergence bounds every interior circle, including the
finitely many initial maps. Rotation preserves modulus. The maximum principle
therefore bounds the original maps on every compact subset of the full disk.
Bounded holomorphic normality gives a further subsequence with holomorphic limit.
Convergence of derivatives preserves derivative modulus one, ruling out a constant
limit; Hurwitz gives injectivity. Restrict the limit to the disk and use extension
agreement to transport holomorphicity and derivative normalization.

The minimum-modulus step is the agent-written reciprocal maximum-principle
alternative to Lyubich's winding-number argument, already supplied by
`minimum_modulus_on_sphere`. No assertion is made about the extension outside the disk. -/
theorem normalized_univalent_sequence_extraction_core
    (ext : C(Complex.UnitDisc, ℂ) → ℂ → ℂ)
    (hext : ∀ f (z : Complex.UnitDisc), ext f z = f z)
    (u : ℕ → C(Complex.UnitDisc, ℂ))
    (hdiff : ∀ n, DifferentiableOn ℂ (ext (u n)) (ball (0 : ℂ) 1))
    (hinj : ∀ n, Function.Injective (u n))
    (hzero : ∀ n, (u n) 0 = 0)
    (hnorm : ∀ n, ‖deriv (ext (u n)) 0‖ = 1) :
    ∃ v : C(Complex.UnitDisc, ℂ),
      DifferentiableOn ℂ (ext v) (ball (0 : ℂ) 1) ∧
      Function.Injective v ∧ v 0 = 0 ∧ ‖deriv (ext v) 0‖ = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ K : Set Complex.UnitDisc, IsCompact K →
          TendstoUniformlyOn (fun n z ↦ u (φ n) z) v atTop K := by
  classical
  let F : ℕ → ℂ → ℂ := fun n ↦ ext (u n)
  have hF0 : ∀ n, F n 0 = 0 := fun n ↦ (hext (u n) 0).trans (hzero n)
  have hFi : ∀ n, InjOn (F n) (ball 0 1) := by
    intro n z hz w hw heq
    exact congrArg (fun z : Complex.UnitDisc ↦ (z : ℂ))
      (hinj n (show u n ⟨z, hz⟩ = u n ⟨w, hw⟩ by
        rw [← hext (u n) ⟨z, hz⟩, ← hext (u n) ⟨w, hw⟩]
        exact heq))
  choose a ha hoa using
    (fun n ↦ normalized_univalent_omits_unit_value (F n) (hdiff n) (hFi n)
      (hF0 n) (hnorm n))
  have ha0 : ∀ n, a n ≠ 0 := by
    intro n h
    have := ha n
    simp [h] at this
  let H : ℕ → ℂ → ℂ := fun n z ↦ F n z / a n
  have hHd : ∀ n, DifferentiableOn ℂ (H n) (ball 0 1) :=
    fun n ↦ (hdiff n).div_const (a n)
  have hHnorm : ∀ n z, ‖H n z‖ = ‖F n z‖ := by
    intro n z
    simp [H, ha n]
  have hH0 : ∀ n, H n 0 = 0 := by intro n; simp [H, hF0]
  have hH1 : ∀ n z, z ∈ ball (0 : ℂ) 1 → H n z ≠ 1 := by
    intro n z hz heq
    exact hoa n z hz ((div_eq_one_iff_eq (ha0 n)).mp heq)
  let G : Set ℂ := ball (0 : ℂ) 1 \ {0}
  obtain ⟨ψ, hψ, hfinite | hinfinite⟩ :=
    conway_montel_caratheodory_omitted_values_g2
      (isOpen_ball.sdiff isClosed_singleton) (punctured_ball_preconnected_g9 1 zero_lt_one)
      H (fun n ↦ (hHd n).mono sdiff_subset) (by
        intro n z hz
        refine ⟨?_, hH1 n z hz.1⟩
        intro heq
        have hz0 : F n z = F n 0 := by
          rw [hF0]
          exact (div_eq_zero_iff).mp heq |>.resolve_right (ha0 n)
        exact hz.2 (hFi n hz.1 (mem_ball_self zero_lt_one) hz0))
  · obtain ⟨h, hhd, hlim⟩ := hfinite
    have hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ ball (0 : ℂ) 1 →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖F (ψ n) z‖ ≤ M := by
      intro K hK hKD
      rcases K.eq_empty_or_nonempty with rfl | hKne
      · exact ⟨0, le_rfl, by simp⟩
      obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
      obtain ⟨r, hzr, hr1⟩ := exists_between (mem_ball_zero_iff.mp (hKD hz₀))
      have hr : 0 < r := (norm_nonneg z₀).trans_lt hzr
      have hSG : sphere (0 : ℂ) r ⊆ G := by
        intro z hz
        have hzn : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
        exact ⟨mem_ball_zero_iff.mpr (hzn.trans_lt hr1), by
          simpa only [mem_singleton_iff] using (norm_pos_iff.mp (hzn.symm ▸ hr))⟩
      obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn
        (hhd.continuousOn.mono hSG)
      obtain ⟨N, hN⟩ := eventually_atTop.mp
        ((Metric.tendstoUniformlyOn_iff.mp (hlim _ (isCompact_sphere _ _) hSG))
          1 zero_lt_one)
      have hBD : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
      choose b hb using (fun n ↦ (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
        ((hdiff (ψ n)).continuousOn.mono hBD))
      let M : ℝ := max 0 (B + 1) + ∑ i ∈ Finset.range N, max 0 (b i)
      have hM : 0 ≤ M := add_nonneg (le_max_left _ _) (Finset.sum_nonneg (by simp))
      refine ⟨M, hM, ?_⟩
      intro n z hz
      have hzball : z ∈ ball (0 : ℂ) r :=
        mem_ball_zero_iff.mpr ((hmax hz).trans_lt hzr)
      by_cases hn : n < N
      · have hbM : b n ≤ M := by
          have hs : max 0 (b n) ≤ ∑ i ∈ Finset.range N, max 0 (b i) :=
            Finset.single_le_sum (fun i hi ↦ le_max_left _ _) (Finset.mem_range.mpr hn)
          exact (le_max_right _ _).trans (hs.trans (le_add_of_nonneg_left (le_max_left _ _)))
        exact (hb n z (ball_subset_closedBall hzball)).trans hbM
      · apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
          ((hdiff (ψ n)).diffContOnCl_ball hBD) _ (subset_closure hzball)
        intro w hw
        rw [frontier_ball _ hr.ne'] at hw
        have hd := hN n (Nat.le_of_not_gt hn) w hw
        have hwB := hB w hw
        have htri : ‖H (ψ n) w‖ ≤ dist (h w) (H (ψ n) w) + ‖h w‖ := by
          simpa only [dist_zero_right, dist_comm] using dist_triangle (H (ψ n) w) (h w) 0
        rw [hHnorm] at htri
        have hBM : B + 1 ≤ M := (le_max_right _ _).trans
          (le_add_of_nonneg_right (Finset.sum_nonneg (by simp)))
        linarith
    obtain ⟨φ, hφ, f, hfd, hflim⟩ := conway_bounded_holomorphic_sequence_normality_g2
      isOpen_ball (fun n ↦ F (ψ n)) (fun n ↦ hdiff (ψ n)) hbound
    have hloc : TendstoLocallyUniformlyOn (fun n ↦ F (ψ (φ n))) f atTop (ball 0 1) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mpr
        (fun K hKD hK ↦ hflim K hK hKD)
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
    have hf0 : f 0 = 0 := by
      apply tendsto_nhds_unique (hloc.tendsto_at h0)
      simpa only [hF0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0))
    have hfnorm : ‖deriv f 0‖ = 1 := by
      apply tendsto_nhds_unique
        (((hloc.deriv (Eventually.of_forall (fun n ↦ hdiff (ψ (φ n)) ))
          isOpen_ball).tendsto_at h0).norm)
      simpa only [Function.comp_apply, F, hnorm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
    have hfi : InjOn f (ball 0 1) := by
      apply univalent_nonconstant_limit isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
        (fun n ↦ hdiff (ψ (φ n))) (fun n ↦ hFi (ψ (φ n)))
        (fun K hKD hK ↦ hflim K hK hKD)
      rintro ⟨c, hc⟩
      have heq : f =ᶠ[𝓝 0] fun _ ↦ c :=
        Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0) hc
      have hd : deriv f 0 = 0 := by rw [heq.deriv_eq]; exact deriv_const 0 c
      simp [hd] at hfnorm
    let v : C(Complex.UnitDisc, ℂ) := ⟨fun z ↦ f z, hfd.continuousOn.domRestrict⟩
    have heq : EqOn (ext v) f (ball 0 1) := fun z hz ↦ hext v ⟨z, hz⟩
    refine ⟨v, hfd.congr heq, ?_, hf0, ?_, ψ ∘ φ, hψ.comp hφ, ?_⟩
    · intro z w hzw
      exact Complex.UnitDisc.coe_injective (hfi z.property w.property hzw)
    · rwa [(Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0) heq).deriv_eq]
    · intro K hK
      have himage := hflim (Subtype.val '' K) (hK.image Complex.UnitDisc.continuous_coe)
        (by rintro z ⟨w, hw, rfl⟩; exact w.property)
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp himage ε hε] with n hn
      intro z hz
      change dist (f z) (u (ψ (φ n)) z) < ε
      simpa only [F, hext] using hn z ⟨z, hz, rfl⟩
  · have hSG : sphere (0 : ℂ) (1 / 2) ⊆ G := by
      intro z hz
      have hzn : ‖z‖ = 1 / 2 := by simpa only [mem_sphere, dist_zero_right] using hz
      refine ⟨mem_ball_zero_iff.mpr (by linarith), ?_⟩
      simpa only [mem_singleton_iff] using (norm_pos_iff.mp (show 0 < ‖z‖ by linarith))
    obtain ⟨N, hN⟩ := hinfinite _ (isCompact_sphere (0 : ℂ) (1 / 2)) hSG 3 (by norm_num)
    have hBD : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    obtain ⟨z, hz, hsmall⟩ := minimum_modulus_on_sphere 0 (1 / 2) (by norm_num)
      (fun z ↦ H (ψ N) z - 1) (((hHd _).sub_const 1).diffContOnCl_ball hBD)
      (fun z hz ↦ sub_ne_zero.mpr (hH1 _ z (hBD hz)))
    have hlarge := hN N le_rfl z hz
    have htri : ‖H (ψ N) z‖ ≤ ‖H (ψ N) z - 1‖ + 1 := by
      simpa only [norm_one] using norm_le_norm_sub_add (H (ψ N) z) 1
    simp only [hH0, zero_sub, norm_neg, norm_one] at hsmall
    linarith

end HolomorphicAnosov

