import HolomorphicAnosov.Analysis.WellsForwardWeightedRecurrence
import HolomorphicAnosov.Analysis.WellsForwardSmoothSequences
import HolomorphicAnosov.Analysis.WellsBackwardSmoothSequences
import HolomorphicAnosov.Analysis.WellsBackwardWeightedRecurrence
import HolomorphicAnosov.Analysis.WellsC0SequenceShifts
import HolomorphicAnosov.Analysis.WellsWeightedC0Composition
import HolomorphicAnosov.Paper.HPS.LocalGraphSmallness
import HolomorphicAnosov.Paper.HPS.NormalizedZeroBounded
import HolomorphicAnosov.Paper.HPS.StableBoundedOrbitCapture
import HolomorphicAnosov.Paper.HPS.BackwardWeightedOrbitUniqueness

/-! This file develops the constructions and results stated below. -/

open Filter
open scoped Topology _root_.Topology ContDiff ZeroAtInfty

namespace HolomorphicAnosov

/-- Under the stated contraction hypotheses, the local strong stable and unstable sets are smooth graphs characterized by the corresponding normalized bounded orbits, with local invariance and uniqueness. (Hirsch–Pugh–Shub, Theorem 5.1 and Corollary 5.4; Wells, pp. 285–291) -/

theorem hps_corollary_5_4_local_strong_graphs
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    (T₁ : E₁ ≃L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (ρ s : ℝ) (hρ : 0 < ρ) (hs : 0 < s)
    (r : ℕ∞) (hr : 1 ≤ r)
    (ha : ‖T₁.symm.toContinuousLinearMap‖ < ρ⁻¹)
    (hk : ‖T₂‖ < ρ) :
    let a := ‖T₁.symm.toContinuousLinearMap‖
    let k := ‖T₂‖
    let B := Metric.ball (0 : E₁ × E₂) s
    ∃ ε : ℝ, 0 < ε ∧
      2 * a * ε < 1 ∧
      a / (1 - a * ε) < ρ⁻¹ ∧ k + ε < ρ ∧
      (a ≠ 0 → a⁻¹ - 2 * ε > ρ) ∧
      (a < 1 → a / (1 - a * ε) < 1) ∧
      (k < 1 → k + ε < 1 ∧ k + 2 * ε < min ρ 1 ∧
        (a ≠ 0 → a⁻¹ - 4 * ε > ρ)) ∧
      ∀ g : (E₁ × E₂) → (E₁ × E₂),
        ContDiffOn ℝ (r : ℕ∞ω) g B → g 0 = 0 →
        (∀ z ∈ B, ∀ z' ∈ B,
          ‖(g z - (T₁ z.1, T₂ z.2)) -
            (g z' - (T₁ z'.1, T₂ z'.2))‖ ≤ ε * ‖z - z'‖) →
        let backwardBounded := fun z : E₁ × E₂ =>
          ∃ w : ℕ → E₁ × E₂, w 0 = z ∧ (∀ n, w n ∈ B) ∧
            (∀ n, g (w (n + 1)) = w n) ∧
            ∃ M : ℝ, ∀ n, ‖w n‖ / (ρ⁻¹) ^ n ≤ M
        let backwardZero := fun z : E₁ × E₂ =>
          ∃ w : ℕ → E₁ × E₂, w 0 = z ∧ (∀ n, w n ∈ B) ∧
            (∀ n, g (w (n + 1)) = w n) ∧
            Tendsto (fun n => ‖w n‖ / (ρ⁻¹) ^ n) atTop (𝓝 0)
        let forwardBounded := fun z : E₁ × E₂ =>
          ∃ w : ℕ → E₁ × E₂, w 0 = z ∧ (∀ n, w n ∈ B) ∧
            (∀ n, g (w n) = w (n + 1)) ∧
            ∃ M : ℝ, ∀ n, ‖w n‖ / ρ ^ n ≤ M
        let forwardZero := fun z : E₁ × E₂ =>
          ∃ w : ℕ → E₁ × E₂, w 0 = z ∧ (∀ n, w n ∈ B) ∧
            (∀ n, g (w n) = w (n + 1)) ∧
            Tendsto (fun n => ‖w n‖ / ρ ^ n) atTop (𝓝 0)
        (a < 1 → ∃ u : E₁ → E₂,
          ContDiffOn ℝ (r : ℕ∞ω) u (Metric.ball 0 s) ∧ u 0 = 0 ∧
          (∀ x ∈ Metric.ball (0 : E₁) s, (x, u x) ∈ B) ∧
          (∀ x ∈ Metric.ball (0 : E₁) s,
            g (x, u x) ∈ B → (g (x, u x)).2 = u (g (x, u x)).1) ∧
          (∀ z ∈ B, (z.2 = u z.1 ↔ backwardBounded z) ∧
            (z.2 = u z.1 ↔ backwardZero z)) ∧
          (∀ (v : E₁ → E₂) (D : Set E₁), IsOpen D → 0 ∈ D →
            D ⊆ Metric.ball 0 s →
            (∀ x ∈ D, backwardBounded (x, v x)) → ∀ x ∈ D, v x = u x)) ∧
        (k < 1 → ∃ v : E₂ → E₁,
          ContDiffOn ℝ (r : ℕ∞ω) v (Metric.ball 0 s) ∧ v 0 = 0 ∧
          (∀ y ∈ Metric.ball (0 : E₂) s, (v y, y) ∈ B) ∧
          (∀ y ∈ Metric.ball (0 : E₂) s,
            g (v y, y) ∈ B ∧ (g (v y, y)).1 = v (g (v y, y)).2) ∧
          (∀ z ∈ B, (z.1 = v z.2 ↔ forwardBounded z) ∧
            (z.1 = v z.2 ↔ forwardZero z)) ∧
          (∀ (u : E₂ → E₁) (D : Set E₂), IsOpen D → 0 ∈ D →
            D ⊆ Metric.ball 0 s →
            (∀ y ∈ D, forwardBounded (u y, y)) → ∀ y ∈ D, u y = v y)) := by
  dsimp
  obtain ⟨ε, hε, hmul, hdiv, hkρ, haρ, ha1, hk1⟩ :=
    hps_local_graph_smallness ‖T₁.symm.toContinuousLinearMap‖ ‖T₂‖ ρ
      (norm_nonneg _) hρ ha hk
  refine ⟨ε, hε, hmul, hdiv, hkρ, haρ, ha1, hk1, ?_⟩
  intro g hg hg0 hrem
  let R : (E₁ × E₂) → (E₁ × E₂) := fun z ↦ g z - (T₁ z.1, T₂ z.2)
  have hR0 : R 0 = 0 := by simp [R, hg0]
  have hRcont : ContDiffOn ℝ (r : ℕ∞ω) R (Metric.ball 0 s) :=
    hg.sub (((T₁.contDiff.comp contDiff_fst).prodMk
      (T₂.contDiff.comp contDiff_snd)).contDiffOn)
  constructor
  · intro haone
    let q : ℝ := max ρ 1
    have hq1 : 1 ≤ q := le_max_right _ _
    have hqρ : ρ ≤ q := le_max_left _ _
    have hq : 0 < q := lt_of_lt_of_le hρ hqρ
    have hden : 0 < 1 - ‖T₁.symm.toContinuousLinearMap‖ * ε := by
      nlinarith [mul_nonneg (norm_nonneg T₁.symm.toContinuousLinearMap) hε.le]
    have haq : ‖T₁.symm.toContinuousLinearMap‖ * q <
        1 - ‖T₁.symm.toContinuousLinearMap‖ * ε := by
      by_cases hρ1 : ρ ≤ 1
      · have hh := (div_lt_iff₀ hden).mp (ha1 haone)
        simpa [q, max_eq_right hρ1] using hh
      · have hh := mul_lt_mul_of_pos_right ((div_lt_iff₀ hden).mp hdiv) hρ
        have hρ1' : 1 < ρ := lt_of_not_ge hρ1
        calc
          ‖T₁.symm.toContinuousLinearMap‖ * q = ρ * ‖T₁.symm.toContinuousLinearMap‖ := by
            simp [q, max_eq_left hρ1'.le, mul_comm]
          _ < ρ⁻¹ * (1 - ‖T₁.symm.toContinuousLinearMap‖ * ε) * ρ := by
            nlinarith [hh]
          _ = 1 - ‖T₁.symm.toContinuousLinearMap‖ * ε := by
            field_simp
    have hsmall : max (‖T₁.symm.toContinuousLinearMap‖ * (q + ε))
        (q⁻¹ * (‖T₂‖ + ε)) < 1 := by
      apply max_lt
      · nlinarith
      · rw [mul_comm, ← div_eq_mul_inv, div_lt_one hq]
        exact lt_of_lt_of_le hkρ hqρ
    obtain ⟨C, hC, hC0, hCLip, hCsmooth, _⟩ :=
      Analysis.wells_weighted_c0_composition s q ε r R hs hq1 hε.le hr
        hRcont hR0 hrem
    obtain ⟨f, hfsmooth, hf0, heq, hfLip, hfUnique⟩ :=
      Analysis.wells_backward_smooth_sequences T₁.symm.toContinuousLinearMap T₂
        q s ε hq hs hε.le r hr hsmall C hC0 hCsmooth hCLip
    let u : E₁ → E₂ := fun p ↦ (f p 0).2
    let ev₀ : C₀(ℕ, E₁ × E₂) →L[ℝ] (E₁ × E₂) :=
      ({ toFun := fun w ↦ w 0, map_add' := by intros; rfl,
         map_smul' := by intros; rfl } : C₀(ℕ,E₁×E₂) →ₗ[ℝ] (E₁×E₂)).mkContinuous
        1 (fun w ↦ by simpa using BoundedContinuousFunction.norm_coe_le_norm w.toBCF 0)
    have husm : ContDiffOn ℝ (r : ℕ∞ω) u (Metric.ball 0 s) :=
      (ContDiffOn.continuousLinearMap_comp ev₀ hfsmooth).snd
    have hu0 : u 0 = 0 := by simp [u, hf0]
    have hgraph (p : E₁) (hp : p ∈ Metric.ball (0 : E₁) s) :
        f p 0 = (p, u p) := by
      refine Prod.ext ?_ ?_
      · simpa using congrArg Prod.fst (heq p hp).2.1
      · rfl
    have hcoord (p : E₁) (n : ℕ) : ‖(q ^ n)⁻¹ • f p n‖ ≤ ‖f p‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hq.le n))]
        calc
          (q ^ n)⁻¹ * ‖f p n‖ ≤ ‖f p n‖ :=
            mul_le_of_le_one_left (norm_nonneg _)
              ((inv_le_one₀ (pow_pos hq n)).mpr (one_le_pow₀ hq1))
          _ ≤ ‖f p‖ := BoundedContinuousFunction.norm_coe_le_norm (f p).toBCF n
    have hphysical (p : E₁) (hp : p ∈ Metric.ball (0 : E₁) s) (n : ℕ) :
        (q ^ n)⁻¹ • f p n ∈ Metric.ball (0 : E₁×E₂) s := by
      simpa using (hcoord p n).trans_lt ((heq p hp).1.trans_lt
        (show ‖p‖ < s by simpa using hp))
    have hgraphmem (p : E₁) (hp : p ∈ Metric.ball (0 : E₁) s) :
        (p, u p) ∈ Metric.ball (0 : E₁×E₂) s := by
      have h0 := hcoord p 0
      rw [Metric.mem_ball, dist_zero_right]
      simpa only [pow_zero, inv_one, one_smul, hgraph p hp] using h0.trans_lt (show ‖f p‖ < s by
        exact (heq p hp).1.trans_lt (by simpa using hp))
    have huLip (p : E₁) (hp : p ∈ Metric.ball (0 : E₁) s)
        (t : E₁) (ht : t ∈ Metric.ball (0 : E₁) s) : ‖u p - u t‖ ≤ ‖p - t‖ := by
      calc
        ‖u p - u t‖ ≤ ‖f p 0 - f t 0‖ := by
          simpa [u] using norm_snd_le (f p 0 - f t 0)
        _ ≤ ‖f p - f t‖ := BoundedContinuousFunction.norm_coe_le_norm (f p - f t).toBCF 0
        _ ≤ ‖p - t‖ := hfLip p hp t ht
    have hbackrec (p : E₁) (hp : p ∈ Metric.ball (0 : E₁) s) :
        ∀ n, g ((q ^ (n + 1))⁻¹ • f p (n + 1)) =
          (q ^ n)⁻¹ • f p n := by
      apply Analysis.wells_backward_weighted_recurrence T₁ T₂ q hq.ne' g R
        (by intro z; dsimp [R]; abel) (f p) (C (f p))
      · intro n
        simpa only [inv_pow, inv_inv] using hC (f p) (by
          simpa using (heq p hp).1.trans_lt (show ‖p‖ < s by simpa using hp)) n
      · intro n
        simpa using congrArg Prod.fst ((heq p hp).2.2 n)
      · intro n
        cases n with
        | zero => simpa using congrArg Prod.snd (heq p hp).2.1
        | succ n => simpa using congrArg Prod.snd ((heq p hp).2.2 n)
    have hweighted (p : E₁) (hp : p ∈ Metric.ball (0 : E₁) s) (n : ℕ) :
        q^n * ‖(q^n)⁻¹ • f p n‖ ≤ ‖p‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hq.le n)),
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq.ne'), one_mul]
      exact (BoundedContinuousFunction.norm_coe_le_norm (f p).toBCF n).trans (heq p hp).1
    have hcapture (w : ℕ → E₁ × E₂)
        (hwmem : ∀ n, w n ∈ Metric.ball 0 s)
        (hwrec : ∀ n, g (w (n+1)) = w n)
        (hwbound : ∃ M : ℝ, ∀ n, q^n * ‖w n‖ ≤ M) : (w 0).2 = u (w 0).1 := by
      have hp : (w 0).1 ∈ Metric.ball (0 : E₁) s := by
        simpa using (norm_fst_le (w 0)).trans_lt (show ‖w 0‖ < s by simpa using hwmem 0)
      obtain ⟨M,hM⟩ := hwbound
      have hb : ∃ K : ℝ, ∀ n, q^n * ‖w n - (q^n)⁻¹ • f (w 0).1 n‖ ≤ K := by
        refine ⟨M+‖(w 0).1‖, fun n ↦ ?_⟩
        calc
          _ ≤ q^n * (‖w n‖+‖(q^n)⁻¹ • f (w 0).1 n‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hq.le n)
          _ ≤ M+‖(w 0).1‖ := by
            rw [mul_add]
            exact add_le_add (hM n) (hweighted _ hp n)
      have he := hps_backward_weighted_orbit_uniqueness T₁ T₂ g (Metric.ball 0 s)
        ε q hε.le hq hsmall hrem w (fun n ↦ (q^n)⁻¹ • f (w 0).1 n)
        hwmem (hphysical _ hp) hwrec (hbackrec _ hp)
        (by simp [hgraph _ hp]) hb
      have he0 := congrArg (fun w : ℕ → E₁ × E₂ ↦ (w 0).2) he
      simpa [hgraph _ hp] using he0
    have hcaptureρ (w : ℕ → E₁ × E₂)
        (hwmem : ∀ n, w n ∈ Metric.ball 0 s)
        (hwrec : ∀ n, g (w (n+1)) = w n)
        (hwbound : ∃ M : ℝ, ∀ n, ‖w n‖ / (ρ⁻¹)^n ≤ M) :
        (w 0).2 = u (w 0).1 := by
      apply hcapture w hwmem hwrec
      by_cases hρ1 : ρ ≤ 1
      · refine ⟨s, fun n ↦ ?_⟩
        simpa [q,max_eq_right hρ1] using (show ‖w n‖ ≤ s from
          (show ‖w n‖ < s by simpa using hwmem n).le)
      · obtain ⟨M,hM⟩ := hwbound
        refine ⟨M,fun n ↦ ?_⟩
        simpa [q,max_eq_left (le_of_not_ge hρ1),inv_pow,div_eq_mul_inv,mul_comm] using hM n
    have hzero (p : E₁) (hp : p ∈ Metric.ball (0 : E₁) s) :
        Tendsto (fun n ↦ ‖(q^n)⁻¹ • f p n‖ / (ρ⁻¹)^n) atTop (𝓝 0) := by
      have hfn : Tendsto (fun n ↦ ‖f p n‖) atTop (𝓝 0) := by
        simpa [cocompact_eq_atTop] using (zero_at_infty (f p)).norm
      apply squeeze_zero (fun n ↦ div_nonneg (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr hρ.le) n))
        (fun n ↦ ?_) hfn
      rw [div_le_iff₀ (pow_pos (inv_pos.mpr hρ) n), norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hq.le n)),inv_pow]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        ((inv_le_inv₀ (pow_pos hq n) (pow_pos hρ n)).mpr
          (pow_le_pow_left₀ hρ.le hqρ n)) (norm_nonneg (f p n))
    refine ⟨u, husm, hu0, hgraphmem, ?_, ?_, ?_⟩
    · intro p hp hgp
      let w : ℕ → E₁ × E₂ := fun n ↦ match n with
        | 0 => g (p,u p)
        | n+1 => (q^n)⁻¹ • f p n
      apply hcapture w
      · intro n; cases n with
        | zero => exact hgp
        | succ n => exact hphysical p hp n
      · intro n; cases n with
        | zero => simp [w,hgraph p hp]
        | succ n => exact hbackrec p hp n
      · refine ⟨max ‖g (p,u p)‖ (q*‖p‖),fun n ↦ ?_⟩
        cases n with
        | zero => simp [w]
        | succ n =>
          calc
            q^(n+1)*‖w (n+1)‖ = q*(q^n*‖(q^n)⁻¹ • f p n‖) := by
              dsimp [w]; rw [pow_succ]; ring
            _ ≤ q*‖p‖ := mul_le_mul_of_nonneg_left (hweighted p hp n) hq.le
            _ ≤ _ := le_max_right _ _
    · intro z hz
      have hp : z.1 ∈ Metric.ball (0 : E₁) s := by
        simpa using (norm_fst_le z).trans_lt (show ‖z‖ < s by simpa using hz)
      have hw0 (h : z.2 = u z.1) : (q^0)⁻¹ • f z.1 0 = z := by
        simp only [pow_zero, inv_one, one_smul, hgraph z.1 hp, ← h, Prod.mk.eta]
      constructor
      · constructor
        · intro h
          exact ⟨fun n ↦ (q^n)⁻¹ • f z.1 n,hw0 h,hphysical z.1 hp,hbackrec z.1 hp,
            hps_normalized_zero_bounded _ ρ⁻¹ (hzero z.1 hp)⟩
        · rintro ⟨w,hw,hm,hrw,hb⟩
          simpa only [hw] using hcaptureρ w hm hrw hb
      · constructor
        · intro h
          exact ⟨fun n ↦ (q^n)⁻¹ • f z.1 n,hw0 h,hphysical z.1 hp,hbackrec z.1 hp,hzero z.1 hp⟩
        · rintro ⟨w,hw,hm,hrw,ht⟩
          simpa only [hw] using hcaptureρ w hm hrw (hps_normalized_zero_bounded _ ρ⁻¹ ht)
    · intro v D _ _ _ hv p hp
      obtain ⟨w,hw,hm,hrw,hb⟩ := hv p hp
      simpa only [hw] using hcaptureρ w hm hrw hb
  · intro hkone
    let q : ℝ := min ρ 1
    have hq : 0 < q := lt_min hρ zero_lt_one
    have hq1 : q ≤ 1 := min_le_right _ _
    have hqρ : q ≤ ρ := min_le_left _ _
    have hden : 0 < 1 - ‖T₁.symm.toContinuousLinearMap‖ * ε := by
      nlinarith [mul_nonneg (norm_nonneg T₁.symm.toContinuousLinearMap) hε.le]
    have haρ' : ‖T₁.symm.toContinuousLinearMap‖ * ρ <
        1 - ‖T₁.symm.toContinuousLinearMap‖ * ε := by
      have h := mul_lt_mul_of_pos_right ((div_lt_iff₀ hden).mp hdiv) hρ
      simpa [mul_assoc, mul_comm, mul_left_comm, hρ.ne'] using h
    have hsmall : max (‖T₁.symm.toContinuousLinearMap‖ * (q + ε))
        (q⁻¹ * (‖T₂‖ + ε)) < 1 := by
      apply max_lt
      · have hle := mul_le_mul_of_nonneg_left hqρ
          (norm_nonneg T₁.symm.toContinuousLinearMap)
        nlinarith
      · rw [mul_comm, ← div_eq_mul_inv, div_lt_one hq]
        exact lt_min hkρ (hk1 hkone).1
    have hlam : 1 ≤ q⁻¹ := (one_le_inv₀ hq).mpr hq1
    obtain ⟨C, hC, hC0, hCLip, hCsmooth, _⟩ :=
      Analysis.wells_weighted_c0_composition s q⁻¹ ε r R hs hlam hε.le hr
        hRcont hR0 hrem
    obtain ⟨f, hfsmooth, hf0, heq, hfLip, hfUnique⟩ :=
      Analysis.wells_forward_smooth_sequences T₁.symm.toContinuousLinearMap T₂
        q s ε hq hs hε.le r hr hsmall C hC0 hCsmooth hCLip
    have hfmem (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) :
        f p ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s := by
      simpa using (heq p hp).1.trans_lt (show ‖p‖ < s by simpa using hp)
    have hrec (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) :
        ∀ n, g ((q ^ n) • f p n) = (q ^ (n + 1)) • f p (n + 1) := by
      apply Analysis.wells_forward_weighted_recurrence T₁ T₂ q hq.ne' g R
        (by intro z; dsimp [R]; abel) (f p) (C (f p))
      · intro n
        simpa only [inv_pow, inv_inv] using hC (f p) (hfmem p hp) n
      · exact congrArg Prod.fst (heq p hp).2.1
      · intro n
        exact congrArg Prod.fst ((heq p hp).2.2 n)
      · intro n
        exact congrArg Prod.snd ((heq p hp).2.2 n)
    have hphysical (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) (n : ℕ) :
        (q ^ n) • f p n ∈ Metric.ball (0 : E₁ × E₂) s := by
      have hcoord : ‖f p n‖ ≤ ‖f p‖ :=
        BoundedContinuousFunction.norm_coe_le_norm (f p).toBCF n
      have hpow : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1
      rw [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (pow_nonneg hq.le n)]
      calc
        q ^ n * ‖f p n‖ ≤ ‖f p n‖ := mul_le_of_le_one_left (norm_nonneg _) hpow
        _ ≤ ‖f p‖ := hcoord
        _ ≤ ‖p‖ := (heq p hp).1
        _ < s := by simpa using hp
    let ev₀ : C₀(ℕ, E₁ × E₂) →L[ℝ] (E₁ × E₂) :=
      ({ toFun := fun w ↦ w 0
         map_add' := fun _ _ ↦ rfl
         map_smul' := fun _ _ ↦ rfl } : C₀(ℕ, E₁ × E₂) →ₗ[ℝ] (E₁ × E₂)).mkContinuous
        1 (fun w ↦ by simpa using BoundedContinuousFunction.norm_coe_le_norm w.toBCF 0)
    let v : E₂ → E₁ := fun p ↦ (f p 0).1
    have hvsm : ContDiffOn ℝ (r : ℕ∞ω) v (Metric.ball 0 s) :=
      (ContDiffOn.continuousLinearMap_comp ev₀ hfsmooth).fst
    have hv0 : v 0 = 0 := by simp [v, hf0]
    have hgraph (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) : f p 0 = (v p, p) := by
      refine Prod.ext ?_ ?_
      · rfl
      · simpa only using congrArg Prod.snd (heq p hp).2.1
    have hgraphmem (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) :
        (v p, p) ∈ Metric.ball (0 : E₁ × E₂) s := by
      simpa only [pow_zero, one_smul, hgraph p hp] using hphysical p hp 0
    have hvLip (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s)
        (t : E₂) (ht : t ∈ Metric.ball (0 : E₂) s) : ‖v p - v t‖ ≤ ‖p - t‖ := by
      calc
        ‖v p - v t‖ ≤ ‖f p 0 - f t 0‖ := norm_fst_le (f p 0 - f t 0)
        _ ≤ ‖f p - f t‖ := BoundedContinuousFunction.norm_coe_le_norm (f p - f t).toBCF 0
        _ ≤ ‖p - t‖ := hfLip p hp t ht
    have hggraph (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) :
        g (v p, p) = q • f p 1 := by
      simpa only [zero_add, pow_zero, pow_one, one_smul, hgraph p hp] using hrec p hp 0
    have hgmem (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) :
        g (v p, p) ∈ Metric.ball (0 : E₁ × E₂) s := by
      rw [hggraph p hp]
      simpa only [pow_one] using hphysical p hp 1
    obtain ⟨_, tail, _, _, htail, _, htailnorm⟩ :=
      Analysis.wells_c0_sequence_shifts (E := E₁ × E₂)
    have hinv (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) :
        g (v p, p) ∈ Metric.ball (0 : E₁ × E₂) s ∧
          (g (v p, p)).1 = v (g (v p, p)).2 := by
      refine ⟨hgmem p hp, ?_⟩
      let t : C₀(ℕ, E₁ × E₂) := q • tail (f p)
      have htcoord (n : ℕ) : t n = q • f p (n + 1) := by simp [t, htail]
      have htnorm : ‖t‖ ≤ ‖f p‖ := by
        calc
          ‖t‖ = q * ‖tail (f p)‖ := by simp [t, norm_smul, Real.norm_of_nonneg hq.le]
          _ ≤ ‖tail (f p)‖ := mul_le_of_le_one_left (norm_nonneg _) hq1
          _ ≤ ‖f p‖ := htailnorm _
      have htmem : t ∈ Metric.ball (0 : C₀(ℕ, E₁ × E₂)) s := by
        simpa using htnorm.trans_lt (show ‖f p‖ < s by simpa using hfmem p hp)
      have hbase : (g (v p, p)).2 ∈ Metric.ball (0 : E₂) s := by
        simpa using (norm_snd_le (g (v p, p))).trans_lt
          (show ‖g (v p, p)‖ < s by simpa using hgmem p hp)
      have hCt (n : ℕ) : C t n = q • C (f p) (n + 1) := by
        rw [hC t htmem n, hC (f p) (hfmem p hp) (n + 1), htcoord]
        simp only [inv_pow, inv_inv, pow_succ, smul_smul, mul_inv_rev]
        simp [mul_comm, hq.ne']
      have htzero : t 0 =
          (q • T₁.symm (t 1).1 - T₁.symm (C t 0).1, (g (v p, p)).2) := by
        have hx := congrArg (fun z : E₁ × E₂ ↦ (q • z).1) ((heq p hp).2.2 0)
        apply Prod.ext
        · simpa [htcoord, hCt, smul_sub, map_smul, smul_smul, mul_comm] using hx
        · simp [htcoord, hggraph p hp]
      have htnext (n : ℕ) : t (n + 1) =
          (q • T₁.symm (t (n + 2)).1 - T₁.symm (C t (n + 1)).1,
            q⁻¹ • (T₂ (t n).2 + (C t n).2)) := by
        have hx := congrArg (fun z : E₁ × E₂ ↦ q • z) ((heq p hp).2.2 (n + 1))
        simpa [htcoord, hCt, smul_sub, smul_add, map_smul, smul_smul,
          mul_comm, mul_left_comm, mul_assoc, Nat.add_assoc] using hx
      have htEq := hfUnique (g (v p, p)).2 hbase t htmem htzero htnext
      change (g (v p, p)).1 = (f (g (v p, p)).2 0).1
      rw [← htEq, htcoord, hggraph p hp]
    have hcapture (w : ℕ → E₁ × E₂)
        (hwmem : ∀ n, w n ∈ Metric.ball 0 s)
        (hwrec : ∀ n, g (w n) = w (n + 1))
        (hwbound : ∃ M : ℝ, ∀ n, ‖w n‖ / ρ ^ n ≤ M) :
        (w 0).1 = v (w 0).2 := by
      by_cases ha0 : ‖T₁.symm.toContinuousLinearMap‖ = 0
      · have hT : T₁.symm.toContinuousLinearMap = 0 := norm_eq_zero.mp ha0
        have hz (x : E₁) : x = 0 := by
          have h := congrArg (fun F : E₁ →L[ℝ] E₁ ↦ F (T₁ x)) hT
          simpa using h
        rw [hz (w 0).1, hz (v (w 0).2)]
      · obtain ⟨M, hM⟩ := hwbound
        exact hps_stable_bounded_orbit_capture T₁ T₂ g s ε ρ hs hρ ha0
          (haρ ha0) hrem v hv0 hgraphmem hvLip hinv w hwmem hwrec M hM
    have hzero (p : E₂) (hp : p ∈ Metric.ball (0 : E₂) s) :
        Tendsto (fun n ↦ ‖(q ^ n) • f p n‖ / ρ ^ n) atTop (𝓝 0) := by
      have hfn : Tendsto (fun n ↦ ‖f p n‖) atTop (𝓝 0) := by
        simpa [cocompact_eq_atTop] using (zero_at_infty (f p)).norm
      apply squeeze_zero (fun n ↦ div_nonneg (norm_nonneg _) (pow_nonneg hρ.le n))
        (fun n ↦ ?_) hfn
      rw [div_le_iff₀ (pow_pos hρ n), norm_smul,
        Real.norm_of_nonneg (pow_nonneg hq.le n)]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq.le hqρ n) (norm_nonneg (f p n))
    refine ⟨v, hvsm, hv0, hgraphmem, hinv, ?_, ?_⟩
    · intro z hz
      have hp : z.2 ∈ Metric.ball (0 : E₂) s := by
        simpa using (norm_snd_le z).trans_lt (show ‖z‖ < s by simpa using hz)
      have hw0 (h : z.1 = v z.2) : (q ^ 0) • f z.2 0 = z := by
        simp only [pow_zero, one_smul, hgraph z.2 hp, ← h, Prod.mk.eta]
      constructor
      · constructor
        · intro h
          exact ⟨fun n ↦ (q ^ n) • f z.2 n, hw0 h, hphysical z.2 hp,
            hrec z.2 hp, hps_normalized_zero_bounded _ ρ (hzero z.2 hp)⟩
        · rintro ⟨w, hw, hm, hrw, hb⟩
          simpa only [hw] using hcapture w hm hrw hb
      · constructor
        · intro h
          exact ⟨fun n ↦ (q ^ n) • f z.2 n, hw0 h, hphysical z.2 hp,
            hrec z.2 hp, hzero z.2 hp⟩
        · rintro ⟨w, hw, hm, hrw, ht⟩
          simpa only [hw] using hcapture w hm hrw (hps_normalized_zero_bounded w ρ ht)
    · intro u D _ _ _ hU y hy
      obtain ⟨w, hw, hm, hrw, hb⟩ := hU y hy
      simpa only [hw] using hcapture w hm hrw hb

end HolomorphicAnosov

