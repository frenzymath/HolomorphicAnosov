import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Tactic

/-!
Radial comparison of a convex complement with a punctured space. (Hatcher, Lemma 3.27)
-/

open Set

namespace HolomorphicAnosov

/-- For a convex set containing zero and lying strictly inside a centered ball, its complement includes by a homotopy equivalence into the punctured space. (Hatcher, Lemma 3.27) -/
theorem convex_complement_puncture_equiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK : Convex ℝ K) (hzero : (0 : E) ∈ K)
    (R : ℝ) (hR : 0 < R) (hbound : K ⊆ Metric.ball 0 R) :
    ∃ e : ContinuousMap.HomotopyEquiv ↥(Kᶜ) {z : E // z ≠ 0},
      ∀ z, (e z).val = z.val := by
  have hne (z : ↥(Kᶜ)) : z.val ≠ 0 := by
    intro hz
    exact z.property (hz ▸ hzero)
  have hnorm (z : E) (hz : z ≠ 0) : ‖(R / ‖z‖) • z‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR (norm_pos_iff.mpr hz))]
    exact div_mul_cancel₀ R (norm_ne_zero_iff.mpr hz)
  have hout (z : E) (hz : z ≠ 0) : (R / ‖z‖) • z ∉ K := by
    intro hm
    have hb := hbound hm
    rw [Metric.mem_ball, dist_zero_right, hnorm z hz] at hb
    exact lt_irrefl _ hb
  have hcoef (t : unitInterval) (z : E) (hz : z ≠ 0) :
      0 < (1 - (t : ℝ)) + (t : ℝ) * (R / ‖z‖) := by
    have hp : 0 < R / ‖z‖ := div_pos hR (norm_pos_iff.mpr hz)
    by_cases ht : (t : ℝ) = 1
    · simp [ht, hp]
    · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
      have hm := mul_nonneg t.property.1 hp.le
      linarith
  have havoid (t : unitInterval) (z : ↥(Kᶜ)) :
      ((1 - (t : ℝ)) + (t : ℝ) * (R / ‖z.val‖)) • z.val ∉ K := by
    let c := (1 - (t : ℝ)) + (t : ℝ) * (R / ‖z.val‖)
    have hc : 0 < c := hcoef t z (hne z)
    have hn : 0 < ‖z.val‖ := norm_pos_iff.mpr (hne z)
    by_cases hzR : ‖z.val‖ ≤ R
    · have hquot : 1 ≤ R / ‖z.val‖ := (le_div_iff₀ hn).mpr (by simpa using hzR)
      have hc1 : 1 ≤ c := by dsimp [c]; nlinarith [t.property.1]
      intro hcz
      have hinv : c⁻¹ ∈ Icc (0 : ℝ) 1 :=
        ⟨inv_nonneg.mpr hc.le, inv_le_one_of_one_le₀ hc1⟩
      have hzK := hK.smul_mem_of_zero_mem hzero hcz hinv
      have heq : c⁻¹ • (c • z.val) = z.val := by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      exact z.property (heq ▸ hzK)
    · intro hm
      have hb : ‖c • z.val‖ < R := by
        simpa only [Metric.mem_ball, dist_zero_right] using hbound hm
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hb
      have heq : c * ‖z.val‖ = (1 - (t : ℝ)) * ‖z.val‖ + (t : ℝ) * R := by
        dsimp [c]
        rw [add_mul, mul_assoc, div_mul_cancel₀ _ hn.ne']
      rw [heq] at hb
      have hprod := mul_nonneg (sub_nonneg.mpr t.property.2)
        (sub_nonneg.mpr (le_of_not_ge hzR))
      nlinarith
  let i : C(↥(Kᶜ), {z : E // z ≠ 0}) :=
    ⟨fun z ↦ ⟨z.val, hne z⟩, continuous_subtype_val.subtype_mk _⟩
  let r : C({z : E // z ≠ 0}, ↥(Kᶜ)) :=
    ⟨fun z ↦ ⟨(R / ‖z.val‖) • z.val, hout z z.property⟩,
      ((continuous_const.div (continuous_norm.comp continuous_subtype_val)
        (fun z ↦ norm_ne_zero_iff.mpr z.property)).smul continuous_subtype_val).subtype_mk _⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id ↥(Kᶜ)) (r.comp i) := {
    toFun := fun z ↦ ⟨((1 - (z.1 : ℝ)) + (z.1 : ℝ) * (R / ‖z.2.val‖)) • z.2.val,
      havoid z.1 z.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hn : Continuous (fun z : unitInterval × ↥(Kᶜ) ↦ R / ‖z.2.val‖) :=
        continuous_const.div (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
          (fun z ↦ norm_ne_zero_iff.mpr (hne z.2))
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_fst).mul hn)).smul
          (continuous_subtype_val.comp continuous_snd)
    map_zero_left := by intro z; apply Subtype.ext; simp
    map_one_left := by intro z; apply Subtype.ext; simp [i, r] }
  let J : ContinuousMap.Homotopy (ContinuousMap.id {z : E // z ≠ 0}) (i.comp r) := {
    toFun := fun z ↦ ⟨((1 - (z.1 : ℝ)) + (z.1 : ℝ) * (R / ‖z.2.val‖)) • z.2.val,
      smul_ne_zero (hcoef z.1 z.2 z.2.property).ne' z.2.property⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hn : Continuous (fun z : unitInterval × {z : E // z ≠ 0} ↦ R / ‖z.2.val‖) :=
        continuous_const.div (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
          (fun z ↦ norm_ne_zero_iff.mpr z.2.property)
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_fst).mul hn)).smul
          (continuous_subtype_val.comp continuous_snd)
    map_zero_left := by intro z; apply Subtype.ext; simp
    map_one_left := by intro z; apply Subtype.ext; simp [i, r] }
  exact ⟨⟨i, r, ⟨H.symm⟩, ⟨J.symm⟩⟩, fun _ ↦ rfl⟩

end HolomorphicAnosov
