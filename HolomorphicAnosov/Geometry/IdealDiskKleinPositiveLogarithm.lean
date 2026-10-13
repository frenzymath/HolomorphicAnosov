import HolomorphicAnosov.Geometry.IdealDiskTriangle
import Mathlib.Tactic
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingHomotopy
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement

namespace HolomorphicAnosov

/-- Radial interpolation from the identity to the Klein map. -/
noncomputable def idealDiskKleinHomotopy (t : ℝ) (z : ℂ) : ℂ :=
  ((1-t) + t * (2 / (1 + ‖z‖^2)) : ℝ) • z

/-- The Klein radial interpolation remains injective on the closed disk. (Lyubich) -/
theorem idealDiskKleinHomotopy_injOn {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Set.InjOn (idealDiskKleinHomotopy t) {z : ℂ | ‖z‖ ≤ 1} := by
  have hscale (r : ℝ) : 0 < (1-t) + t * (2 / (1+r^2)) := by
    have hp : 0 < 2 / (1+r^2) := by positivity
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← ht0]
      norm_num
    · have hm := mul_pos ht0 hp
      linarith [ht.2]
  have hk : StrictMonoOn (fun r : ℝ ↦ 2*r/(1+r^2)) (Set.Icc 0 1) := by
    intro r hr s hs hrs
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hprod : r*s < 1 := (mul_le_mul_of_nonneg_left hs.2 hr.1).trans_lt
      (by simpa using hrs.trans_le hs.2)
    nlinarith [mul_pos (sub_pos.mpr hrs) (sub_pos.mpr hprod)]
  have hm : StrictMonoOn (fun r : ℝ ↦ ((1-t) + t * (2/(1+r^2))) * r)
      (Set.Icc 0 1) := by
    intro r hr s hs hrs
    have h := hk hr hs hrs
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← ht0]
      simpa using hrs
    · have hp := mul_pos ht0 (sub_pos.mpr h)
      have hn := mul_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr hrs).le
      have halg (r : ℝ) : ((1-t) + t * (2/(1+r^2))) * r =
          (1-t)*r + t*(2*r/(1+r^2)) := by ring
      dsimp only
      rw [halg, halg]
      nlinarith

  intro x hx y hy heq
  have hn := congrArg norm heq
  simp only [idealDiskKleinHomotopy, norm_smul, Real.norm_eq_abs,
    abs_of_pos (hscale _)] at hn
  have hr := hm.injOn ⟨norm_nonneg _, hx⟩ ⟨norm_nonneg _, hy⟩ hn
  dsimp [idealDiskKleinHomotopy] at heq
  rw [hr] at heq
  exact mul_left_cancel₀ (by exact_mod_cast (hscale ‖y‖).ne') heq

@[simp] theorem idealDiskKleinHomotopy_zero (z : ℂ) :
    idealDiskKleinHomotopy 0 z = z := by simp [idealDiskKleinHomotopy]

@[simp] theorem idealDiskKleinHomotopy_one (z : ℂ) :
    idealDiskKleinHomotopy 1 z = idealDiskKlein z := by
  simp [idealDiskKleinHomotopy, idealDiskKlein, Algebra.smul_def]
  ring

/-- The radial interpolation is jointly continuous. -/
theorem continuous_idealDiskKleinHomotopy :
    Continuous (fun p : ℝ × ℂ ↦ idealDiskKleinHomotopy p.1 p.2) := by
  unfold idealDiskKleinHomotopy
  fun_prop (disch := intro p; positivity)

/-- The Klein coordinate transports positive winding, with the omitted point transported by the same isotopy. (Lyubich) -/
theorem idealDiskKlein_positive_logarithm
    (γ : ComplexLoop) (hγ : ∀ z, ‖γ z‖ ≤ 1) (a : ℂ) (ha : ‖a‖ ≤ 1)
    (hne : ∀ z, γ z ≠ a)
    (L : C(↑unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = γ (Circle.exp (2 * Real.pi * (t : ℝ))) - a)
    (hinc : L 1 - L 0 = (2 * Real.pi : ℂ) * Complex.I) :
    ∃ M : C(↑unitInterval, ℂ),
      (∀ t, Complex.exp (M t) = idealDiskKlein (γ (Circle.exp (2 * Real.pi * (t : ℝ)))) -
        idealDiskKlein a) ∧ M 1 - M 0 = (2 * Real.pi : ℂ) * Complex.I := by
  let g₀ : ComplexLoop := ⟨fun z ↦ γ z - a, by fun_prop⟩
  let g₁ : ComplexLoop := ⟨fun z ↦ idealDiskKleinHomotopy 1 (γ z) -
    idealDiskKleinHomotopy 1 a, by
      exact (continuous_idealDiskKleinHomotopy.comp
        (continuous_const.prodMk γ.continuous)).sub continuous_const⟩
  have h₀ : ∀ z, g₀ z ≠ 0 := fun z ↦ sub_ne_zero.mpr (hne z)
  have h₁ : ∀ z, g₁ z ≠ 0 := by
    intro z he
    apply hne z
    exact idealDiskKleinHomotopy_injOn (by simp) (hγ z) ha (sub_eq_zero.mp he)
  have hhom : LoopHomotopyAvoids g₀ g₁ 0 := by
    refine ⟨⟨fun p ↦ idealDiskKleinHomotopy p.1 (γ p.2) -
        idealDiskKleinHomotopy p.1 a, ?_⟩, ?_, ?_, ?_⟩
    · exact (continuous_idealDiskKleinHomotopy.comp
        (continuous_subtype_val.fst'.prodMk (γ.continuous.comp continuous_snd))).sub
        (continuous_idealDiskKleinHomotopy.comp
          (continuous_subtype_val.fst'.prodMk continuous_const))
    · intro z
      simp [g₀]
    · intro z
      rfl
    · intro t z he
      apply hne z
      exact idealDiskKleinHomotopy_injOn t.property (hγ z) ha (sub_eq_zero.mp he)
  have hw₀ : loopWinding g₀ 0 h₀ = 1 := by
    apply loopWinding_eq_of_increment g₀ 0 h₀ L
    · simpa [puncturedLoopPath, g₀] using hL
    · simpa using hinc
  have hw₁ : loopWinding g₁ 0 h₁ = 1 :=
    (loopWinding_homotopy g₀ g₁ 0 h₀ h₁ hhom).symm.trans hw₀
  obtain ⟨M, hm, hi⟩ := loopWinding_lift g₁ 0 h₁
  refine ⟨M, ?_, ?_⟩
  · simpa [puncturedLoopPath, g₁] using hm
  · rw [hw₁] at hi
    simpa [sub_eq_iff_eq_add, add_comm] using hi

end HolomorphicAnosov
