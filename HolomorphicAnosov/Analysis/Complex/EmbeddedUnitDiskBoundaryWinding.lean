import HolomorphicAnosov.Analysis.Complex.OddLoopWindingNonzero
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingHomotopy
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingCongrSub

namespace HolomorphicAnosov


/-- The boundary of an injectively embedded closed complex unit disk has nonzero
winding about the image of its center. Agent-written exponential-lift proof of
the planar separation step in Hatcher Theorem 2B.3, p.172.

Move the subtracted image point along the radius opposite to each boundary
point. Injectivity keeps every difference nonzero. The initial loop is the
boundary minus the center image, and the final loop is the odd difference of
opposite boundary images. Homotopy invariance and nonzero odd winding finish. -/
theorem embedded_unit_disk_boundary_winding_ne_zero
    (f : Metric.closedBall (0 : ℂ) 1 → ℂ) (hf : Continuous f)
    (hi : Function.Injective f) :
    let γ : ComplexLoop := ⟨fun z ↦ f ⟨z, by simp⟩, hf.comp (by fun_prop)⟩
    let c := f ⟨0, by simp⟩
    ∃ hc : ∀ z, γ z ≠ c, loopWinding γ c hc ≠ 0 := by
  intro γ c
  let d (t : unitInterval) (z : Circle) : Metric.closedBall (0 : ℂ) 1 :=
    ⟨-(t : ℝ) • (z : ℂ), by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg t.property.1, Circle.norm_coe, mul_one]
      exact t.property.2⟩
  have hd (t : unitInterval) (z : Circle) :
      (⟨(z : ℂ), by simp⟩ : Metric.closedBall (0 : ℂ) 1) ≠ d t z := by
    intro heq
    have he := congrArg Subtype.val heq
    change (z : ℂ) = -(t : ℝ) • (z : ℂ) at he
    have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
    have hh : ((1 + (t : ℝ) : ℝ) : ℂ) * (z : ℂ) = 0 := by
      have he2 : (z : ℂ) = -((t : ℂ) * (z : ℂ)) := by
        simpa only [neg_smul, Complex.real_smul] using he
      push_cast
      rw [add_mul, one_mul]
      exact eq_neg_iff_add_eq_zero.mp he2
    have hcoef := (mul_eq_zero.mp hh).resolve_right hz0
    have hr : 1 + (t : ℝ) = 0 := by exact_mod_cast hcoef
    linarith [t.property.1]
  have havoid (t : unitInterval) (z : Circle) : γ z - f (d t z) ≠ 0 :=
    sub_ne_zero.mpr (fun he ↦ hd t z (hi he))
  have hc (z : Circle) : γ z ≠ c := by
    have h := havoid 0 z
    simpa [d, c, sub_ne_zero] using h
  refine ⟨hc, ?_⟩
  let δ : ComplexLoop := ⟨fun z ↦ γ z - c, by fun_prop⟩
  let α : ComplexLoop := ⟨fun z ↦ γ z - γ (-z), by fun_prop⟩
  have hα (z : Circle) : α z ≠ 0 := by
    simpa [α, γ, d] using havoid 1 z
  have hδ (z : Circle) : δ z ≠ 0 := sub_ne_zero.mpr (hc z)
  have hodd : ∀ z, α (-z) = -α z := by intro z; simp [α, neg_sub]
  have hhom : LoopHomotopyAvoids δ α 0 := by
    refine ⟨⟨fun p ↦ γ p.2 - f (d p.1 p.2), ?_⟩, ?_, ?_, havoid⟩
    · exact (γ.continuous.comp continuous_snd).sub (hf.comp (by fun_prop))
    · intro z
      simp [δ, c, d]
    · intro z
      simp [α, γ, d]
  have heq : loopWinding γ c hc = loopWinding α 0 hα :=
    (loopWinding_congr_sub γ δ c 0 hc hδ (fun z ↦ by simp [δ])).trans
      (loopWinding_homotopy δ α 0 hδ hα hhom)
  rw [heq]
  exact loopWinding_ne_zero_of_odd α hα hodd

end HolomorphicAnosov
