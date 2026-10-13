import HolomorphicAnosov.Ghys.AffineProjectiveStructure

open Set Filter Metric _root_.Topology

namespace HolomorphicAnosov.Ghys

universe u

/-- Two invertible complex affine transformations that agree on a chart germ have equal
coefficients. -/
theorem affineTransformation_eq_of_eventuallyEq
    {L : Type u} [TopologicalSpace L]
    (c : OpenPartialHomeomorph L ℂ) {a b : ComplexAffineTransformation}
    {x : L} (hx : x ∈ c.source)
    (h : ∀ᶠ y in 𝓝 x, a.apply (c y) = b.apply (c y)) : a = b := by
  have h' : ∀ᶠ z in 𝓝 (c x), a.apply z = b.apply z :=
    (c.eventually_nhds (fun z ↦ a.apply z = b.apply z) hx).2 h
  change {z : ℂ | a.apply z = b.apply z} ∈ 𝓝 (c x) at h'
  rw [Metric.mem_nhds_iff] at h'
  obtain ⟨ε, hε, hball⟩ := h'
  have h0 := hball (mem_ball_self hε)
  let z₁ : ℂ := c x + (ε : ℂ) / 2
  have hz₁ : z₁ ∈ Metric.ball (c x) ε := by
    rw [mem_ball]
    dsimp [z₁]
    norm_num [abs_of_pos hε]
    linarith
  have h1 := hball hz₁
  have heps : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
  have hslope : a.slope = b.slope := by
    dsimp [ComplexAffineTransformation.apply] at h0 h1
    have hdiff : (a.slope - b.slope) * (ε / 2 : ℂ) = 0 := by
      linear_combination h1 - h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right
      (div_ne_zero heps (by norm_num)))
  have htrans : a.translation = b.translation := by
    dsimp [ComplexAffineTransformation.apply] at h0
    rw [hslope] at h0
    linear_combination h0
  cases a
  cases b
  simp_all

end HolomorphicAnosov.Ghys
