import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulus

/-! # Cyclic relabeling reciprocates the conformal modulus

Source: Lehto–Virtanen (1973), I §2.4, p.15, final displayed formula.
-/

namespace HolomorphicAnosov.Analysis.MarkedRectangle
open Set

/-- Moving the first corner of a marked quadrilateral to the end reciprocates its
conformal modulus. Source: Lehto–Virtanen, I §2.4, p.15, last display.

Proof: for a rectangle model of width a and height b, rotate the rectangle of
width b and height a by z ↦ a + iz. Its corners become the original corners
1,2,3,0. Compose the original holomorphic map and its literal inverse with this
rotation and its inverse; compose the closed-rectangle homeomorphisms likewise.
The new side ratio is b/a=(a/b)⁻¹. Positive side lengths exclude degeneracy. -/
theorem HasMarkedConformalModulus.cyclic {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (h : HasMarkedConformalModulus Q p m) :
    HasMarkedConformalModulus Q (fun i ↦ p (i + 1)) m⁻¹ := by
  obtain ⟨a, b, ha, hb, rfl, F, G, hF, hG, hbij, hGmap, hGF, hFG, e, he, hp⟩ := h
  let r : ℂ → ℂ := fun z ↦ (a : ℂ) + Complex.I * z
  let s : ℂ → ℂ := fun z ↦ -Complex.I * (z - a)
  have hsr (z : ℂ) : s (r z) = z := by dsimp [s, r]; ring_nf; simp
  have hrs (z : ℂ) : r (s z) = z := by dsimp [s, r]; ring_nf; simp
  have hro : MapsTo r (OpenRectangle b a) (OpenRectangle a b) := by
    intro z hz
    rcases hz with ⟨hx, hy⟩
    change (0 < (r z).re ∧ (r z).re < a) ∧ (0 < (r z).im ∧ (r z).im < b)
    dsimp [r]; simp only [Complex.I_mul_re, Complex.I_mul_im, zero_add]
    exact ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩, hx⟩
  have hso : MapsTo s (OpenRectangle a b) (OpenRectangle b a) := by
    intro z hz
    rcases hz with ⟨hx, hy⟩
    change (0 < (s z).re ∧ (s z).re < b) ∧ (0 < (s z).im ∧ (s z).im < a)
    dsimp [s]; simp only [neg_mul, Complex.neg_re, Complex.I_mul_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero, neg_neg, Complex.neg_im,
      Complex.I_mul_im, Complex.sub_re, Complex.ofReal_re]
    exact ⟨hy, ⟨by linarith [hx.2], by linarith [hx.1]⟩⟩
  have hrc : MapsTo r (ClosedRectangle b a) (ClosedRectangle a b) := by
    intro z hz
    rcases hz with ⟨hx, hy⟩
    change (0 ≤ (r z).re ∧ (r z).re ≤ a) ∧ (0 ≤ (r z).im ∧ (r z).im ≤ b)
    dsimp [r]; simp only [Complex.I_mul_re, Complex.I_mul_im, zero_add]
    exact ⟨⟨by linarith [hy.2], by linarith [hy.1]⟩, hx⟩
  have hsc : MapsTo s (ClosedRectangle a b) (ClosedRectangle b a) := by
    intro z hz
    rcases hz with ⟨hx, hy⟩
    change (0 ≤ (s z).re ∧ (s z).re ≤ b) ∧ (0 ≤ (s z).im ∧ (s z).im ≤ a)
    dsimp [s]; simp only [neg_mul, Complex.neg_re, Complex.I_mul_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero, neg_neg, Complex.neg_im,
      Complex.I_mul_im, Complex.sub_re, Complex.ofReal_re]
    exact ⟨hy, ⟨by linarith [hx.2], by linarith [hx.1]⟩⟩
  have hr : Differentiable ℂ r := (differentiable_const _).add ((differentiable_const _).mul differentiable_id)
  have hs : Differentiable ℂ s := (differentiable_const _).mul (differentiable_id.sub (differentiable_const _))
  let er : ClosedRectangle b a ≃ₜ ClosedRectangle a b :=
    { toFun := fun z ↦ ⟨r z, hrc z.property⟩
      invFun := fun z ↦ ⟨s z, hsc z.property⟩
      left_inv := fun z ↦ Subtype.ext (hsr z)
      right_inv := fun z ↦ Subtype.ext (hrs z)
      continuous_toFun := (hr.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hs.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨b, a, hb, ha, by simp, F ∘ r, s ∘ G, hF.comp hr.differentiableOn hro,
    hs.differentiableOn.comp hG hGmap, ?_, hso.comp hGmap, ?_, ?_, er.trans e, ?_, ?_⟩
  · exact hbij.comp ⟨hro, fun x _ y _ hxy ↦ by simpa only [hsr] using congrArg s hxy,
      fun z hz ↦ ⟨s z, hso hz, hrs z⟩⟩
  · intro z hz
    simp only [Function.comp_apply, hGF _ (hro hz), hsr]
  · intro z hz
    simp only [Function.comp_apply, hrs, hFG _ hz]
  · intro z hz
    exact he (er z) (hro hz)
  · intro i z hz
    apply hp (i + 1) (er z)
    change r (z : ℂ) = RectangleCorner a b (i + 1)
    rw [hz]
    fin_cases i <;> norm_num [r, RectangleCorner] <;> ring_nf <;> simp

end HolomorphicAnosov.Analysis.MarkedRectangle
