import HolomorphicAnosov.Analysis.Complex.QCPartitionTwoPieceRigidity

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle

/-- A half-turn of the source rectangle exchanges its complete horizontal sides
and advances its four marks by two, without changing its modulus. Compose the
conformal model and its inverse with the involution z ↦ a+ib−z. This involution
preserves both rectangles and exchanges their bottom and top sides; hence the
ambient side flag is negated. Source: Lehto–Virtanen I.§2.4 p.15 and I.Lemma 4.2. -/
theorem qc_complete_sides_half_turn
    {Q : Set ℂ} {p : Fin 4 → ℂ} {m M : ℝ} {flip : Bool}
    (h : HasMarkedConformalModulusWithCompleteASides Q p m M flip) :
    HasMarkedConformalModulusWithCompleteASides Q (fun i ↦ p (i + 2)) m M (!flip) := by
  obtain ⟨a,b,ha,hb,hm,F,G,hF,hG,hbij,hGmap,hGF,hFG,e,he,hp,hbot,htop⟩ := h
  let r : ℂ → ℂ := fun z ↦ (a : ℂ) + (b : ℂ) * Complex.I - z
  have hrr (z : ℂ) : r (r z) = z := by dsimp [r]; ring
  have hre (z : ℂ) : (r z).re = a - z.re := by simp [r]
  have him (z : ℂ) : (r z).im = b - z.im := by simp [r]
  have hro : MapsTo r (OpenRectangle a b) (OpenRectangle a b) := by
    intro z hz
    change (0 < (r z).re ∧ (r z).re < a) ∧ (0 < (r z).im ∧ (r z).im < b)
    rw [hre,him]
    rcases hz with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  have hrc : MapsTo r (ClosedRectangle a b) (ClosedRectangle a b) := by
    intro z hz
    change (0 ≤ (r z).re ∧ (r z).re ≤ a) ∧ (0 ≤ (r z).im ∧ (r z).im ≤ b)
    rw [hre,him]
    rcases hz with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  have hr : Differentiable ℂ r := (differentiable_const _).sub differentiable_id
  let er : ClosedRectangle a b ≃ₜ ClosedRectangle a b :=
    { toFun := fun z ↦ ⟨r z,hrc z.property⟩
      invFun := fun z ↦ ⟨r z,hrc z.property⟩
      left_inv := fun z ↦ Subtype.ext (hrr z)
      right_inv := fun z ↦ Subtype.ext (hrr z)
      continuous_toFun := (hr.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hr.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨a,b,ha,hb,hm,F ∘ r,r ∘ G,hF.comp hr.differentiableOn hro,
    hr.differentiableOn.comp hG hGmap,?_,hro.comp hGmap,?_,?_,er.trans e,?_,?_,?_,?_⟩
  · exact hbij.comp ⟨hro,fun x _ y _ hxy ↦ by simpa only [hrr] using congrArg r hxy,
      fun z hz ↦ ⟨r z,hro hz,hrr z⟩⟩
  · intro z hz
    simp only [Function.comp_apply,hGF _ (hro hz),hrr]
  · intro z hz
    simp only [Function.comp_apply,hrr,hFG _ hz]
  · intro z hz
    exact he (er z) (hro hz)
  · intro i z hz
    apply hp (i + 2) (er z)
    change r (z : ℂ) = _
    rw [hz]
    fin_cases i <;> norm_num [r,RectangleCorner]
  · intro z hz
    have hz' : (er z : ℂ) ∈ ClosedRectangleSide a b 2 := by
      change (r z).re ∈ Icc 0 a ∧ (r z).im ∈ ({b} : Set ℝ)
      change (z : ℂ).re ∈ Icc 0 a ∧ (z : ℂ).im ∈ ({0} : Set ℝ) at hz
      refine ⟨(hrc z.property).1,?_⟩
      change (r z).im = b
      rw [him,show (z : ℂ).im = 0 from hz.2,sub_zero]
    cases flip <;> simpa using htop (er z) hz'
  · intro z hz
    have hz' : (er z : ℂ) ∈ ClosedRectangleSide a b 0 := by
      change (r z).re ∈ Icc 0 a ∧ (r z).im ∈ ({0} : Set ℝ)
      change (z : ℂ).re ∈ Icc 0 a ∧ (z : ℂ).im ∈ ({b} : Set ℝ) at hz
      refine ⟨(hrc z.property).1,?_⟩
      change (r z).im = 0
      rw [him,show (z : ℂ).im = b from hz.2,sub_self]
    cases flip <;> simpa using hbot (er z) hz'

end HolomorphicAnosov
