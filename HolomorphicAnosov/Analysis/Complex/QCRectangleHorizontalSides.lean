import HolomorphicAnosov.Analysis.MarkedRectangleVerticalSides
import Mathlib.Topology.Homeomorph.Lemmas

namespace HolomorphicAnosov.Analysis
open Set

/-- Exchanging real and imaginary coordinates in both marked rectangles turns
horizontal side correspondence into the existing vertical side theorem. This
is purely a topological adapter; no analyticity of the rectangle map is used. -/
theorem marked_rectangle_open_horizontal_side
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (T : ℂ → ℂ)
    (h_bijective : BijOn T (Complex.reProdIm (Ioo 0 a) (Ioo 0 b))
      (Complex.reProdIm (Ioo 0 A) (Ioo 0 B)))
    (e : Complex.reProdIm (Icc 0 a) (Icc 0 b) ≃ₜ
      Complex.reProdIm (Icc 0 A) (Icc 0 B))
    (h_extension : ∀ z : Complex.reProdIm (Icc 0 a) (Icc 0 b),
      (z : ℂ) ∈ Complex.reProdIm (Ioo 0 a) (Ioo 0 b) → (e z : ℂ) = T z)
    (h_zero : (e ⟨0, by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = 0)
    (h_right : (e ⟨(a : ℂ), by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ))
    (h_top_right : (e ⟨(a : ℂ) + (b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ) + (B : ℂ) * Complex.I)
    (h_top_left : (e ⟨(b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (B : ℂ) * Complex.I)
    (y Y : ℝ) (hy : (y = 0 ∧ Y = 0) ∨ (y = b ∧ Y = B)) :
    ∀ z : Complex.reProdIm (Icc 0 a) (Icc 0 b), (z : ℂ).im = y →
      (z : ℂ).re ∈ Ioo 0 a →
      (e z : ℂ).im = Y ∧ (e z : ℂ).re ∈ Ioo 0 A := by
  let s : ℂ → ℂ := fun z ↦ (z.im : ℂ) + z.re * Complex.I
  have sre (z : ℂ) : (s z).re = z.im := by simp [s]
  have sim (z : ℂ) : (s z).im = z.re := by simp [s]
  have ss (z : ℂ) : s (s z) = z := by apply Complex.ext <;> simp [s]
  have sc : Continuous s := by dsimp [s]; fun_prop
  let E (a b : ℝ) : Complex.reProdIm (Icc 0 a) (Icc 0 b) ≃ₜ
      Complex.reProdIm (Icc 0 b) (Icc 0 a) :=
    { toFun := fun z ↦ ⟨s z, by simpa only [Complex.mem_reProdIm, Function.comp_apply, sre, sim, mem_preimage] using (And.intro z.property.2 z.property.1)⟩
      invFun := fun z ↦ ⟨s z, by simpa only [Complex.mem_reProdIm, Function.comp_apply, sre, sim, mem_preimage] using (And.intro z.property.2 z.property.1)⟩
      left_inv := fun z ↦ Subtype.ext (ss z)
      right_inv := fun z ↦ Subtype.ext (ss z)
      continuous_toFun := (sc.comp continuous_subtype_val).subtype_mk (fun z ↦ by
        simpa only [Complex.mem_reProdIm, Function.comp_apply, sre, sim, mem_preimage] using
          (And.intro z.property.2 z.property.1))
      continuous_invFun := (sc.comp continuous_subtype_val).subtype_mk (fun z ↦ by
        simpa only [Complex.mem_reProdIm, Function.comp_apply, sre, sim, mem_preimage] using
          (And.intro z.property.2 z.property.1)) }
  have hsb (a b : ℝ) : BijOn s (Complex.reProdIm (Ioo 0 a) (Ioo 0 b))
      (Complex.reProdIm (Ioo 0 b) (Ioo 0 a)) := by
    refine ⟨fun z hz ↦ ?_, fun z hz w hw h ↦ ?_, fun z hz ↦ ?_⟩
    · simpa only [Complex.mem_reProdIm, Function.comp_apply, sre, sim, mem_preimage] using And.intro hz.2 hz.1
    · exact (ss z).symm.trans ((congrArg s h).trans (ss w))
    · exact ⟨s z, by simpa only [Complex.mem_reProdIm, Function.comp_apply, sre, sim, mem_preimage] using (And.intro hz.2 hz.1), ss z⟩
  let e' := (E b a).trans (e.trans (E A B))
  let T' := s ∘ T ∘ s
  have hbij' : BijOn T' (Complex.reProdIm (Ioo 0 b) (Ioo 0 a))
      (Complex.reProdIm (Ioo 0 B) (Ioo 0 A)) :=
    (hsb A B).comp (h_bijective.comp (hsb b a))
  have he' (z : Complex.reProdIm (Icc 0 b) (Icc 0 a))
      (hz : (z : ℂ) ∈ Complex.reProdIm (Ioo 0 b) (Ioo 0 a)) : (e' z : ℂ) = T' z := by
    change s (e (E b a z)) = s (T (s z))
    rw [h_extension (E b a z) ((hsb b a).mapsTo hz)]
    rfl
  have h0 : (e' ⟨0, by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = 0 := by
    simpa [e', E, s] using congrArg s h_zero
  have hright : (e' ⟨(b : ℂ), by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (B : ℂ) := by
    simpa [e', E, s] using congrArg s h_top_left
  have htr : (e' ⟨(b : ℂ) + (a : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (B : ℂ) + (A : ℂ) * Complex.I := by
    simpa [e', E, s] using congrArg s h_top_right
  have htl : (e' ⟨(a : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ) * Complex.I := by
    simpa [e', E, s] using congrArg s h_right
  intro z hz hz'
  have hzre : ((E a b z : Complex.reProdIm (Icc 0 b) (Icc 0 a)) : ℂ).re = y :=
    (sre z).trans hz
  have hzim : ((E a b z : Complex.reProdIm (Icc 0 b) (Icc 0 a)) : ℂ).im ∈ Ioo 0 a := by
    change (s z).im ∈ Ioo 0 a
    rw [sim]
    exact hz'
  have h := marked_rectangle_open_vertical_side hb ha hB hA T' hbij' e' he'
    h0 hright htr htl y Y hy (E a b z) hzre hzim
  have hval : (e' (E a b z) : ℂ) = s (e z) := by
    change s (e (E b a (E a b z))) = s (e z)
    have hzEq : E b a (E a b z) = z := Subtype.ext (ss z)
    rw [hzEq]
  simpa only [hval, sre, sim] using h


/-- A homeomorphism of closed rectangles with the four marked corners and
exact interior correspondence preserves both coordinate sides. This form
eliminates the arbitrary ambient representative from the two side theorems. -/
lemma marked_rectangle_coordinate_sides
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (e : Complex.reProdIm (Icc 0 a) (Icc 0 b) ≃ₜ
      Complex.reProdIm (Icc 0 A) (Icc 0 B))
    (hinterior : ∀ z, (e z : ℂ) ∈ Complex.reProdIm (Ioo 0 A) (Ioo 0 B) ↔
      (z : ℂ) ∈ Complex.reProdIm (Ioo 0 a) (Ioo 0 b))
    (h_zero : (e ⟨0, by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = 0)
    (h_right : (e ⟨(a : ℂ), by simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ))
    (h_top_right : (e ⟨(a : ℂ) + (b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ) + (B : ℂ) * Complex.I)
    (h_top_left : (e ⟨(b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (B : ℂ) * Complex.I) :
    (∀ z : Complex.reProdIm (Icc 0 a) (Icc 0 b),
      (z : ℂ).im ∈ Ioo 0 b →
        ((z : ℂ).re = 0 → (e z : ℂ).re = 0) ∧
        ((z : ℂ).re = a → (e z : ℂ).re = A)) ∧
    (∀ z : Complex.reProdIm (Icc 0 a) (Icc 0 b),
      (z : ℂ).re ∈ Ioo 0 a →
        ((z : ℂ).im = 0 → (e z : ℂ).im = 0) ∧
        ((z : ℂ).im = b → (e z : ℂ).im = B)) := by
  classical
  let R := Complex.reProdIm (Icc 0 a) (Icc 0 b)
  let T : ℂ → ℂ := Function.extend Subtype.val (fun z : R ↦ (e z : ℂ)) (fun _ ↦ 0)
  have hT (z : R) : T z = (e z : ℂ) := Subtype.val_injective.extend_apply _ _ z
  have hRsub : Complex.reProdIm (Ioo 0 a) (Ioo 0 b) ⊆ R := by
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have htargetsub : Complex.reProdIm (Ioo 0 A) (Ioo 0 B) ⊆
      Complex.reProdIm (Icc 0 A) (Icc 0 B) := by
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hbij : BijOn T (Complex.reProdIm (Ioo 0 a) (Ioo 0 b))
      (Complex.reProdIm (Ioo 0 A) (Ioo 0 B)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [hT ⟨z, hRsub hz⟩]
      exact (hinterior _).mpr hz
    · intro z hz w hw heq
      rw [hT ⟨z, hRsub hz⟩, hT ⟨w, hRsub hw⟩] at heq
      exact congrArg Subtype.val (e.injective (Subtype.ext heq))
    · intro w hw
      let z := e.symm ⟨w, htargetsub hw⟩
      have hz : (z : ℂ) ∈ Complex.reProdIm (Ioo 0 a) (Ioo 0 b) :=
        (hinterior z).mp (by simpa [z] using hw)
      exact ⟨z, hz, (hT z).trans (congrArg Subtype.val (e.apply_symm_apply _))⟩
  have hext : ∀ z : R, (z : ℂ) ∈ Complex.reProdIm (Ioo 0 a) (Ioo 0 b) →
      (e z : ℂ) = T z := fun z _ ↦ (hT z).symm
  constructor
  · intro z hz
    exact ⟨fun h ↦ (marked_rectangle_open_vertical_side ha hb hA hB T hbij e hext
      h_zero h_right h_top_right h_top_left 0 0 (Or.inl ⟨rfl, rfl⟩) z h hz).1,
      fun h ↦ (marked_rectangle_open_vertical_side ha hb hA hB T hbij e hext
      h_zero h_right h_top_right h_top_left a A (Or.inr ⟨rfl, rfl⟩) z h hz).1⟩
  · intro z hz
    exact ⟨fun h ↦ (marked_rectangle_open_horizontal_side ha hb hA hB T hbij e hext
      h_zero h_right h_top_right h_top_left 0 0 (Or.inl ⟨rfl, rfl⟩) z h hz).1,
      fun h ↦ (marked_rectangle_open_horizontal_side ha hb hA hB T hbij e hext
      h_zero h_right h_top_right h_top_left b B (Or.inr ⟨rfl, rfl⟩) z h hz).1⟩

end HolomorphicAnosov.Analysis

