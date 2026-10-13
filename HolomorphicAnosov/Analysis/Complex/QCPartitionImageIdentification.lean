import HolomorphicAnosov.Analysis.Complex.QCPartitionTwoPieceRigidity
import HolomorphicAnosov.Analysis.Complex.QCMarkedModulusTransport

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle
open scoped Pointwise

lemma qc_translated_rectangle_nonempty_width {s a b : ℝ}
    (h : ((s : ℂ) +ᵥ OpenRectangle a b).Nonempty) : 0 < a := by
  obtain ⟨z,w,hw,rfl⟩ := h
  exact hw.1.1.trans hw.1.2

lemma qc_translated_rectangle_closure_re {s a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : z ∈ closure ((s : ℂ) +ᵥ OpenRectangle a b)) :
    s ≤ z.re ∧ z.re ≤ s + a := by
  rw [closure_vadd,RectangleModelPreparation.closure_openRectangle ha hb] at hz
  obtain ⟨w,hw,rfl⟩ := hz
  simp only [vadd_eq_add,Complex.add_re,Complex.ofReal_re]
  exact ⟨by linarith [hw.1.1],by linarith [hw.1.2]⟩

/-- The origin identifies the left piece in the translated two-strip conclusion.
Since both strips are nonempty, their widths are positive. The right strip has
strictly positive left endpoint and cannot contain the origin in its closure.
Thus the origin-containing piece is the left strip, whose left endpoint must
be zero. The intersection of the two closed strips has real coordinate equal
to their common endpoint. Source: the coordinate identification in the proof of
Lehto–Virtanen I.Theorem 5.1, after the equality case of I.Lemma 4.2. -/
theorem qc_partition_image_identification
    {M : ℝ} {P₁ P₂ : Set ℂ}
    (hne₁ : P₁.Nonempty) (hne₂ : P₂.Nonempty) (hzero : (0 : ℂ) ∈ closure P₁)
    (hpart : ∃ x₁ x₂ : ℝ, 0 ≤ x₁ ∧ x₁ ≤ x₂ ∧ x₂ ≤ M ∧
      ((P₁ = (x₁ : ℂ) +ᵥ OpenRectangle (x₂ - x₁) 1 ∧
          P₂ = (x₂ : ℂ) +ᵥ OpenRectangle (M - x₂) 1) ∨
       (P₁ = (x₂ : ℂ) +ᵥ OpenRectangle (M - x₂) 1 ∧
          P₂ = (x₁ : ℂ) +ᵥ OpenRectangle (x₂ - x₁) 1))) :
    ∃ c : ℝ, 0 < c ∧ c < M ∧ P₁ = OpenRectangle c 1 ∧
      P₂ = (c : ℂ) +ᵥ OpenRectangle (M - c) 1 ∧
      ∀ z ∈ closure P₁ ∩ closure P₂, z.re = c := by
  obtain ⟨x₁,x₂,h1,h12,h2,hord⟩ := hpart
  have hwidth : 0 < x₂ - x₁ ∧ 0 < M - x₂ := by
    rcases hord with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨qc_translated_rectangle_nonempty_width hne₁,
        qc_translated_rectangle_nonempty_width hne₂⟩
    · exact ⟨qc_translated_rectangle_nonempty_width hne₂,
        qc_translated_rectangle_nonempty_width hne₁⟩
  have h2pos : 0 < x₂ := by linarith [hwidth.1]
  have hleft : P₁ = (x₁ : ℂ) +ᵥ OpenRectangle (x₂ - x₁) 1 ∧
      P₂ = (x₂ : ℂ) +ᵥ OpenRectangle (M - x₂) 1 := by
    rcases hord with h | h
    · exact h
    · rw [h.1] at hzero
      have hh := (qc_translated_rectangle_closure_re hwidth.2 (by norm_num) hzero).1
      norm_num at hh
      linarith
  have hx₁ : x₁ = 0 := by
    rw [hleft.1] at hzero
    have hh := (qc_translated_rectangle_closure_re hwidth.1 (by norm_num) hzero).1
    norm_num at hh
    linarith
  subst x₁
  simp only [Complex.ofReal_zero,zero_vadd,sub_zero] at hleft
  refine ⟨x₂,h2pos,by linarith [hwidth.2],hleft.1,hleft.2,?_⟩
  intro z hz
  have hz₁ : z.re ≤ x₂ := by
    rw [hleft.1,RectangleModelPreparation.closure_openRectangle h2pos (by norm_num)] at hz
    exact hz.1.1.2
  have hz₂ : x₂ ≤ z.re := by
    have hh := hz.2
    rw [hleft.2] at hh
    exact (qc_translated_rectangle_closure_re hwidth.2 (by norm_num) hh).1
  exact le_antisymm hz₁ hz₂

/-- Once the seam identifies the two right marks of the left strip, marked
modulus uniqueness identifies its width. The zero and unit-imaginary marks
are the two fixed outer corners; the seam and horizontal-side equations
identify its two other corners. -/
theorem qc_partition_image_width
    {P₁ P₂ : Set ℂ} {p : Fin 4 → ℂ} {m c : ℝ} (hc : 0 < c)
    (hP : P₁ = OpenRectangle c 1)
    (hmod : HasMarkedConformalModulus P₁ p m)
    (h0 : p 0 = 0) (h3 : p 3 = Complex.I)
    (h1 : p 1 ∈ closure P₁ ∩ closure P₂) (h2 : p 2 ∈ closure P₁ ∩ closure P₂)
    (hb : (p 1).im = 0) (ht : (p 2).im = 1)
    (hseam : ∀ z ∈ closure P₁ ∩ closure P₂, z.re = c) : m = c := by
  have hp : p = RectangleCorner c 1 := by
    funext i
    fin_cases i
    · simpa [RectangleCorner] using h0
    · apply Complex.ext
      · simpa [RectangleCorner] using hseam _ h1
      · simpa [RectangleCorner] using hb
    · apply Complex.ext
      · simpa [RectangleCorner] using hseam _ h2
      · simpa [RectangleCorner] using ht
    · simpa [RectangleCorner] using h3
  rw [hP,hp] at hmod
  simpa using HolomorphicAnosov.HasMarkedConformalModulus.unique hmod (qc_identity_rectangle_modulus hc (by norm_num))

/-- Preservation of every left open subrectangle fixes the real coordinate.
If a point and its image have different real coordinates, a cut strictly
between the two separates their membership in the same left subrectangle,
contradicting the image identity and injectivity. -/
theorem qc_rectangle_real_of_left_images
    {M : ℝ} {f : ℂ → ℂ}
    (hf : MapsTo f (OpenRectangle M 1) (OpenRectangle M 1))
    (hinj : InjOn f (OpenRectangle M 1))
    (hleft : ∀ x ∈ Ioo 0 M, f '' OpenRectangle x 1 = OpenRectangle x 1) :
    ∀ z ∈ OpenRectangle M 1, (f z).re = z.re := by
  intro z hz
  have hw := hf hz
  have hmem (x : ℝ) (hx : x ∈ Ioo 0 M) :
      z ∈ OpenRectangle x 1 ↔ f z ∈ OpenRectangle x 1 := by
    constructor
    · intro hzx
      rw [← hleft x hx]
      exact mem_image_of_mem f hzx
    · intro hfx
      rw [← hleft x hx] at hfx
      obtain ⟨w,hw',heq⟩ := hfx
      have hwM : w ∈ OpenRectangle M 1 :=
        ⟨⟨hw'.1.1,hw'.1.2.trans hx.2⟩,hw'.2⟩
      exact (hinj hwM hz heq) ▸ hw'
  apply le_antisymm
  · by_contra h
    have hlt : z.re < (f z).re := lt_of_not_ge h
    let x := (z.re + (f z).re) / 2
    have hx : x ∈ Ioo 0 M := ⟨by dsimp [x]; linarith [hz.1.1,hw.1.1],
      by dsimp [x]; linarith [hz.1.2,hw.1.2]⟩
    have hzx : z ∈ OpenRectangle x 1 :=
      ⟨⟨hz.1.1,by dsimp [x]; linarith⟩,hz.2⟩
    have hfx := ((hmem x hx).mp hzx).1.2
    dsimp [x] at hfx
    linarith
  · by_contra h
    have hlt : (f z).re < z.re := lt_of_not_ge h
    let x := (z.re + (f z).re) / 2
    have hx : x ∈ Ioo 0 M := ⟨by dsimp [x]; linarith [hz.1.1,hw.1.1],
      by dsimp [x]; linarith [hz.1.2,hw.1.2]⟩
    have hfx : f z ∈ OpenRectangle x 1 :=
      ⟨⟨hw.1.1,by dsimp [x]; linarith⟩,hw.2⟩
    have hzx := ((hmem x hx).mpr hfx).1.2
    dsimp [x] at hzx
    linarith

end HolomorphicAnosov
