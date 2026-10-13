import HolomorphicAnosov.Analysis.Complex.QCMarkedCompleteSides
import HolomorphicAnosov.Analysis.Complex.QCCompleteSidesHalfTurn
import HolomorphicAnosov.Analysis.Complex.QCPartitionImageIdentification

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle
open scoped Pointwise

lemma qc_closed_rectangle_image_model {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℂ → ℂ) (hfc : ContinuousOn f (ClosedRectangle a b))
    (hinj : InjOn f (ClosedRectangle a b)) :
    ∃ e : ClosedRectangle a b ≃ₜ closure (f '' OpenRectangle a b),
      (∀ z, (e z : ℂ) = f z) ∧
      ∀ z, (e z : ℂ) ∈ f '' OpenRectangle a b ↔ (z : ℂ) ∈ OpenRectangle a b := by
  have hcl := RectangleModelPreparation.closure_openRectangle ha hb
  have hcompact : IsCompact (ClosedRectangle a b) := isCompact_Icc.reProdIm isCompact_Icc
  have hclosure : f '' ClosedRectangle a b = closure (f '' OpenRectangle a b) := by
    rw [← hcl] at hfc hcompact ⊢
    exact Subset.antisymm hfc.image_closure
      (closure_minimal (image_mono subset_closure) (hcompact.image_of_continuousOn hfc).isClosed)
  have : CompactSpace (ClosedRectangle a b) := isCompact_iff_compactSpace.mp hcompact
  let k : ClosedRectangle a b → ℂ := fun z ↦ f z
  have hkc : Continuous k := hfc.domRestrict
  have hki : Function.Injective k := fun z w h ↦ Subtype.ext (hinj z.property w.property h)
  have hkr : range k = closure (f '' OpenRectangle a b) := by
    rw [← hclosure]
    ext z
    exact ⟨fun ⟨w,hw⟩ ↦ ⟨w,w.property,hw⟩,fun ⟨w,hw,he⟩ ↦ ⟨⟨w,hw⟩,he⟩⟩
  let e := (hkc.isClosedEmbedding hki).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hkr)
  have he (z : ClosedRectangle a b) : (e z : ℂ) = f z := rfl
  refine ⟨e,he,?_⟩
  intro z
  rw [he]
  constructor
  · rintro ⟨w,hw,heq⟩
    have hwc : w ∈ ClosedRectangle a b := hcl ▸ subset_closure hw
    exact (hinj hwc z.property heq) ▸ hw
  · exact fun hz ↦ mem_image_of_mem f hz

lemma qc_complete_sides_of_rectangle_image {a b M m : ℝ}
    (ha : 0 < a) (hb : 0 < b) (f : ℂ → ℂ)
    (hfc : ContinuousOn f (ClosedRectangle a b)) (hinj : InjOn f (ClosedRectangle a b))
    (hmod : HasMarkedConformalModulus (f '' OpenRectangle a b)
      (fun i ↦ f (RectangleCorner a b i)) m)
    (hbottom : MapsTo f (ClosedRectangleSide a b 0) (ClosedRectangleSide M 1 0))
    (htop : MapsTo f (ClosedRectangleSide a b 2) (ClosedRectangleSide M 1 2)) :
    HasMarkedConformalModulusWithCompleteASides (f '' OpenRectangle a b)
      (fun i ↦ f (RectangleCorner a b i)) m M false := by
  obtain ⟨e,he,hint⟩ := qc_closed_rectangle_image_model ha hb f hfc hinj
  apply qc_complete_a_sides_of_boundary_model hmod ha hb e hint
  · intro i z hz
    rw [he,hz]
  · intro z hz
    simpa [he] using hbottom hz
  · intro z hz
    simpa [he] using htop hz

/-- Saturation of the marked moduli of every vertical split makes the normalized
homeomorphism preserve each left subrectangle. Transfer complete horizontal
sides to the two conformal models, rotate the right marking by a half-turn,
and apply two-piece rigidity. The fixed origin selects the left output strip;
the two seam marks and modulus uniqueness determine its width. Source:
Lehto–Virtanen I.Theorem 5.1, pp.28–29. -/
theorem qc_vertical_partition_images
    {M : ℝ} (hM : 0 < M) (f : ℂ → ℂ)
    (hfc : ContinuousOn f (ClosedRectangle M 1))
    (hinj : InjOn f (ClosedRectangle M 1))
    (hmap : MapsTo f (ClosedRectangle M 1) (ClosedRectangle M 1))
    (hbottom : MapsTo f (ClosedRectangleSide M 1 0) (ClosedRectangleSide M 1 0))
    (htop : MapsTo f (ClosedRectangleSide M 1 2) (ClosedRectangleSide M 1 2))
    (h0 : f 0 = 0) (hI : f Complex.I = Complex.I)
    (hopen : ∀ V : Set ℂ, IsOpen V → V ⊆ OpenRectangle M 1 → IsOpen (f '' V))
    (hmod : ∀ x ∈ Ioo 0 M,
      HasMarkedConformalModulus (f '' OpenRectangle x 1)
        (fun i ↦ f (RectangleCorner x 1 i)) x ∧
      HasMarkedConformalModulus (f '' ((x : ℂ) +ᵥ OpenRectangle (M - x) 1))
        (fun i ↦ f ((x : ℂ) + RectangleCorner (M - x) 1 i)) (M - x)) :
    ∀ x ∈ Ioo 0 M, f '' OpenRectangle x 1 = OpenRectangle x 1 := by
  intro x hx
  have hmx : 0 < M - x := sub_pos.mpr hx.2
  have hL : ClosedRectangle x 1 ⊆ ClosedRectangle M 1 := by
    intro z hz
    exact ⟨⟨hz.1.1,hz.1.2.trans hx.2.le⟩,hz.2⟩
  have hR : MapsTo (fun z : ℂ ↦ (x : ℂ) + z)
      (ClosedRectangle (M-x) 1) (ClosedRectangle M 1) := by
    intro z hz
    change (0 ≤ ((x : ℂ)+z).re ∧ ((x : ℂ)+z).re ≤ M) ∧
      (0 ≤ ((x : ℂ)+z).im ∧ ((x : ℂ)+z).im ≤ 1)
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_add]
    exact ⟨⟨by linarith [hz.1.1,hx.1],by linarith [hz.1.2]⟩,hz.2⟩
  have hLo : OpenRectangle x 1 ⊆ OpenRectangle M 1 := by
    intro z hz
    exact ⟨⟨hz.1.1,hz.1.2.trans hx.2⟩,hz.2⟩
  have hRo : (x : ℂ) +ᵥ OpenRectangle (M-x) 1 ⊆ OpenRectangle M 1 := by
    rintro z ⟨w,hw,rfl⟩
    change (0 < ((x : ℂ)+w).re ∧ ((x : ℂ)+w).re < M) ∧
      (0 < ((x : ℂ)+w).im ∧ ((x : ℂ)+w).im < 1)
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_add]
    exact ⟨⟨by linarith [hw.1.1,hx.1],by linarith [hw.1.2]⟩,hw.2⟩
  have hRc : OpenRectangle M 1 ⊆ ClosedRectangle M 1 := by
    rw [← RectangleModelPreparation.closure_openRectangle hM (by norm_num)]
    exact subset_closure
  obtain ⟨hmL,hmR⟩ := hmod x hx
  have hrimage : (fun z : ℂ ↦ f ((x : ℂ)+z)) '' OpenRectangle (M-x) 1 =
      f '' ((x : ℂ) +ᵥ OpenRectangle (M-x) 1) := by
    rw [← image_vadd,image_image]
    rfl
  have hrcont : ContinuousOn (fun z : ℂ ↦ f ((x : ℂ)+z)) (ClosedRectangle (M-x) 1) :=
    hfc.comp ((continuous_const.add continuous_id).continuousOn) hR
  have hrinj : InjOn (fun z : ℂ ↦ f ((x : ℂ)+z)) (ClosedRectangle (M-x) 1) := by
    intro z hz w hw heq
    exact add_left_cancel (hinj (hR hz) (hR hw) heq)
  have hLb : MapsTo f (ClosedRectangleSide x 1 0) (ClosedRectangleSide M 1 0) := by
    intro z hz
    exact hbottom ⟨⟨hz.1.1,hz.1.2.trans hx.2.le⟩,hz.2⟩
  have hLt : MapsTo f (ClosedRectangleSide x 1 2) (ClosedRectangleSide M 1 2) := by
    intro z hz
    exact htop ⟨⟨hz.1.1,hz.1.2.trans hx.2.le⟩,hz.2⟩
  have hRb : MapsTo (fun z : ℂ ↦ f ((x : ℂ)+z))
      (ClosedRectangleSide (M-x) 1 0) (ClosedRectangleSide M 1 0) := by
    intro z hz
    apply hbottom
    change (0 ≤ ((x : ℂ)+z).re ∧ ((x : ℂ)+z).re ≤ M) ∧ ((x : ℂ)+z).im = 0
    simp only [Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,zero_add]
    exact ⟨⟨by linarith [hz.1.1,hx.1],by linarith [hz.1.2]⟩,hz.2⟩
  have hRt : MapsTo (fun z : ℂ ↦ f ((x : ℂ)+z))
      (ClosedRectangleSide (M-x) 1 2) (ClosedRectangleSide M 1 2) := by
    intro z hz
    apply htop
    change (0 ≤ ((x : ℂ)+z).re ∧ ((x : ℂ)+z).re ≤ M) ∧ ((x : ℂ)+z).im = 1
    simp only [Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,zero_add]
    exact ⟨⟨by linarith [hz.1.1,hx.1],by linarith [hz.1.2]⟩,hz.2⟩
  have hsL := qc_complete_sides_of_rectangle_image hx.1 (by norm_num) f
    (hfc.mono hL) (hinj.mono hL) hmL hLb hLt
  have hsR := qc_complete_sides_of_rectangle_image hmx (by norm_num)
    (fun z : ℂ ↦ f ((x : ℂ)+z)) hrcont hrinj
    (by simpa only [hrimage] using hmR) hRb hRt
  rw [hrimage] at hsR
  have hclosed : IsClosed (ClosedRectangle M 1) :=
    (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  have hinside (V : Set ℂ) (hV : V ⊆ OpenRectangle M 1) :
      closure (f '' V) ⊆ closure (OpenRectangle M 1) := by
    rw [RectangleModelPreparation.closure_openRectangle hM (by norm_num)]
    exact closure_minimal (by rintro _ ⟨z,hz,rfl⟩; exact hmap (hRc (hV hz))) hclosed
  have hd : Disjoint (f '' OpenRectangle x 1)
      (f '' ((x : ℂ) +ᵥ OpenRectangle (M-x) 1)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u,hu,rfl⟩ ⟨v,hv,heq⟩
    have huv := hinj (hRc (hRo hv)) (hRc (hLo hu)) heq
    subst v
    obtain ⟨w,hw,he⟩ := hv
    have hre := congrArg Complex.re he
    simp only [vadd_eq_add,Complex.add_re,Complex.ofReal_re] at hre
    linarith [hu.1.2,hw.1.1]
  have hoR : IsOpen ((x : ℂ) +ᵥ OpenRectangle (M-x) 1) :=
    (RectangleModelPreparation.isOpen_openRectangle _ _).vadd _
  have hp := qc_partition_two_piece_rigidity M hM
    (f '' OpenRectangle x 1) (f '' ((x : ℂ) +ᵥ OpenRectangle (M-x) 1))
    (hopen _ (RectangleModelPreparation.isOpen_openRectangle _ _) hLo)
    (hopen _ hoR hRo) hd (hinside _ hLo) (hinside _ hRo)
    _ _ x (M-x) ⟨false,hsL,qc_complete_sides_half_turn hsR⟩ (by ring)
  have hcornL := qc_partition_marked_corners_mem_closure hmL
  have hcornR := qc_partition_marked_corners_mem_closure hmR
  have hzero : (0 : ℂ) ∈ closure (f '' OpenRectangle x 1) := by
    simpa [RectangleCorner,h0] using hcornL 0
  obtain ⟨c,hc,hcM,hPc,hPr,hseam⟩ := qc_partition_image_identification
    (qc_partition_piece_nonempty hmL) (qc_partition_piece_nonempty hmR) hzero hp
  have hwidth : x = c := by
    apply qc_partition_image_width hc hPc hmL
    · simpa [RectangleCorner] using h0
    · simpa [RectangleCorner] using hI
    · constructor
      · exact hcornL 1
      · simpa [RectangleCorner] using hcornR 0
    · constructor
      · exact hcornL 2
      · simpa [RectangleCorner] using hcornR 3
    · have hh := hbottom (show (x : ℂ) ∈ ClosedRectangleSide M 1 0 from
        ⟨⟨hx.1.le,hx.2.le⟩,by simp⟩)
      simpa [RectangleCorner] using hh.2
    · have hh := htop (show (x : ℂ)+Complex.I ∈ ClosedRectangleSide M 1 2 from
        ⟨by simpa using And.intro hx.1.le hx.2.le,by simp⟩)
      simpa [RectangleCorner] using hh.2
    · exact hseam
  exact hwidth ▸ hPc

end HolomorphicAnosov
