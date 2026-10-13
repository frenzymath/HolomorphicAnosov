import HolomorphicAnosov.Analysis.MarkedRectangleG3BoundarySegmentClosure

/-! Horizontal straight-side closure, obtained by rotating the vertical-side
statement. Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010), pp.189--190. -/

open Set
noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- A continuous horizontal side whose real coordinate is strictly increasing on
the interior and whose imaginary coordinate is constant there covers exactly the
closed horizontal segment between its endpoint images. -/
theorem complex_horizontal_side_coverage
    {a b c : ℝ} (hab : a < b) (F : ℝ → ℂ)
    (hc : ContinuousOn F (Icc a b))
    (hm : StrictMonoOn (fun t ↦ (F t).re) (Ioo a b))
    (himag : ∀ t ∈ Ioo a b, (F t).im = c) :
    StrictMonoOn (fun t ↦ (F t).re) (Icc a b) ∧
      (∀ t ∈ Icc a b, (F t).im = c) ∧
      F '' Icc a b = Complex.reProdIm (Icc (F a).re (F b).re) {c} := by
  let G : ℝ → ℂ := fun t ↦ Complex.I * F t
  have hGc : ContinuousOn G (Icc a b) := by
    exact (continuousOn_const.mul hc : ContinuousOn (fun t ↦ Complex.I * F t) (Icc a b))
  have hGm : StrictMonoOn (fun t ↦ (G t).im) (Ioo a b) := by
    intro x hx y hy hxy
    simpa [G, Complex.mul_im] using hm hx hy hxy
  have hGre : ∀ t ∈ Ioo a b, (G t).re = -c := by
    intro t ht
    simp [G, Complex.mul_re, himag t ht]
  obtain ⟨hGmono, hGreClosed, hGimage⟩ :=
    complex_central_side_coverage hab G hGc hGm hGre
  have hmono : StrictMonoOn (fun t ↦ (F t).re) (Icc a b) := by
    simpa [G, Complex.mul_im] using hGmono
  have hconst : ∀ t ∈ Icc a b, (F t).im = c := by
    intro t ht
    have := hGreClosed t ht
    simpa [G, Complex.mul_re] using this
  refine ⟨hmono, hconst, ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨⟨hmono.monotoneOn (left_mem_Icc.mpr hab.le) ht ht.1,
      hmono.monotoneOn ht (right_mem_Icc.mpr hab.le) ht.2⟩, hconst t ht⟩
  · intro z hz
    have hz' : Complex.I * z ∈ Complex.reProdIm {-c} (Icc (G a).im (G b).im) := by
      constructor
      · change (Complex.I * z).re = -c
        simpa [Complex.mul_re] using congrArg Neg.neg hz.2
      · simpa [Complex.mul_im, G] using hz.1
    have hzG : Complex.I * z ∈ G '' Icc a b := hGimage.symm ▸ hz'
    obtain ⟨t, ht, htz⟩ := hzG
    refine ⟨t, ht, ?_⟩
    apply Complex.ext
    · simpa [G, Complex.mul_im] using congrArg Complex.im htz
    · simpa [G, Complex.mul_re] using congrArg Complex.re htz

end HolomorphicAnosov.Analysis.MarkedRectangle

