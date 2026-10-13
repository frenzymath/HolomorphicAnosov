import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Defs

open Set

namespace HolomorphicAnosov.Analysis

/-- The original interior bijection and four corner marks force either open vertical side
of the closed-rectangle homeomorphism into the corresponding open target side.

Source: Farb–Margalit, Version 5.0, §11.5 Theorem 11.10, p.341, side-preservation
prerequisite. This agent-written adapter derives that prerequisite from the parent's
corner-marked boundary extension; it does not assume boundary values of the total T.

Proof: surjectivity of T on interiors and injectivity of e exclude an interior image
of a side point. Injectivity and the four marks exclude every corner as an image of
an open side point. The continuous image of the open source side is preconnected;
closed-set separation confines it first to vertical or horizontal lines, and then
to one line. Continuity at the two marked endpoints selects the marked vertical line. Corner
avoidance makes the output height inequalities strict. No holomorphy is needed. -/
theorem marked_rectangle_open_vertical_side
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (T : ℂ → ℂ)
    (h_bijective : Set.BijOn T ((Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b))) ((Complex.reProdIm (Set.Ioo 0 A) (Set.Ioo 0 B))))
    (e : (Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)) ≃ₜ (Complex.reProdIm (Set.Icc 0 A) (Set.Icc 0 B)))
    (h_extension : ∀ z : (Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)),
      (z : ℂ) ∈ (Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)) → (e z : ℂ) = T z)
    (h_zero : (e ⟨0, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = 0)
    (h_right : (e ⟨(a : ℂ), by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ))
    (h_top_right : (e ⟨(a : ℂ) + (b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) =
      (A : ℂ) + (B : ℂ) * Complex.I)
    (h_top_left : (e ⟨(b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) =
      (B : ℂ) * Complex.I)
    (x X : ℝ) (hx : (x = 0 ∧ X = 0) ∨ (x = a ∧ X = A)) :
    ∀ z : Complex.reProdIm (Icc 0 a) (Icc 0 b), (z : ℂ).re = x →
      (z : ℂ).im ∈ Ioo 0 b →
      (e z : ℂ).re = X ∧ (e z : ℂ).im ∈ Ioo 0 B := by
  let R := Complex.reProdIm (Icc 0 a) (Icc 0 b)
  let E : ℂ → ℂ := Function.extend Subtype.val (fun z : R ↦ (e z : ℂ)) (fun _ ↦ 0)
  have hE (z : ℂ) (hz : z ∈ R) : E z = (e ⟨z, hz⟩ : ℂ) :=
    Subtype.val_injective.extend_apply _ _ ⟨z, hz⟩
  have hEc : ContinuousOn E R := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (fun z : R ↦ E z) = (fun z : R ↦ (e z : ℂ)) :=
      funext fun z ↦ hE z z.property
    change Continuous (fun z : R ↦ E z)
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have hpath (t : ℝ) (ht : t ∈ Icc 0 b) : (x : ℂ) + (t : ℂ) * Complex.I ∈ R := by
    rcases hx with ⟨rfl, hX⟩ | ⟨rfl, hX⟩ <;>
      simpa [R, Complex.mem_reProdIm, ha.le] using ht
  let g : ℝ → ℂ := fun t ↦ E ((x : ℂ) + (t : ℂ) * Complex.I)
  have hg : ContinuousOn g (Icc 0 b) :=
    hEc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn hpath
  have hgE (t : ℝ) (ht : t ∈ Icc 0 b) :
      g t = (e ⟨(x : ℂ) + (t : ℂ) * Complex.I, hpath t ht⟩ : ℂ) := hE _ _
  have hzero : g 0 = (X : ℂ) := by
    rw [hgE 0 (left_mem_Icc.mpr hb.le)]
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using h_zero
    · simpa using h_right
  have htop : g b = (X : ℂ) + (B : ℂ) * Complex.I := by
    rw [hgE b (right_mem_Icc.mpr hb.le)]
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using h_top_left
    · exact h_top_right
  have hboundary : ∀ t ∈ Ioo 0 b,
      (g t).re = 0 ∨ (g t).re = A ∨ (g t).im = 0 ∨ (g t).im = B := by
    intro t ht
    let z : R := ⟨(x : ℂ) + (t : ℂ) * Complex.I, hpath t (Ioo_subset_Icc_self ht)⟩
    have heq : g t = (e z : ℂ) := hgE t (Ioo_subset_Icc_self ht)
    have hclosed := (e z).property
    rw [← heq] at hclosed
    simp only [Complex.mem_reProdIm, mem_Icc] at hclosed
    by_contra hn
    push Not at hn
    have hi : g t ∈ Complex.reProdIm (Ioo 0 A) (Ioo 0 B) := by
      simp only [Complex.mem_reProdIm, mem_Ioo]
      exact ⟨⟨lt_of_le_of_ne hclosed.1.1 (Ne.symm hn.1),
        lt_of_le_of_ne hclosed.1.2 hn.2.1⟩,
        ⟨lt_of_le_of_ne hclosed.2.1 (Ne.symm hn.2.2.1),
        lt_of_le_of_ne hclosed.2.2 hn.2.2.2⟩⟩
    obtain ⟨w, hw, hTw⟩ := h_bijective.surjOn hi
    have hwR : w ∈ R := ⟨⟨hw.1.1.le, hw.1.2.le⟩, ⟨hw.2.1.le, hw.2.2.le⟩⟩
    have he : e ⟨w, hwR⟩ = e z := Subtype.ext ((h_extension ⟨w, hwR⟩ hw).trans
      (hTw.trans heq))
    have hzw : w = (x : ℂ) + (t : ℂ) * Complex.I := congrArg Subtype.val (e.injective he)
    have hre := congrArg Complex.re hzw
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Complex.add_re, add_zero] at hre
    rcases hx with ⟨hx, hX⟩ | ⟨hx, hX⟩
    · exact (ne_of_gt hw.1.1) (hre.trans hx)
    · exact hw.1.2.ne (hre.trans hx)
  have hcorners : ∀ t ∈ Ioo 0 b,
      ¬ (((g t).re = 0 ∨ (g t).re = A) ∧ ((g t).im = 0 ∨ (g t).im = B)) := by
    intro t ht h
    let z : R := ⟨(x : ℂ) + (t : ℂ) * Complex.I, hpath t (Ioo_subset_Icc_self ht)⟩
    have heq : g t = (e z : ℂ) := hgE t (Ioo_subset_Icc_self ht)
    rcases h with ⟨hr | hr, hi | hi⟩
    · have hval : (e z : ℂ) = 0 := by rw [← heq]; exact Complex.ext hr hi
      have hz := e.injective (Subtype.ext (hval.trans h_zero.symm))
      have him := congrArg (fun w : R ↦ (w : ℂ).im) hz
      simp [z] at him
      exact ht.1.ne' him
    · have hval : (e z : ℂ) = (B : ℂ) * Complex.I := by
        rw [← heq]; apply Complex.ext <;> simpa using ‹_›
      have hz := e.injective (Subtype.ext (hval.trans h_top_left.symm))
      have him := congrArg (fun w : R ↦ (w : ℂ).im) hz
      simp [z] at him
      exact ht.2.ne him
    · have hval : (e z : ℂ) = (A : ℂ) := by
        rw [← heq]; apply Complex.ext <;> simpa using ‹_›
      have hz := e.injective (Subtype.ext (hval.trans h_right.symm))
      have him := congrArg (fun w : R ↦ (w : ℂ).im) hz
      simp [z] at him
      exact ht.1.ne' him
    · have hval : (e z : ℂ) = (A : ℂ) + (B : ℂ) * Complex.I := by
        rw [← heq]; apply Complex.ext <;> simpa using ‹_›
      have hz := e.injective (Subtype.ext (hval.trans h_top_right.symm))
      have him := congrArg (fun w : R ↦ (w : ℂ).im) hz
      simp [z] at him
      exact ht.2.ne him
  have hcurve : ∀ t ∈ Icc 0 b, (g t).re = X := by
    let s : Set ℂ := g '' Ioo 0 b
    have hs : IsPreconnected s := isPreconnected_Ioo.image g (hg.mono Ioo_subset_Icc_self)
    have hsep {u v : Set ℂ} (hu : IsClosed u) (hv : IsClosed v)
        (hcover : s ⊆ u ∪ v) (hdis : ∀ z ∈ s, ¬ (z ∈ u ∧ z ∈ v)) :
        s ⊆ u ∨ s ⊆ v := by
      exact isPreconnected_iff_subset_of_disjoint_closed.mp hs u v hu hv hcover
        (by
          ext z
          exact ⟨fun hz ↦ (hdis z hz.1 hz.2).elim, fun hz ↦ hz.elim⟩)
    have hr0 : IsClosed {z : ℂ | z.re = 0} := isClosed_eq Complex.continuous_re continuous_const
    have hra : IsClosed {z : ℂ | z.re = A} := isClosed_eq Complex.continuous_re continuous_const
    have hi0 : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
    have hiB : IsClosed {z : ℂ | z.im = B} := isClosed_eq Complex.continuous_im continuous_const
    have hcover : s ⊆ ({z : ℂ | z.re = 0} ∪ {z : ℂ | z.re = A}) ∪
        ({z : ℂ | z.im = 0} ∪ {z : ℂ | z.im = B}) := by
      rintro z ⟨t, ht, rfl⟩
      simpa only [mem_union, mem_ofPred_eq, or_assoc] using hboundary t ht
    have hdis : ∀ z ∈ s, ¬ (z ∈ ({z : ℂ | z.re = 0} ∪ {z : ℂ | z.re = A}) ∧
        z ∈ ({z : ℂ | z.im = 0} ∪ {z : ℂ | z.im = B})) := by
      rintro z ⟨t, ht, rfl⟩
      exact hcorners t ht
    have hclosure : Icc (0 : ℝ) b ⊆ closure (Ioo 0 b) := by rw [closure_Ioo hb.ne]
    rcases hsep (hr0.union hra) (hi0.union hiB) hcover hdis with hv | hh
    · rcases hsep hr0 hra hv (by
        intro z hz h
        have := h.2.symm.trans h.1
        exact hA.ne' this) with hl | hr
      · have heq := (show EqOn (fun t ↦ (g t).re) (fun _ ↦ 0) (Ioo 0 b) from
          fun t ht ↦ hl ⟨t, ht, rfl⟩).of_subset_closure
            (Complex.continuous_re.comp_continuousOn hg) continuousOn_const
            Ioo_subset_Icc_self hclosure
        have hX : X = 0 := by simpa [hzero] using heq (left_mem_Icc.mpr hb.le)
        exact fun t ht ↦ (heq ht).trans hX.symm
      · have heq := (show EqOn (fun t ↦ (g t).re) (fun _ ↦ A) (Ioo 0 b) from
          fun t ht ↦ hr ⟨t, ht, rfl⟩).of_subset_closure
            (Complex.continuous_re.comp_continuousOn hg) continuousOn_const
            Ioo_subset_Icc_self hclosure
        have hX : X = A := by simpa [hzero] using heq (left_mem_Icc.mpr hb.le)
        exact fun t ht ↦ (heq ht).trans hX.symm
    · rcases hsep hi0 hiB hh (by
        intro z hz h
        have := h.2.symm.trans h.1
        exact hB.ne' this) with hbottom | htop'
      · have heq := (show EqOn (fun t ↦ (g t).im) (fun _ ↦ 0) (Ioo 0 b) from
          fun t ht ↦ hbottom ⟨t, ht, rfl⟩).of_subset_closure
            (Complex.continuous_im.comp_continuousOn hg) continuousOn_const
            Ioo_subset_Icc_self hclosure
        have h := heq (right_mem_Icc.mpr hb.le)
        simp only [htop, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, Complex.add_im, zero_add] at h
        exact (hB.ne' h).elim
      · have heq := (show EqOn (fun t ↦ (g t).im) (fun _ ↦ B) (Ioo 0 b) from
          fun t ht ↦ htop' ⟨t, ht, rfl⟩).of_subset_closure
            (Complex.continuous_im.comp_continuousOn hg) continuousOn_const
            Ioo_subset_Icc_self hclosure
        have h := heq (left_mem_Icc.mpr hb.le)
        simp only [hzero, Complex.ofReal_im] at h
        exact (hB.ne' h.symm).elim
  intro z hz hy
  have hzval : (z : ℂ) = (x : ℂ) + ((z : ℂ).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  have hgval : g (z : ℂ).im = (e z : ℂ) := by
    rw [hgE _ (Ioo_subset_Icc_self hy)]
    exact congrArg (fun w : R ↦ (e w : ℂ)) (Subtype.ext hzval.symm)
  have hre : (e z : ℂ).re = X := by
    rw [← hgval]
    exact hcurve _ (Ioo_subset_Icc_self hy)
  refine ⟨hre, ?_⟩
  have hc := (e z).property.2
  have hnc := hcorners _ hy
  rw [hgval] at hnc
  have hvertical : (e z : ℂ).re = 0 ∨ (e z : ℂ).re = A := by
    rcases hx with ⟨hx, hX⟩ | ⟨hx, hX⟩
    · exact Or.inl (hre.trans hX)
    · exact Or.inr (hre.trans hX)
  exact ⟨lt_of_le_of_ne hc.1 (by intro h; exact hnc ⟨hvertical, Or.inl h.symm⟩),
    lt_of_le_of_ne hc.2 (by intro h; exact hnc ⟨hvertical, Or.inr h⟩)⟩

end HolomorphicAnosov.Analysis

