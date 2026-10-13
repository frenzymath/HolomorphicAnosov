import Mathlib.Analysis.Complex.UnitDisc.Basic
import HolomorphicAnosov.Analysis.ChordCapSignReversal
import HolomorphicAnosov.Analysis.UnitCircleChordZeroDeterminant
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Basic

open Set
open scoped ComplexConjugate

namespace HolomorphicAnosov.Analysis

/-! # Chord-cap component transport

This is the geometric bridge in Tao, *246C Notes 2*, §2, Theorem 20: an
interior homeomorphism transports one of the two convex caps cut out by the
endpoint chord into the selected complementary component of the Jordan loop.
The source proof uses the component partition of the disk minus the chord and
homeomorphism transport of components. -/

/-- A nonempty component of the image disk minus an endpoint chord contains
the image of one entire strict chord cap.

Source: Tao, *246C Notes 2*, §2, Theorem 20, final proof paragraph.
Proof: `hfrange`, `hsource`, endpoint exclusion and injectivity of `e` identify
the preimage of `range j` with the open chord. The affine functional
`im (conj (ω-ζ) * (z-ζ))` vanishes exactly on its supporting line; within the
disk this line is precisely the open chord. The two strict sign sets are
nonempty convex caps: the chord midpoint is interior, and small displacements
in both normal directions give witnesses. Convexity makes each cap connected.
Choose `v ∈ V`. Component containment puts it in `Q \ range j`, so its inverse
image `b` under `e` lies in one strict cap. That whole cap is connected and its
image lies in `Q \ range j`, hence its image is contained in the component of
`v`, which is `V` by `hVcomponent`. Reversing the endpoints reverses the affine
functional, giving the second alternative when the original sign is positive.
No boundary regularity or continuity of `f` beyond the stated exact image
relations is needed. Distinct endpoints include the antipodal case. -/
theorem chord_cap_image_component
    (Q V : Set ℂ) (e : Complex.UnitDisc ≃ₜ Q) (j : Circle → ℂ)
    (ζ ω : Circle) (hDistinct : ζ ≠ ω)
    (f : ℝ → ℂ)
    (hcinterior : ∀ t : ℝ, t ∈ Ioo 0 1 →
      AffineMap.lineMap (ζ : ℂ) (ω : ℂ) t ∈ Metric.ball (0 : ℂ) 1)
    (hfrange : range j = f '' Icc 0 1)
    (hsource : ∀ (t : ℝ) (ht : t ∈ Ioo 0 1),
      f t = (e ⟨AffineMap.lineMap (ζ : ℂ) (ω : ℂ) t, hcinterior t ht⟩ : ℂ))
    (hendpoint : f 0 ∉ Q ∧ f 1 ∉ Q)
    (hVne : V.Nonempty)
    (hVcomponent : ∀ v ∈ V, connectedComponentIn (Q \ range j) v = V) :
    (∃ b : Complex.UnitDisc,
        (conj ((ω : ℂ) - ζ) * ((b : ℂ) - ζ)).im < 0 ∧
        ∀ z : Complex.UnitDisc,
          (conj ((ω : ℂ) - ζ) * ((z : ℂ) - ζ)).im < 0 → (e z : ℂ) ∈ V) ∨
      (∃ b : Complex.UnitDisc,
        (conj ((ζ : ℂ) - ω) * ((b : ℂ) - ω)).im < 0 ∧
        ∀ z : Complex.UnitDisc,
          (conj ((ζ : ℂ) - ω) * ((z : ℂ) - ω)).im < 0 → (e z : ℂ) ∈ V) := by
  have hpre (z : Complex.UnitDisc) : (e z : ℂ) ∈ range j ↔
      ∃ t : ℝ, ∃ ht : t ∈ Ioo 0 1,
        (z : ℂ) = AffineMap.lineMap (ζ : ℂ) (ω : ℂ) t := by
    rw [hfrange]
    constructor
    · rintro ⟨t, ht, heq⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hendpoint.1 (heq.symm ▸ (e z).property)
      have ht1 : t ≠ 1 := by
        rintro rfl
        exact hendpoint.2 (heq.symm ▸ (e z).property)
      have ht' : t ∈ Ioo 0 1 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      refine ⟨t, ht', ?_⟩
      have he : e ⟨AffineMap.lineMap (ζ : ℂ) (ω : ℂ) t, hcinterior t ht'⟩ = e z :=
        Subtype.ext ((hsource t ht').symm.trans heq)
      exact (congrArg (fun x : Complex.UnitDisc ↦ (x : ℂ)) (e.injective he)).symm
    · rintro ⟨t, ht, hz⟩
      refine ⟨t, Ioo_subset_Icc_self ht, ?_⟩
      rw [hsource t ht]
      have hz' : (⟨AffineMap.lineMap (ζ : ℂ) (ω : ℂ) t,
          hcinterior t ht⟩ : Complex.UnitDisc) = z := Subtype.ext hz.symm
      rw [hz']
  have hlinezero (t : ℝ) :
      (conj ((ω : ℂ) - ζ) *
        (AffineMap.lineMap (ζ : ℂ) (ω : ℂ) t - ζ)).im = 0 := by
    rw [AffineMap.lineMap_apply_module]
    simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hreverse (z : ℂ) :
      (conj ((ζ : ℂ) - ω) * (z - ω)).im =
        -(conj ((ω : ℂ) - ζ) * (z - ζ)).im := by
    exact chord_cap_sign_reversal (ζ := (ζ : ℂ)) (ω := (ω : ℂ)) z
  have hmap (a d : ℂ) (b : Complex.UnitDisc)
      (hb : (conj d * ((b : ℂ) - a)).im < 0) (heb : (e b : ℂ) ∈ V)
      (havoid : ∀ z : Complex.UnitDisc,
        (conj d * ((z : ℂ) - a)).im < 0 → (e z : ℂ) ∉ range j) :
      ∀ z : Complex.UnitDisc,
        (conj d * ((z : ℂ) - a)).im < 0 → (e z : ℂ) ∈ V := by
    let A : Set ℂ := {z | z ∈ Metric.ball (0 : ℂ) 1 ∧ (conj d * (z - a)).im < 0}
    let B : Set Complex.UnitDisc := {z | (conj d * ((z : ℂ) - a)).im < 0}
    have hA : Convex ℝ A := by
      intro x hx y hy r s hr hs hrs
      refine ⟨convex_ball (0 : ℂ) 1 hx.1 hy.1 hr hs hrs, ?_⟩
      have hlin : (conj d * (r • x + s • y - a)).im =
          r * (conj d * (x - a)).im + s * (conj d * (y - a)).im := by
        have hr' : r = 1 - s := by linarith
        rw [hr']
        simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re, Complex.sub_re,
          Complex.sub_im, Complex.add_re, Complex.add_im, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      change (conj d * (r • x + s • y - a)).im < 0
      rw [hlin]
      have hx' := hx.2
      have hy' := hy.2
      by_cases hr0 : r = 0
      · have hs1 : s = 1 := by linarith
        simpa [hr0, hs1] using hy'
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg
          (lt_of_le_of_ne hr (Ne.symm hr0)) hx') (mul_nonpos_of_nonneg_of_nonpos hs hy'.le)
    have himage : ((↑) : Complex.UnitDisc → ℂ) '' B = A := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.property, hw⟩
      · intro hz
        exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
    have hB : IsPreconnected B := by
      apply Complex.UnitDisc.isEmbedding_coe.isInducing.isPreconnected_image.mp
      rw [himage]
      exact hA.isPreconnected
    have hC := hB.image (fun z ↦ (e z : ℂ))
      (continuous_subtype_val.comp e.continuous).continuousOn
    have hsub : (fun z ↦ (e z : ℂ)) '' B ⊆ Q \ range j := by
      rintro x ⟨z, hz, rfl⟩
      exact ⟨(e z).property, havoid z hz⟩
    have hcomp := hC.subset_connectedComponentIn (mem_image_of_mem _ hb) hsub
    rw [hVcomponent (e b) heb] at hcomp
    intro z hz
    exact hcomp (mem_image_of_mem _ hz)
  obtain ⟨v, hv⟩ := hVne
  have hvS : v ∈ Q \ range j := by
    have hsub := connectedComponentIn_subset (Q \ range j) v
    rw [hVcomponent v hv] at hsub
    exact hsub hv
  let b : Complex.UnitDisc := e.symm ⟨v, hvS.1⟩
  have heb : (e b : ℂ) = v := by simp [b]
  have hbne : (conj ((ω : ℂ) - ζ) * ((b : ℂ) - ζ)).im ≠ 0 := by
    intro hb
    obtain ⟨t, ht, heq⟩ := unit_circle_chord_zero_determinant
      (ζ : ℂ) (ω : ℂ) (b : ℂ) (fun h ↦ hDistinct (Subtype.ext h))
      (by simp) (by simp) b.norm_lt_one hb
    exact hvS.2 (heb ▸ (hpre b).mpr ⟨t, ht, heq⟩)
  rcases lt_or_gt_of_ne hbne with hb | hb
  · refine Or.inl ⟨b, hb, hmap (ζ : ℂ) ((ω : ℂ) - ζ) b hb (heb ▸ hv) ?_⟩
    intro z hz hJ
    obtain ⟨t, ht, heq⟩ := (hpre z).mp hJ
    rw [heq, hlinezero] at hz
    exact (lt_irrefl 0) hz
  · have hb' : (conj ((ζ : ℂ) - ω) * ((b : ℂ) - ω)).im < 0 := by
      rw [hreverse]
      linarith
    refine Or.inr ⟨b, hb', hmap (ω : ℂ) ((ζ : ℂ) - ω) b hb' (heb ▸ hv) ?_⟩
    intro z hz hJ
    obtain ⟨t, ht, heq⟩ := (hpre z).mp hJ
    rw [hreverse, heq, hlinezero, neg_zero] at hz
    exact (lt_irrefl 0) hz

end HolomorphicAnosov.Analysis
