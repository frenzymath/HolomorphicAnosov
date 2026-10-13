import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Schwarz reflection across a real boundary

Source: Shaun Bullett, *MTH6111 Complex Analysis 2010–11*, Section V,
Proposition 23.1 and its proof, printed p. 3. The DAG node is
`analysis.schwarz_real_boundary_extension_g6_20261007`.

The given function has the closed upper part of an arbitrary conjugation-invariant open set
as its subtype domain. The reflected function has the original open set as its subtype domain.
`Function.extend Subtype.val _ (fun _ ↦ 0)` is used only to state complex differentiability
with Mathlib's ambient `DifferentiableOn`: it agrees with the subtype function on its domain,
and values outside that domain have no effect on holomorphy on the indicated open sets.
No connectedness of the open set, boundary derivative, or injectivity is assumed.
-/

namespace HolomorphicAnosov

open scoped ComplexConjugate
open Set Complex MeasureTheory

noncomputable section

/-- The literal Schwarz reflection: use the given function on the closed upper part and
the conjugate of its value at the conjugate point on the lower part. Source: Bullett,
Section V, Proposition 23.1, printed p. 3. The domain-membership proofs use only conjugation
invariance and the sign of the imaginary part. -/
def schwarzRealBoundaryExtension {U : Set ℂ}
    (hconj : ∀ z ∈ U, conj z ∈ U)
    (f : {z : ℂ // z ∈ U ∧ 0 ≤ z.im} → ℂ) : U → ℂ :=
  fun z ↦ if h : 0 ≤ (z : ℂ).im then f ⟨z, z.property, h⟩
    else conj (f ⟨conj (z : ℂ), hconj z z.property,
      by simpa only [Complex.conj_im, neg_nonneg] using le_of_lt (lt_of_not_ge h)⟩)

/-- Schwarz reflection for a function continuous up to its real boundary.

Source: Bullett, Section V, Proposition 23.1 and full proof, printed p. 3;
DAG node `analysis.schwarz_real_boundary_extension_g6_20261007`. The local proof also
applies when the conjugation-invariant open set is disconnected.

Proof: On the real axis the two formulas agree because the boundary values have imaginary
part zero. Near each real point, paste the continuous upper and lower formulas on the closed
halves of a disk contained in `U`; away from the real axis continuity is immediate. The formula
also gives conjugation symmetry and agreement with `f` on the closed upper part.

The given differentiability proves holomorphy on the upper part. On the lower part use the
conjugation-sandwich differentiability theorem
`mathlib.complex_differentiableAt_conj_conj_iff`. Around a real point choose a small symmetric
disk contained in `U`. Every axis-parallel rectangle in this disk has zero contour integral:
for a rectangle in a closed half-plane use the continuous-boundary rectangular Cauchy theorem
`mathlib.complex_cauchy_rectangle_continuous_boundary`; for one crossing the real axis split
at height zero and cancel the common horizontal segment. Continuity makes the edge integrals
integrable, and `mathlib.intervalIntegral_integral_add_adjacent_intervals_g5` joins the divided
vertical edges, with `mathlib.continuousOn_intervalIntegrable` providing integrability.
Degenerate rectangles cancel directly. The resulting rectangular conservative property and
continuity imply holomorphy by `mathlib.complex_morera_conservative_continuous`. These local
disks cover the real points and, with the two open half-parts, cover `U`. The argument is local;
it does not assume that every loop in `U` bounds a region contained in `U`.
-/
theorem schwarz_real_boundary_extension {U : Set ℂ}
    (hU : IsOpen U) (hconj : ∀ z ∈ U, conj z ∈ U)
    (f : {z : ℂ // z ∈ U ∧ 0 ≤ z.im} → ℂ)
    (hf_cont : Continuous f)
    (hf_holo : DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ ↦ 0))
      {z : ℂ | z ∈ U ∧ 0 < z.im})
    (hf_real : ∀ z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}, (z : ℂ).im = 0 → (f z).im = 0) :
    let F := schwarzRealBoundaryExtension hconj f
    DifferentiableOn ℂ (Function.extend Subtype.val F (fun _ ↦ 0)) U ∧
      Continuous F ∧
      (∀ z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}, F ⟨z, z.property.1⟩ = f z) ∧
      (∀ z : U, F ⟨conj (z : ℂ), hconj z z.property⟩ = conj (F z)) := by
  dsimp only
  let F := schwarzRealBoundaryExtension hconj f
  have hF_upper (z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}) :
      F ⟨z, z.property.1⟩ = f z := by
    simp only [F, schwarzRealBoundaryExtension]
    split_ifs with h
    · rfl
    · exact False.elim (h z.property.2)
  have hF_conj (z : U) :
      F ⟨conj (z : ℂ), hconj z z.property⟩ = conj (F z) := by
    by_cases hz : 0 ≤ (z : ℂ).im
    · by_cases hzi : (z : ℂ).im = 0
      · have he : conj (z : ℂ) = z := Complex.ext (by simp) (by simp [hzi])
        have hfr : conj (f ⟨z, z.property, hz⟩) = f ⟨z, z.property, hz⟩ :=
          Complex.ext (by simp) (by simp [hf_real ⟨z, z.property, hz⟩ hzi])
        simp [F, schwarzRealBoundaryExtension, hz, he, hfr]
      · have hn : ¬ (z : ℂ).im ≤ 0 := not_le.mpr (lt_of_le_of_ne hz (Ne.symm hzi))
        simp [F, schwarzRealBoundaryExtension, hz, hn]
    · have hz' : (z : ℂ).im ≤ 0 := (lt_of_not_ge hz).le
      simp [F, schwarzRealBoundaryExtension, hz, hz']
  have hF_cont : Continuous F := by
    let S : Set U := {z | 0 ≤ (z : ℂ).im}
    let T : Set U := {z | (z : ℂ).im ≤ 0}
    have him : Continuous (fun z : U ↦ (z : ℂ).im) :=
      Complex.continuous_im.comp continuous_subtype_val
    have hS : IsClosed S := isClosed_le continuous_const him
    have hT : IsClosed T := isClosed_le him continuous_const
    have hupper : ContinuousOn F S := by
      rw [continuousOn_iff_continuous_domRestrict]
      let ι : S → {z : ℂ // z ∈ U ∧ 0 ≤ z.im} :=
        fun z ↦ ⟨z.1.1, z.1.2, z.2⟩
      have hι : Continuous ι :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      exact (hf_cont.comp hι).congr (fun z ↦ (hF_upper (ι z)).symm)
    have hlower : ContinuousOn F T := by
      rw [continuousOn_iff_continuous_domRestrict]
      let ι : T → {z : ℂ // z ∈ U ∧ 0 ≤ z.im} :=
        fun z ↦ ⟨conj z.1.1, hconj z.1.1 z.1.2, by
          have hz : (z.1 : ℂ).im ≤ 0 := z.2
          simpa only [Complex.conj_im, neg_nonneg] using hz⟩
      have hι : Continuous ι :=
        (Complex.continuous_conj.comp
          (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
      refine (Complex.continuous_conj.comp (hf_cont.comp hι)).congr ?_
      intro z
      calc
        conj (f (ι z)) = conj (F ⟨(ι z : ℂ), (ι z).property.1⟩) := by
          exact congrArg conj (hF_upper (ι z)).symm
        _ = F z.1 := by
          simpa only [Complex.conj_conj] using congrArg conj (hF_conj z.1)
    have hcover : S ∪ T = Set.univ := by
      ext z
      simp only [S, T, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact le_total 0 (z : ℂ).im
    exact continuousOn_univ.mp (hcover ▸ hupper.union_of_isClosed hlower hS hT)
  let G := Function.extend Subtype.val F (fun _ ↦ 0)
  let g := Function.extend Subtype.val f (fun _ ↦ 0)
  have hG_val (z : U) : G z = F z := Subtype.val_injective.extend_apply _ _ z
  have hg_val (z : {z : ℂ // z ∈ U ∧ 0 ≤ z.im}) : g z = f z :=
    Subtype.val_injective.extend_apply _ _ z
  have hG_upper (z : ℂ) (hz : z ∈ U ∧ 0 ≤ z.im) : G z = g z := by
    calc
      G z = F ⟨z, hz.1⟩ := hG_val ⟨z, hz.1⟩
      _ = f ⟨z, hz⟩ := hF_upper ⟨z, hz⟩
      _ = g z := (hg_val ⟨z, hz⟩).symm
  have hG_lower (z : ℂ) (hz : z ∈ U ∧ z.im ≤ 0) : G z = conj (g (conj z)) := by
    have hzc : conj z ∈ U ∧ 0 ≤ (conj z).im :=
      ⟨hconj z hz.1, by simpa using hz.2⟩
    calc
      G z = F ⟨z, hz.1⟩ := hG_val ⟨z, hz.1⟩
      _ = conj (F ⟨conj z, hzc.1⟩) := by
        simp only [hF_conj ⟨z, hz.1⟩, Complex.conj_conj]
      _ = conj (G (conj z)) := congrArg conj (hG_val ⟨conj z, hzc.1⟩).symm
      _ = conj (g (conj z)) := congrArg conj (hG_upper _ hzc)
  have hG_cont : ContinuousOn G U := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hF_cont.congr (fun z ↦ (hG_val z).symm)
  have hopen : IsOpen {z : ℂ | z ∈ U ∧ 0 < z.im} :=
    hU.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hopen' : IsOpen {z : ℂ | z ∈ U ∧ z.im < 0} :=
    hU.inter (isOpen_lt Complex.continuous_im continuous_const)
  have hG_diff (z : ℂ) (hz : z ∈ U) (hi : z.im ≠ 0) : DifferentiableAt ℂ G z := by
    rcases hi.lt_or_gt with hneg | hpos
    · have hzc : conj z ∈ U ∧ 0 < (conj z).im :=
        ⟨hconj z hz, by simpa using hneg⟩
      have hd : DifferentiableAt ℂ (conj ∘ g ∘ conj) z :=
        differentiableAt_conj_conj_iff.mpr (hf_holo.differentiableAt (hopen.mem_nhds hzc))
      apply hd.congr_of_eventuallyEq
      filter_upwards [hopen'.mem_nhds ⟨hz, hneg⟩] with w hw
      exact hG_lower w ⟨hw.1, hw.2.le⟩
    · apply (hf_holo.differentiableAt (hopen.mem_nhds ⟨hz, hpos⟩)).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds ⟨hz, hpos⟩] with w hw
      exact hG_upper w ⟨hw.1, hw.2.le⟩
  refine ⟨?_, hF_cont, hF_upper, hF_conj⟩
  change DifferentiableOn ℂ G U
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hG_cont⟩
  let B (a b c d : ℝ) : ℂ :=
    (∫ x in a..b, G (x + c * I)) - (∫ x in a..b, G (x + d * I)) +
      I • (∫ y in c..d, G (b + y * I)) - I • (∫ y in c..d, G (a + y * I))
  have hhalf (a b c d : ℝ) (hcd : c ≤ d)
      (hsub : reProdIm (uIcc a b) (uIcc c d) ⊆ U) (hs : d ≤ 0 ∨ 0 ≤ c) :
      B a b c d = 0 := by
    have hc := hG_cont.mono hsub
    have hd : DifferentiableOn ℂ G
        (reProdIm (Ioo (min a b) (max a b)) (Ioo c d)) := by
      intro z hz
      apply (hG_diff z (hsub ⟨⟨hz.1.1.le, hz.1.2.le⟩,
        by simpa [uIcc_of_le hcd] using ⟨hz.2.1.le, hz.2.2.le⟩⟩) ?_).differentiableWithinAt
      rcases hs with hs | hs
      · exact (hz.2.2.trans_le hs).ne
      · exact (hs.trans_lt hz.2.1).ne'
    have hrect := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn G
      (a + c * I) (b + d * I) (by simpa using hc)
      (by convert hd using 1; simp [min_eq_left hcd, max_eq_right hcd])
    simpa [B, min_eq_left hcd, max_eq_right hcd] using hrect
  have hordered (a b c d : ℝ) (hcd : c ≤ d)
      (hsub : reProdIm (uIcc a b) (uIcc c d) ⊆ U) : B a b c d = 0 := by
    by_cases hd : d ≤ 0
    · exact hhalf a b c d hcd hsub (Or.inl hd)
    by_cases hc : 0 ≤ c
    · exact hhalf a b c d hcd hsub (Or.inr hc)
    have hc0 : c ≤ 0 := (lt_of_not_ge hc).le
    have h0d : 0 ≤ d := (lt_of_not_ge hd).le
    have hzero : (0 : ℝ) ∈ uIcc c d := by simp [uIcc_of_le hcd, hc0, h0d]
    have hsub₁ : reProdIm (uIcc a b) (uIcc c 0) ⊆ U :=
      fun z hz ↦ hsub ⟨hz.1, uIcc_subset_uIcc_left hzero hz.2⟩
    have hsub₂ : reProdIm (uIcc a b) (uIcc 0 d) ⊆ U :=
      fun z hz ↦ hsub ⟨hz.1, uIcc_subset_uIcc_right hzero hz.2⟩
    have h₁ := hhalf a b c 0 hc0 hsub₁ (Or.inl le_rfl)
    have h₂ := hhalf a b 0 d h0d hsub₂ (Or.inr le_rfl)
    have hint (x : ℝ) (hx : x ∈ uIcc a b) :
        IntervalIntegrable (fun y : ℝ ↦ G (x + y * I)) volume c d := by
      apply (hG_cont.comp (by fun_prop) ?_).intervalIntegrable
      intro y hy
      apply hsub
      simpa [mem_reProdIm] using And.intro hx hy
    have hsplit (x : ℝ) (hx : x ∈ uIcc a b) :
        (∫ y in c..0, G (x + y * I)) + (∫ y in 0..d, G (x + y * I)) =
          ∫ y in c..d, G (x + y * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hint x hx).mono_set (uIcc_subset_uIcc_left hzero))
        ((hint x hx).mono_set (uIcc_subset_uIcc_right hzero))
    have heq : B a b c d = B a b c 0 + B a b 0 d := by
      dsimp [B]
      rw [← hsplit a left_mem_uIcc, ← hsplit b right_mem_uIcc]
      simp only [mul_add]
      ring
    rw [heq, h₁, h₂, add_zero]
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  change B z.re w.re z.im w.im = 0
  have hzw' : reProdIm (uIcc z.re w.re) (uIcc z.im w.im) ⊆ U := by
    simpa only [Rectangle] using hzw
  by_cases h : z.im ≤ w.im
  · exact hordered z.re w.re z.im w.im h hzw'
  · have hs := hordered z.re w.re w.im z.im (le_of_not_ge h)
      (by simpa only [uIcc_comm w.im z.im, Rectangle] using hzw)
    have heq : B z.re w.re z.im w.im = - B z.re w.re w.im z.im := by
      dsimp [B]
      simp only [intervalIntegral.integral_symm w.im z.im]
      ring
    rw [heq, hs, neg_zero]

end

end HolomorphicAnosov

