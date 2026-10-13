import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Separation.Hausdorff

/-!
# Affine normalization at the marked corners of a rectangle

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5, Theorem 11.10, printed p.343 (PDF p.353), final continuity conclusion.
The endpoint argument below is agent-written detail for the conclusion omitted
in the parent rectangle-rigidity proof.
-/

namespace HolomorphicAnosov.Analysis

/-- An interior real affine formula and three fixed corner marks force positive scaling.

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0,
§11.5, Theorem 11.10, printed p.343; agent-written endpoint justification.

Proof: Since `a` and `b` are positive, the closure of the open source rectangle is
its closed rectangle, by `Complex.closure_reProdIm` and `closure_Ioo`. Extend the
ambient value of `e` from the closed rectangle by zero outside it. This extension
is continuous on the closed rectangle because `e` is continuous. On the open
rectangle it agrees with `z ↦ (c : ℂ) * z + d`; the latter is continuous everywhere.
`Set.EqOn.of_subset_closure` extends this equality to the closed rectangle.
Evaluation at zero gives `d = 0`. Evaluation at the right corner and taking real
parts gives `A = c * a`. Evaluation at the top-left corner and taking imaginary
parts gives `B = c * b`. Positivity of `a` and `A` forces `c > 0`, so cancellation
of this nonzero common factor gives `a / b = A / B`. Choose the scaling factor `c`.
No boundary derivative or continuity of `T` outside the interior is required.
-/
theorem rectangle_scaling_of_real_affine
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A)
    (T : ℂ → ℂ)
    (c : ℝ) (d : ℂ)
    (hformula : ∀ z ∈ Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b),
      T z = (c : ℂ) * z + d)
    (e : (Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)) ≃ₜ (Complex.reProdIm (Set.Icc 0 A) (Set.Icc 0 B)))
    (h_extension : ∀ z : (Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)),
      (z : ℂ) ∈ (Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)) → (e z : ℂ) = T z)
    (h_zero : (e ⟨0, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = 0)
    (h_right : (e ⟨(a : ℂ), by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ))
    (h_top_left : (e ⟨(b : ℂ) * Complex.I, by
      simp [Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) =
      (B : ℂ) * Complex.I) :
    ∃ c : ℝ, 0 < c ∧
      (∀ z ∈ (Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)), T z = (c : ℂ) * z) ∧
      A = c * a ∧ B = c * b ∧ a / b = A / B := by
  classical
  let U : Set ℂ := Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)
  let C : Set ℂ := Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)
  have hUC : U ⊆ C := fun z hz ↦ ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hclosure : closure U = C := by
    simp only [U, C, Complex.closure_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne]
  let F : ℂ → ℂ := fun z ↦ if hz : z ∈ C then (e ⟨z, hz⟩ : ℂ) else 0
  have hFc : ContinuousOn F C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hext : (fun z : C ↦ F z) = (fun z : C ↦ (e z : ℂ)) := by
      funext z
      simp [F, z.property]
    change Continuous (fun z : C ↦ F z)
    rw [hext]
    exact continuous_subtype_val.comp e.continuous
  have hFU : Set.EqOn F (fun z ↦ (c : ℂ) * z + d) U := by
    intro z hz
    simpa only [F, dite_eq_left (hUC hz), h_extension ⟨z, hUC hz⟩ hz] using hformula z hz
  have hFC : Set.EqOn F (fun z ↦ (c : ℂ) * z + d) C :=
    hFU.of_subset_closure hFc
      ((continuous_const.mul continuous_id).add continuous_const).continuousOn
      hUC (by rw [hclosure])
  have hz0 : (0 : ℂ) ∈ C := by simp [C, Complex.mem_reProdIm, ha.le, hb.le]
  have hza : (a : ℂ) ∈ C := by simp [C, Complex.mem_reProdIm, ha.le, hb.le]
  have hzb : (b : ℂ) * Complex.I ∈ C := by
    simp [C, Complex.mem_reProdIm, ha.le, hb.le]
  have hF0 : F 0 = 0 := by simpa only [F, dite_eq_left hz0] using h_zero
  have hFa : F a = A := by simpa only [F, dite_eq_left hza] using h_right
  have hFb : F ((b : ℂ) * Complex.I) = (B : ℂ) * Complex.I := by
    simpa only [F, dite_eq_left hzb] using h_top_left
  have hd : d = 0 := by simpa [hF0] using (hFC hz0).symm
  have hwidth : A = c * a := by
    simpa [hFa, hd] using congrArg Complex.re (hFC hza)
  have hheight : B = c * b := by
    simpa [hFb, hd] using congrArg Complex.im (hFC hzb)
  have hc : 0 < c := (mul_pos_iff_of_pos_right ha).mp (hwidth ▸ hA)
  refine ⟨c, hc, ?_, hwidth, hheight, ?_⟩
  · intro z hz
    simpa [hd] using hformula z hz
  · rw [hwidth, hheight]
    exact (mul_div_mul_left a b hc.ne').symm

end HolomorphicAnosov.Analysis
