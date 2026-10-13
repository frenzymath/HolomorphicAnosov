import HolomorphicAnosov.Analysis.MarkedRectangleHorizontalPreservation
import HolomorphicAnosov.Analysis.Complex.HorizontalDerivativeReal
import HolomorphicAnosov.Analysis.Complex.RealDerivativeAffine
import HolomorphicAnosov.Analysis.MarkedRectangleAffineBoundary
import Mathlib.Analysis.Complex.Convex

/-!
# Rigidity of a marked holomorphic rectangle bijection

Source: Farb–Margalit, *A Primer on Mapping Class Groups*, author Version 5.0 (2011),
§11.5 Theorem 11.10 and its written proof, printed pp.341–343 (PDF pp.351–353),
using only the K=1 length–area and horizontal/vertical equality argument.
The exact boundary-extension, inverse and integral prerequisites are recorded in
DAG node `analysis.marked_rectangle_g3_rectangle_rigidity`.

An ambient function represents the interior map: its values outside the open source
rectangle are unrestricted. Holomorphicity is `DifferentiableOn ℂ`; the boundary
extension is a genuine homeomorphism of the closed-rectangle subtypes, with agreement
on the interior and the four corners marked individually. No boundary derivative is
assumed. The proof reduces to horizontal preservation, real-affine rigidity, and boundary normalization.
The imported analytic horizontal-preservation and affine helper obligations remain explicit.
-/

namespace HolomorphicAnosov.Analysis.MarkedRectangleG3RectangleRigidity

/-- The open rectangle (0,a) × (0,b) in the complex plane.
Source: the rectangle R_(a,b) in the DAG statement and Farb–Margalit §11.5. -/
abbrev openRectangle (a b : ℝ) : Set ℂ :=
  Complex.reProdIm (Set.Ioo 0 a) (Set.Ioo 0 b)

/-- The closed rectangle [0,a] × [0,b] in the complex plane.
Source: the closed rectangles in the DAG statement and Farb–Margalit §11.5. -/
abbrev closedRectangle (a b : ℝ) : Set ℂ :=
  Complex.reProdIm (Set.Icc 0 a) (Set.Icc 0 b)

/-- A holomorphic bijection between positive rectangles, extending homeomorphically
with the ordered corners 0,a,a+ib,ib mapped to 0,A,A+iB,iB, is multiplication by
one positive real scalar. In particular their width/height ratios agree.

Source: Farb–Margalit Version 5.0, §11.5 Theorem 11.10, printed pp.341–343,
restricted to K=1. The named horizontal-preservation theorem contains the source
length–area and equality argument. Horizontal preservation forces the derivative
to be real. The open rectangle is convex and nonempty, hence connected; the
real-derivative affine theorem gives T(z)=cz+d there. Continuity of the boundary
homeomorphism extends this formula to the corners, and the marks at zero, a and
ib force d=0, A=ca, B=cb and c>0. Cancellation gives the ratio equality.

The parent contains no local admission, but the horizontal-preservation,
real-derivative affine and marked-boundary helper proofs remain obligations.
-/
theorem rectangle_rigidity
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (T : ℂ → ℂ)
    (h_holomorphic : DifferentiableOn ℂ T (openRectangle a b))
    (h_bijective : Set.BijOn T (openRectangle a b) (openRectangle A B))
    (e : closedRectangle a b ≃ₜ closedRectangle A B)
    (h_extension : ∀ z : closedRectangle a b,
      (z : ℂ) ∈ openRectangle a b → (e z : ℂ) = T z)
    (h_zero : (e ⟨0, by
      simp [closedRectangle, Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = 0)
    (h_right : (e ⟨(a : ℂ), by
      simp [closedRectangle, Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) = (A : ℂ))
    (h_top_right : (e ⟨(a : ℂ) + (b : ℂ) * Complex.I, by
      simp [closedRectangle, Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) =
      (A : ℂ) + (B : ℂ) * Complex.I)
    (h_top_left : (e ⟨(b : ℂ) * Complex.I, by
      simp [closedRectangle, Complex.mem_reProdIm, ha.le, hb.le]⟩ : ℂ) =
      (B : ℂ) * Complex.I) :
    ∃ c : ℝ, 0 < c ∧
      (∀ z ∈ openRectangle a b, T z = (c : ℂ) * z) ∧
      A = c * a ∧ B = c * b ∧ a / b = A / B := by
  have hopen : IsOpen (openRectangle a b) := isOpen_Ioo.reProdIm isOpen_Ioo
  have hconv : Convex ℝ (openRectangle a b) :=
    ((convex_Ioo (0 : ℝ) a).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioo (0 : ℝ) b).linear_preimage Complex.imCLM.toLinearMap)
  have hconn : IsConnected (openRectangle a b) := by
    apply hconv.isConnected
    refine ⟨(a / 2 : ℝ) + (b / 2 : ℝ) * Complex.I, ?_⟩
    simp only [openRectangle, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add, Set.mem_Ioo]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hline := MarkedRectangleHorizontalPreservation.horizontal_preservation
    ha hb hA hB T h_holomorphic h_bijective e h_extension h_zero h_right
      h_top_right h_top_left
  have hreal := Analysis.Complex.deriv_im_eq_zero_of_horizontal_preservation
    hopen h_holomorphic hline
  obtain ⟨c, d, hformula⟩ := Analysis.Complex.real_affine_of_deriv_im_eq_zero
    hopen hconn h_holomorphic hreal
  exact rectangle_scaling_of_real_affine ha hb hA T c d hformula e h_extension
    h_zero h_right h_top_left

end HolomorphicAnosov.Analysis.MarkedRectangleG3RectangleRigidity

