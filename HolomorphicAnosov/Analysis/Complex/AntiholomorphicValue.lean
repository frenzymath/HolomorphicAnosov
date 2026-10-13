import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.HolomorphicComplexOneForm
import HolomorphicAnosov.Geometry.VectorDolbeaultDerivative
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Generic antiholomorphic value calculus

Public reusable algebraic and local pullback identities extracted from Zhang Lemma 4.3.
-/

namespace HolomorphicAnosov

noncomputable section
/-- The antiholomorphic part of an actual real derivative.
Source: Demailly I §3.C pp.22–24, Wirtinger convention; concrete real-linear evaluation. -/
def antiholomorphicValue {d e : ℕ}
    (D : ComplexModel d →L[ℝ] ComplexModel e) (v : ComplexModel d) : ComplexModel e :=
  (1 / 2 : ℂ) • (D v + Complex.I • D (Complex.I • v))


/-- The holomorphic coefficient derivative contributes zero to the antiholomorphic part.
Source: Zhang Lemma 4.3 p.15 (25); explicit real-coordinate scalar algebra. -/
theorem antiholomorphicValue_product {d e r : ℕ}
    (K : ComplexModel d →L[ℂ] (ComplexModel e →L[ℂ] ComplexModel r))
    (B : ComplexModel e →L[ℂ] ComplexModel r)
    (D : ComplexModel d →L[ℝ] ComplexModel e)
    (a : ComplexModel e) (v : ComplexModel d) :
    (1 / 2 : ℂ) • ((K v) a + B (D v) +
      Complex.I • ((K (Complex.I • v)) a + B (D (Complex.I • v)))) =
        B (antiholomorphicValue D v) := by
  ext j
  simp [antiholomorphicValue, map_smul, smul_smul, smul_add]
  ring


/-- A constant normalized pairing annihilates the antiholomorphic derivative.
Source: Zhang Lemma 4.3 p.15 after (25); explicit real-coordinate scalar algebra. -/
theorem antiholomorphicValue_normalized_pairing {d e : ℕ}
    (K : ComplexModel d →L[ℂ] (ComplexModel e →L[ℂ] ℂ))
    (θ : ComplexModel e →L[ℂ] ℂ)
    (D : ComplexModel d →L[ℝ] ComplexModel e) (a : ComplexModel e)
    (hconstant : ∀ v : ComplexModel d, (K v) a + θ (D v) = 0)
    (v : ComplexModel d) : θ (antiholomorphicValue D v) = 0 := by
  have hv := hconstant v
  have hi := hconstant (Complex.I • v)
  have hKi : (K (Complex.I • v)) a = Complex.I * (K v) a := by
    simp [map_smul, smul_eq_mul]
  have hzero : θ (D v) + Complex.I * θ (D (Complex.I • v)) = 0 := by
    rw [hKi] at hi
    have hmul := congrArg (fun z : ℂ ↦ Complex.I * z) hi
    simp only [mul_add, mul_zero, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hmul
    linear_combination hv + hmul
  simp only [antiholomorphicValue, map_smul, map_add, smul_eq_mul]
  rw [hzero, mul_zero]


/-- Decompose a complex scalar in a real-linear map into its real and imaginary parts.
Native algebra expansion used for Demailly I §3.C pp.22–24; Complex.re_add_im. -/
theorem realMap_complex_smul {d e : ℕ}
    (D : ComplexModel d →L[ℝ] ComplexModel e) (c : ℂ) (v : ComplexModel d) :
    D (c • v) = c.re • D v + c.im • D (Complex.I • v) := by
  have hv : c • v = c.re • v + c.im • (Complex.I • v) := by
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, ← add_mul, Complex.re_add_im]
  rw [hv, map_add, map_smul, map_smul]


/-- The antiholomorphic part is conjugate-linear in its input.
Source: Demailly I §3.C pp.22–24; expansion into real and imaginary scalar parts. -/
theorem antiholomorphicValue_smul {d e : ℕ}
    (D : ComplexModel d →L[ℝ] ComplexModel e) (c : ℂ) (v : ComplexModel d) :
    antiholomorphicValue D (c • v) = star c • antiholomorphicValue D v := by
  have hc : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  unfold antiholomorphicValue
  rw [smul_comm Complex.I c v]
  rw [realMap_complex_smul D c v, realMap_complex_smul D c (Complex.I • v)]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  ext j
  simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Complex.real_smul,
    smul_eq_mul]
  rw [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring


/-- Expand the conjugate-linear derivative in the finite coordinate basis.
Source: Demailly I §3.C pp.22–24; finite basis expansion and conjugate scalar action. -/
theorem antiholomorphicValue_basis {d e : ℕ}
    (D : ComplexModel d →L[ℝ] ComplexModel e) (v : ComplexModel d) :
    antiholomorphicValue D v =
      ∑ k : Fin d, star (v k) • antiholomorphicValue D (Pi.single k 1) := by
  have hsum (w : Fin d → ComplexModel d) :
      antiholomorphicValue D (∑ k, w k) = ∑ k, antiholomorphicValue D (w k) := by
    simp only [antiholomorphicValue, map_sum, Finset.smul_sum]
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
  conv_lhs => rw [pi_eq_sum_univ' v, hsum]
  exact Finset.sum_congr rfl (fun k _ ↦ antiholomorphicValue_smul D (v k) _)


/-- Differentiate a holomorphic coefficient acting on a smooth composed vector.
Source: Zhang Lemma 4.3 p.15 (25); native real chain and bilinear evaluation rules. -/
theorem antiholomorphicValue_fderiv_pullback {d e r t : ℕ}
    (C : ComplexModel d → (ComplexModel e →L[ℂ] ComplexModel r))
    (K : ComplexModel d →L[ℂ] (ComplexModel e →L[ℂ] ComplexModel r))
    (a : ComplexModel t → ComplexModel e) (D : ComplexModel t →L[ℝ] ComplexModel e)
    (φ : ComplexModel d → ComplexModel t) (J : ComplexModel d →L[ℂ] ComplexModel t)
    (z : ComplexModel d) (hC : HasFDerivAt C K z)
    (ha : HasFDerivAt a D (φ z)) (hφ : HasFDerivAt φ J z) (v : ComplexModel d) :
    antiholomorphicValue (fderiv ℝ (fun w ↦ C w (a (φ w))) z) v =
      C z (antiholomorphicValue D (J v)) := by
  let evaluation := (ContinuousLinearMap.apply (E := ComplexModel e) ℂ (ComplexModel r)).flip.bilinearRestrictScalars ℝ
  have hderiv := evaluation.hasFDerivAt_of_bilinear
    (hC.restrictScalars ℝ) (ha.comp z (hφ.restrictScalars ℝ))
  change HasFDerivAt (fun w ↦ C w (a (φ w))) _ z at hderiv
  rw [hderiv.fderiv]
  change (1 / 2 : ℂ) • ((C z) (D (J v)) + (K v) (a (φ z)) +
    Complex.I • ((C z) (D (J (Complex.I • v))) + (K (Complex.I • v)) (a (φ z)))) = _
  rw [map_smul J]
  have h := antiholomorphicValue_product K (C z) (D.comp (J.restrictScalars ℝ))
    (a (φ z)) v
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    antiholomorphicValue, map_smul J, add_comm] using h


/-- Differentiate an actually constant normalized functional pairing.
Source: Zhang Lemma 4.3 p.15 after (25); derivative uniqueness and bilinear evaluation. -/
theorem antiholomorphicValue_fderiv_normalized {d e : ℕ}
    (T : ComplexModel d → (ComplexModel e →L[ℂ] ℂ))
    (K : ComplexModel d →L[ℂ] (ComplexModel e →L[ℂ] ℂ))
    (a : ComplexModel d → ComplexModel e) (D : ComplexModel d →L[ℝ] ComplexModel e)
    (z : ComplexModel d) (hT : HasFDerivAt T K z) (ha : HasFDerivAt a D z)
    (hpair : (fun w ↦ T w (a w)) =ᶠ[nhds z] (fun _ ↦ (1 : ℂ)))
    (v : ComplexModel d) : T z (antiholomorphicValue D v) = 0 := by
  let evaluation := (ContinuousLinearMap.apply (E := ComplexModel e) ℂ ℂ).flip.bilinearRestrictScalars ℝ
  have hderiv := evaluation.hasFDerivAt_of_bilinear (hT.restrictScalars ℝ) ha
  change HasFDerivAt (fun w ↦ T w (a w)) _ z at hderiv
  have hzero := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℂ) z).congr_of_eventuallyEq hpair
  have heq := hderiv.unique hzero
  apply antiholomorphicValue_normalized_pairing K (T z) D (a z) _ v
  intro w
  have hw := congrArg (fun L ↦ L w) heq
  change (T z) (D w) + (K w) (a z) = 0 at hw
  simpa only [add_comm] using hw


/-- Constant complex output scalars factor out of the antiholomorphic derivative.
Source: Zhang Lemma 4.3 p.15 (25); explicit complex scalar algebra. -/
theorem antiholomorphicValue_output_smul {d e : ℕ}
    (D : ComplexModel d →L[ℝ] ComplexModel e) (ν : ℂ) (v : ComplexModel d) :
    antiholomorphicValue (ν • D) v = ν • antiholomorphicValue D v := by
  simp only [antiholomorphicValue, smul_apply, smul_add, smul_smul, mul_assoc, mul_comm]


end
end HolomorphicAnosov
