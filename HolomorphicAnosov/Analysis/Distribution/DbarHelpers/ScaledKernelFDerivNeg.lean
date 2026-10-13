import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivative sign of a scaled smoothing kernel

Source: Semyon Dyatlov, 18.155 distributions notes (2026), §6.1.1, Theorem6.4, proof p.69, final
translated-kernel derivative-sign calculation (6.10), applied to the smooth scaled kernel from
§1.3.2 (1.31).
DAG node: `analysis.dbar_helper_scaled_kernel_fderiv_neg_g6`.
-/

open Set TopologicalSpace
open scoped ContDiff

namespace HolomorphicAnosov.Analysis.Distribution

/--
For a real smooth compactly supported test on real m-dimensional Euclidean space and every real
scale, the derivative of its scaled complex-valued translated kernel with respect to its center
equals the negative derivative with respect to the spatial variable in each real direction.

Source: Dyatlov, 18.155 notes, §6.1.1, Theorem6.4, proof p.69, final translated-kernel
derivative-sign calculation (6.10), applied to the smooth scaled kernel from §1.3.2 (1.31).

Proof: The scaled test kernel is smooth by composition with scalar multiplication, complex
coercion, and multiplication by its normalization constant. Write it as g(x-y). The derivative in
the center variable is the derivative of g at x-y composed with the identity. The derivative in
the spatial variable is that same derivative composed with negative identity. Evaluating on the
chosen direction and using linearity gives opposite signs, as in Dyatlov’s displayed calculation
for first derivatives. This calculation does not require positivity of the scale or normalized
integral; at scale zero the Lean inverse convention still yields a smooth constant kernel.
-/
theorem scaled_kernel_fderiv_neg {m : ℕ}
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (ε : ℝ) (x y v : EuclideanSpace ℝ (Fin m)) :
    (fderiv ℝ (fun p ↦ (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (p-y)) : ℝ) : ℂ)) x) v =
      -(fderiv ℝ (fun q ↦ (((ε⁻¹)^m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (x-q)) : ℝ) : ℂ)) y) v := by
  let g : EuclideanSpace ℝ (Fin m) → ℂ :=
    fun z ↦ (((ε⁻¹)^m : ℝ) : ℂ) * ((ρ (ε⁻¹ • z) : ℝ) : ℂ)
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (ρ.contDiff.comp (contDiff_id.const_smul ε⁻¹)))
  have hd := hg.differentiable (by simp)
  have hx := (hd (x-y)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)
  have hy := (hd (x-y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  have hdx := hx.fderiv
  have hdy := hy.fderiv
  simp only [Function.comp_def, id_eq] at hdx hdy
  change (fderiv ℝ (fun p ↦ g (p-y)) x) v =
    -(fderiv ℝ (fun q ↦ g (x-q)) y) v
  rw [hdx, hdy]
  simp


end HolomorphicAnosov.Analysis.Distribution
