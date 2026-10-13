import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

namespace HolomorphicAnosov

/-- A real differentiable map is complex differentiable at a point if its derivative
has complex-invariant range and a complex-linear left inverse.

Source: Demailly, Complex Analytic and Differential Geometry, Chapter I,
Lemma 7.15, printed p.60, tangent-plane projection argument. In projected graph
coordinates the projection is a complex-linear left inverse of the real
derivative. For each complex scalar a and vector v, range invariance gives z
with D z = a D v. Applying the left inverse forces z = a v, hence D is
complex-linear. Its existing continuity gives a continuous complex-linear
map with the same underlying real derivative. Restriction-of-scalars calculus
then supplies the complex derivative. No finite-dimensionality or nonzero-rank
hypothesis is needed. -/
theorem complex_differentiableAt_of_complex_range
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (P : F →L[ℂ] E)
    (hP : Function.LeftInverse P (fderiv ℝ f x))
    (hS : ∀ (a : ℂ) v, a • fderiv ℝ f x v ∈ (fderiv ℝ f x).range) :
    DifferentiableAt ℂ f x := by
  let D := fderiv ℝ f x
  have hscalar (a : ℂ) (v : E) : D (a • v) = a • D v := by
    obtain ⟨z, hz⟩ := hS a v
    have hz' : D z = a • D v := hz
    have hzval : z = a • v := by
      have hh := congrArg P hz'
      simpa only [D, map_smul, hP z, hP v] using hh
    simpa only [hzval] using hz'
  let Dc : E →L[ℂ] F :=
    { toLinearMap :=
        { toFun := D
          map_add' := D.map_add
          map_smul' := hscalar }
      cont := D.continuous }
  exact (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt
    (show Dc.restrictScalars ℝ = fderiv ℝ f x by rfl)).differentiableAt

end HolomorphicAnosov

