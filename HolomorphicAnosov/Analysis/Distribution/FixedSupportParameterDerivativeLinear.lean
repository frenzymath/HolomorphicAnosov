import HolomorphicAnosov.Analysis.Distribution.FixedSupportParameterDerivativeTests
import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# Continuous linear derivative tests

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3,
pp. 68–69, equations (6.8)–(6.9).

DAG node: `analysis.distribution_fixed_support_parameter_derivative_linear_g10`.
-/

noncomputable section
open Set
open scoped ContDiff
namespace HolomorphicAnosov.Analysis

/-- At a fixed parameter, directional derivatives form a continuous real-linear map into
smooth test functions, with all supports contained in the same compact set.

Construct each directional test by the parameter derivative test theorem. Pointwise
uniqueness and linearity of the Fréchet derivative prove additivity and real homogeneity.
A linear map from the finite-dimensional parameter space into the locally convex test
function space is continuous. This also applies in dimension zero and for empty K. -/
theorem fixed_support_parameter_derivative_linear
    {m k : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (p : EuclideanSpace ℝ (Fin k)) (hp : p ∈ P) :
    ∃ J : EuclideanSpace ℝ (Fin k) →L[ℝ] TestFunction U ℂ ⊤,
      (∀ v y, J v y = (fderivWithin ℝ (fun q ↦ H q y) (P : Set _) p) v) ∧
      ∀ v, tsupport (J v : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K := by
  have hex (v : EuclideanSpace ℝ (Fin k)) :=
    fixed_support_parameter_derivative_test U P K hK hKU H hH hSupport 1 (fun _ ↦ v) p hp
  choose J hJ hsupp using hex
  have hval (v : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin m)) :
      J v y = (fderivWithin ℝ (fun q ↦ H q y) (P : Set _) p) v := by
    rw [hJ]
    exact iteratedFDerivWithin_one_apply (P.isOpen.uniqueDiffWithinAt (𝕜 := ℝ) hp) _
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] TestFunction U ℂ ⊤ :=
    { toFun := J
      map_add' := by
        intro v w
        ext y
        change J (v + w) y = J v y + J w y
        simp only [hval, map_add]
      map_smul' := by
        intro a v
        ext y
        change J (a • v) y = a • J v y
        simp only [hval, map_smul] }
  exact ⟨L.toContinuousLinearMap, hval, hsupp⟩
end HolomorphicAnosov.Analysis
