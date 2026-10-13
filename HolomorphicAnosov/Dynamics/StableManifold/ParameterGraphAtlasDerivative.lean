import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivatives of the actual parameter graph atlas expressions

Source: HPS, *Invariant Manifolds* (1977), pp.27–29,35,61–62; Mathlib's
Fréchet chain rule. The derivative is taken only in the fibre variable.
-/

noncomputable section
open Set
namespace HolomorphicAnosov

/-- The actual fibre derivative transforms by the genuine source and receiving
linear charts.

Source: HPS, *Invariant Manifolds*, pp.27–29 and 61–62, supplies the fibre derivative
and local bundle-chart setting. The displayed coordinate formula is its explicit
specialization of Mathlib's `HasFDerivAt.comp` and `ContinuousLinearMap.hasFDerivAt`.

First identify the partial-chart expression on its valid base
overlap, then apply the Fréchet chain rule to the two continuous linear equivalences
and the given original fibre derivative. No differentiability of the base is used. -/
theorem parameter_graph_atlas_derivative
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀ p, E p → F (b p)) (i : A) (j : B) (p : A)
    (hp : p ∈ (e.chart i).baseSet) (hbp : b p ∈ (f.chart j).baseSet)
    (x : FiniteFiberModel (e.rank i)) (D : E p →L[ℝ] F (b p))
    (hD : HasFDerivAt (g p) D ((e.coordinates i p hp).symm x)) :
    HasFDerivAt (fibreChartExpression e f b g i j p)
      ((f.coordinates j (b p) hbp).toContinuousLinearMap.comp
        (D.comp (e.coordinates i p hp).symm.toContinuousLinearMap)) x := by
  have heq : fibreChartExpression e f b g i j p =
      fun y ↦ f.coordinates j (b p) hbp (g p ((e.coordinates i p hp).symm y)) := by
    funext y
    have happly : (e.chart i)
        (⟨p, (e.coordinates i p hp).symm y⟩ : Sigma E) = (p, y) := by
      rw [e.chart_apply i p hp]
      simp
    have hinv : (e.chart i).toOpenPartialHomeomorph.symm (p, y) =
        (⟨p, (e.coordinates i p hp).symm y⟩ : Sigma E) := by
      rw [← happly]
      exact (e.chart i).toOpenPartialHomeomorph.left_inv
        ((e.chart i).mem_source.mpr (show p ∈ (e.chart i).baseSet from hp))
    unfold fibreChartExpression
    rw [hinv]
    exact congrArg Prod.snd (f.chart_apply j (b p) hbp _)
  rw [heq]
  exact (f.coordinates j (b p) hbp).toContinuousLinearMap.hasFDerivAt.comp x
    (hD.comp x (e.coordinates i p hp).symm.toContinuousLinearMap.hasFDerivAt)

end HolomorphicAnosov
