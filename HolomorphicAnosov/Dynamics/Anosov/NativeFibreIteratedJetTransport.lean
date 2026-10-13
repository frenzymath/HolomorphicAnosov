import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.Anosov.NativeFibreChartExpressionTransport
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Fibre chart cancellation and vertical jets

Agent-written coordinate calculation supporting HPS (1977), first proof of (5.5),
printed pp.61–62. It relates the graph supplier's finite-rank atlas expression to
the exponential supplier's tangent-frame expression. Both source and receiving
frame memberships are explicit. The receiving coefficient is inverted at `f p`.
No derivative of a parameter or invariant splitting is used.
-/

noncomputable section
open Set
open scoped Manifold ContDiff Topology _root_.Topology Bundle

/-!
# Native fibre iterated-jet transport

Fixed-frame iterated fibre derivatives for the HPS expression.
-/

namespace HolomorphicAnosov.HPS.NativeFibreChartJetTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {V : M → Type*} [∀ p, NormedAddCommGroup (V p)] [∀ p, NormedSpace ℝ (V p)]
  [TopologicalSpace (Sigma V)]
  (av : FiniteRankNormedAtlas (E := V)) (f : M → M)
  (L : ∀ p, V p ≃L[ℝ] TangentSpace 𝓘(ℝ, E) p)
  (G : ∀ p, TangentSpace 𝓘(ℝ, E) p → TangentSpace 𝓘(ℝ, E) (f p))
  (i j s t p : M)
  (hi : p ∈ (av.chart i).baseSet) (hj : f p ∈ (av.chart j).baseSet)
  (hs : p ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).baseSet)
  (ht : f p ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).baseSet)

/-- Finite vertical derivatives of that same atlas expression: the source
coefficient occupies every multilinear argument, and the receiving inverse acts
on the result. Includes order zero. Smoothness is only of the stated tangent-frame
expression on its whole fibre; no parameter smoothness is introduced. -/
theorem iteratedFDeriv_fibreChartExpression (r m : ℕ) (hm : m ≤ r)
    (hg : ContDiff ℝ r
      (ExponentialLift.fibreExpression univ f (fun q ↦ G q.1) s t ⟨p, mem_univ p⟩))
    (x : FiniteFiberModel (av.rank i)) :
    let C := (((av.coordinates i p hi).symm.trans (L p)).trans
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).continuousLinearEquivAt ℝ p hs))
    let D := (((av.coordinates j (f p) hj).symm.trans (L (f p))).trans
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).continuousLinearEquivAt ℝ (f p) ht))
    iteratedFDeriv ℝ m
      (fibreChartExpression av av f (fun q v ↦ (L (f q)).symm (G q (L q v))) i j p) x =
      D.symm.toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m
          (ExponentialLift.fibreExpression univ f (fun q ↦ G q.1) s t
            ⟨p, mem_univ p⟩) (C x)).compContinuousLinearMap
              (fun _ ↦ C.toContinuousLinearMap)) := by
  dsimp only
  rw [fibreChartExpression_eq_tangentExpression av f L G i j s t p hi hj hs ht]
  let C := (((av.coordinates i p hi).symm.trans (L p)).trans
    ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).continuousLinearEquivAt ℝ p hs))
  let D := (((av.coordinates j (f p) hj).symm.trans (L (f p))).trans
    ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).continuousLinearEquivAt ℝ (f p) ht))
  let g := ExponentialLift.fibreExpression univ f (fun q ↦ G q.1) s t ⟨p, mem_univ p⟩
  change iteratedFDeriv ℝ m (D.symm.toContinuousLinearMap ∘
    (g ∘ C.toContinuousLinearMap)) x =
      D.symm.toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m g (C x)).compContinuousLinearMap
          (fun _ ↦ C.toContinuousLinearMap))
  calc
    iteratedFDeriv ℝ m (D.symm.toContinuousLinearMap ∘
        (g ∘ C.toContinuousLinearMap)) x =
      D.symm.toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (g ∘ C.toContinuousLinearMap) x) := by
          exact D.symm.toContinuousLinearMap.iteratedFDeriv_comp_left
            ((hg.comp C.contDiff).contDiffAt) (by exact_mod_cast hm)
    _ = D.symm.toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m g (C x)).compContinuousLinearMap
          (fun _ ↦ C.toContinuousLinearMap)) := by
          rw [C.toContinuousLinearMap.iteratedFDeriv_comp_right hg x
            (by exact_mod_cast hm)]
          rfl


end HolomorphicAnosov.HPS.NativeFibreChartJetTransport

