import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Geometry.UniformExponentialLift
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
# Native fibre chart expression transport

Guarded source/receiving-frame cancellation for the HPS fibre expression.
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

/-- The actual atlas expression is the tangent-frame expression precomposed with
the source coefficient and postcomposed with the inverse receiving coefficient.
The proof cancels the atlas partial inverse, then the two tangent-frame inverses.
This includes zero-rank models and imposes no fibre regularity. -/
theorem fibreChartExpression_eq_tangentExpression :
    let C := (((av.coordinates i p hi).symm.trans (L p)).trans
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).continuousLinearEquivAt ℝ p hs))
    let D := (((av.coordinates j (f p) hj).symm.trans (L (f p))).trans
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).continuousLinearEquivAt ℝ (f p) ht))
    fibreChartExpression av av f (fun q v ↦ (L (f q)).symm (G q (L q v))) i j p =
      fun x ↦ D.symm (ExponentialLift.fibreExpression univ f (fun q ↦ G q.1) s t
        ⟨p, mem_univ p⟩ (C x)) := by
  dsimp only
  funext x
  have hq : (av.chart i).toOpenPartialHomeomorph.symm (p, x) =
      (⟨p, (av.coordinates i p hi).symm x⟩ : Sigma V) := by
    have h := (av.chart i).toOpenPartialHomeomorph.left_inv
      ((av.chart i).mem_source.mpr hi :
        (⟨p, (av.coordinates i p hi).symm x⟩ : Sigma V) ∈ (av.chart i).source)
    change (av.chart i).toOpenPartialHomeomorph.symm
      ((av.chart i) ⟨p, (av.coordinates i p hi).symm x⟩) =
      (⟨p, (av.coordinates i p hi).symm x⟩ : Sigma V) at h
    rw [av.chart_apply i p hi, ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  let q := (av.chart i).toOpenPartialHomeomorph.symm (p, x)
  unfold fibreChartExpression
  change ((av.chart j) ⟨f q.1,
      (fun q v ↦ (L (f q)).symm (G q ((L q) v))) q.1 q.2⟩).2 = _
  dsimp [q]
  rw [hq, av.chart_apply j (f p) hj]
  unfold ExponentialLift.fibreExpression
  have hsource :=
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL_continuousLinearMapAt
      (R := ℝ) hs (L p ((av.coordinates i p hi).symm x))
  have hreceiving :=
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).symmL_continuousLinearMapAt
      (R := ℝ) ht (G p (L p ((av.coordinates i p hi).symm x)))
  have hsource' :
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ p
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).continuousLinearEquivAt
          ℝ p hs (L p ((av.coordinates i p hi).symm x))) =
      L p ((av.coordinates i p hi).symm x) := by
    rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq _ hs]
    exact hsource
  have hreceiving' :
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).continuousLinearEquivAt
          ℝ (f p) ht).symm
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).continuousLinearMapAt
          ℝ (f p) (G p (L p ((av.coordinates i p hi).symm x)))) =
      G p (L p ((av.coordinates i p hi).symm x)) := by
    rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq _ ht]
    exact hreceiving
  rw [hsource', hreceiving']


end HolomorphicAnosov.HPS.NativeFibreChartJetTransport

