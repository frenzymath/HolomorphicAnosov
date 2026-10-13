import HolomorphicAnosov.Dynamics.Anosov.FiniteOrderNativePlaqueCoherence
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Filter
open scoped _root_.Topology Manifold ContDiff
noncomputable section
universe u
namespace HolomorphicAnosov

/-- Joint continuity of the second spatial jet on an open domain implies joint continuity of the
derivative of the first derivative. -/
theorem continuous_spatial_second_derivative_of_jet_g18
    {P V E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : P → V → E) (B : Set V) (hB : IsOpen B)
    (hjet : Continuous (fun z : P × B ↦ iteratedFDerivWithin ℝ 2 (q z.1) B z.2.1)) :
    Continuous (fun z : P × B ↦ fderiv ℝ (fderiv ℝ (q z.1)) z.2.1) := by
  let C := (continuousMultilinearCurryFin1 ℝ V (V →L[ℝ] E)).toContinuousLinearEquiv
  let R := (continuousMultilinearCurryRightEquiv' ℝ 1 V E).toContinuousLinearEquiv
  have hc := C.continuous.comp (R.continuous.comp hjet)
  apply hc.congr
  intro z
  have he := iteratedFDerivWithin_succ_eq_comp_right (𝕜 := ℝ)
    (f := q z.1) (n := 1) hB.uniqueDiffOn z.2.property
  change iteratedFDerivWithin ℝ 2 (q z.1) B z.2.1 = R.symm
    (iteratedFDerivWithin ℝ 1 (fderivWithin ℝ (q z.1) B) B z.2.1) at he
  change C (R (iteratedFDerivWithin ℝ 2 (q z.1) B z.2.1)) = _
  rw [he, R.apply_symm_apply]
  have hnear : fderivWithin ℝ (q z.1) B =ᶠ[𝓝 z.2.1] fderiv ℝ (q z.1) := by
    filter_upwards [hB.mem_nhds z.2.property] with v hv
    exact fderivWithin_of_isOpen hB hv
  apply ContinuousLinearMap.ext
  intro v
  change iteratedFDerivWithin ℝ 1 (fderivWithin ℝ (q z.1) B) B z.2.1 (fun _ ↦ v) = _
  rw [iteratedFDerivWithin_one_apply (hB.uniqueDiffOn _ z.2.property),
    fderivWithin_of_isOpen hB z.2.property, hnear.fderiv_eq]

/-- Finite-order native plaque coherence of order at least two gives a jointly continuous second
coordinate derivative. -/
theorem HPS.FiniteOrderNativePlaqueCoherence.continuous_second_derivative_g18
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    {D : RealTangentDistribution 𝓘(ℝ,E) M}
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    {F : HPS.LeafPartition D ι L r} {x : M} {d : ℕ}
    {Φ : HPS.FiniteC1NativePlaqueFamily F x d} {N : ℕ}
    (H : HPS.FiniteOrderNativePlaqueCoherence Φ N) (hN : 2 ≤ N) :
    Continuous (fun z : Φ.family.centerDomain × Metric.ball (0 : Fin d → ℝ) Φ.family.radius ↦
      fderiv ℝ (fderiv ℝ (H.coordinate z.1)) z.2.1) :=
  continuous_spatial_second_derivative_of_jet_g18 H.coordinate _ Metric.isOpen_ball
    (H.jointly_continuous_derivatives 2 hN)

end HolomorphicAnosov
