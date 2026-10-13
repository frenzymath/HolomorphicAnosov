import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic

/-!
# Smoothness of the components of a smooth vector field


-/ 

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- The coefficients of a smooth field in a smooth coordinate chart are smooth on the chart source. Source: Lee (2003), Lemma 4.2, pp.83–84. -/
theorem LocalSmoothVectorField.contMDiffOn_tangentCoefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {U : Opens M} {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (X : LocalSmoothVectorField E M U) (k : Fin n) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p ↦ X.tangentCoefficient b c p k)
      c.source := by
  have ht := (contMDiffOn_of_mem_maximalAtlas hc).contMDiffOn_tangentMapWithin
    (m := ∞) (by simp) c.open_source.uniqueMDiffOn
  have hs := ht.comp X.contMDiff.contMDiffOn (fun p hp ↦ hp)
  have hv := (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp_contMDiffOn hs
  have hk := (b.coord k).toContinuousLinearMap.contMDiff.comp_contMDiffOn hv
  apply hk.congr
  intro p hp
  change b.repr (mvfderiv 𝓘(ℝ, E) c p (X p)) k =
    b.repr (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) c c.source p (X p)) k
  rw [mfderivWithin_eq_mfderiv (c.open_source.uniqueMDiffWithinAt hp)
    ((contMDiffAt_of_mem_maximalAtlas hc hp).mdifferentiableAt (by simp))]
  rfl

end
end HolomorphicAnosov

