import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
Reusable FixedFibreSmooth declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Inclusion of a fixed tangent fibre is smooth for the actual tangent-bundle atlas. -/
lemma tangentBundle_fixed_fibre_contMDiff (p : M) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun v : E ↦ (⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩ :
        TangentBundle 𝓘(ℝ, E) M)) := by
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_const, ?_⟩
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) p
  let L : E →L[ℝ] E := (e.continuousLinearMapAt ℝ p).comp
    (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ L :=
    L.contDiff.contMDiff
  convert hL.contMDiffAt using 1
  ext w
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) p) _).symm

end
end HolomorphicAnosov
