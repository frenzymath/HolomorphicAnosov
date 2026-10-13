import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
/-- This is the coordinate frame on a full chart domain. (Andrews, §8.3) -/
theorem exists_coordinate_frame_of_source_eq_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    [IsManifold 𝓘(ℝ, E) ∞ N]
    (c : OpenPartialHomeomorph N E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ N)
    (hsource : c.source = univ) (v : E) :
    ∃ X : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : N → Type _),
      ∀ q, mvfderiv 𝓘(ℝ, E) c q (X q) = v := by
  let : IsManifold 𝓘(ℝ, E) 2 N := IsManifold.of_le (n := ∞) (by simp)
  let W := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c (fun _ ↦ v)
  have hcD : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have hq (q : N) : q ∈ c.source := by rw [hsource]; trivial
  have hcst (z : E) : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : E ↦ (⟨z, v⟩ : TangentBundle 𝓘(ℝ, E) E)) z :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ (⟨q, W q⟩ : TangentBundle 𝓘(ℝ, E) N)) := by
    intro q
    exact (hcst (c q)).mpullback_vectorField_preimage
      (contMDiffAt_of_mem_maximalAtlas hc (hq q)) ⟨hcD.mfderiv (hq q), rfl⟩ (by simp)
  refine ⟨⟨W, hW⟩, ?_⟩
  intro q
  exact (show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q).IsInvertible from
    ⟨hcD.mfderiv (hq q), rfl⟩).self_apply_inverse v

end
end HolomorphicAnosov
