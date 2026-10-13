import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.BumpFunction

/-! Constant coordinate tangent vectors are realized locally by smooth vector fields. (Andrews,
Lecture 8, Prop. 8.3.1, p.74; Gallier–Quaintance, Props. 16.7–16.8, pp.451–454) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- At any chart-source point, a constant coordinate vector is the coordinate germ of a smooth
vector field on the whole manifold. (Andrews, Lecture 8, Prop. 8.3.1, p.74; Gallier–Quaintance,
Props. 16.7–16.8, pp.451–454) -/
theorem exists_coordinate_frame_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace E N]
    [IsManifold 𝓘(ℝ, E) ∞ N]
    (c : OpenPartialHomeomorph N E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ N)
    (p : N) (hp : p ∈ c.source) (v : E) :
    ∃ X : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : N → Type _),
      ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (X q) = v := by
  let : IsManifold 𝓘(ℝ, E) 2 N := IsManifold.of_le (n := ∞) (by simp)
  let W := VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c (fun _ ↦ v)
  have hcD : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have hcst (z : E) : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : E ↦ (⟨z, v⟩ : TangentBundle 𝓘(ℝ, E) E)) z :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have hW : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ (⟨q, W q⟩ : TangentBundle 𝓘(ℝ, E) N)) c.source := by
    intro q hq
    exact ((hcst (c q)).mpullback_vectorField_preimage
      (contMDiffAt_of_mem_maximalAtlas hc hq) ⟨hcD.mfderiv hq, rfl⟩
      (by simp)).contMDiffWithinAt
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := 𝓘(ℝ, E)) p).mem_iff.mp (c.open_source.mem_nhds hp)
  refine ⟨⟨fun q ↦ β q • W q, β.contMDiff.contMDiffOn.smul_section_of_tsupport
    c.open_source hβ hW⟩, ?_⟩
  filter_upwards [β.eventuallyEq_one, c.open_source.mem_nhds hp] with q hq hqc
  change mvfderiv 𝓘(ℝ, E) c q (β q • W q) = v
  simp only [hq, Pi.one_apply, one_smul]
  exact (show (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q).IsInvertible from
    ⟨hcD.mfderiv hqc, rfl⟩).self_apply_inverse v

end HolomorphicAnosov

