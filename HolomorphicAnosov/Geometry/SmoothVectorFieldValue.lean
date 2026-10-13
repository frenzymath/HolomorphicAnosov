import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- Every tangent vector is the value at its point of a smooth vector field. -/
theorem exists_smooth_vectorField_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (p : M) (v : TangentSpace 𝓘(ℝ, E) p) :
    ∃ Z : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : M → Type _),
      Z p = v := by
  let t := trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) p
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
    (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E _ p))
  have he : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ (⟨q, FiberBundle.extend E v q⟩ : TangentBundle 𝓘(ℝ, E) M)) t.baseSet := by
    intro q hq
    rw [t.contMDiffWithinAt_section _ hq]
    apply (contMDiffWithinAt_const (c := (t ⟨p, v⟩).2)).congr
    · intro r hr
      simp only [FiberBundle.extend]
      have ht := t.apply_mk_symm hr (t ⟨p, v⟩).2
      have ht' := congrArg Prod.snd ht
      exact ht'
    · simp only [FiberBundle.extend]
      have ht := t.apply_mk_symm hq (t ⟨p, v⟩).2
      have ht' := congrArg Prod.snd ht
      exact ht'
  have hZ := β.contMDiff.contMDiffOn.smul_section_of_tsupport
    t.open_baseSet hβ he
  refine ⟨⟨fun q ↦ β q • FiberBundle.extend E v q, hZ⟩, ?_⟩
  simp


end
end HolomorphicAnosov
