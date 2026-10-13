import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

open Bundle Filter Set
open scoped Topology Manifold ContDiff
noncomputable section

namespace HolomorphicAnosov

/-- Every fibrewise nonempty open convex constraint in a smooth vector bundle admits a smooth section. The section is obtained by local choices and a partition of unity (Wockel, Thm. 11). -/
theorem exists_smooth_section_mem_open_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, Module ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
    (O : Set (TotalSpace F V)) (hO : IsOpen O)
    (hconv : ∀ x, Convex ℝ {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ O})
    (hne : ∀ x, ∃ v : V x, (⟨x, v⟩ : TotalSpace F V) ∈ O) :
    ∃ s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯,
      ∀ x, (⟨x, s x⟩ : TotalSpace F V) ∈ O := by
  apply exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, E) V
    (fun x ↦ {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ O}) hconv
  intro x
  obtain ⟨v, hv⟩ := hne x
  let s : ∀ y, V y := FiberBundle.extend F v
  obtain ⟨U, hU, hs⟩ := FiberBundle.exists_contMDiffOn_extend 𝓘(ℝ, E) F (k := ∞) v
  have hcont : ContinuousAt (fun y ↦ (⟨y, s y⟩ : TotalSpace F V)) x :=
    (FiberBundle.contMDiffAt_extend 𝓘(ℝ, E) F (k := ∞) v).continuousAt
  have hx : (⟨x, s x⟩ : TotalSpace F V) ∈ O := by
    simpa [s, FiberBundle.extend_apply_self] using hv
  have hpre : (fun y ↦ (⟨y, s y⟩ : TotalSpace F V)) ⁻¹' O ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (hO.mem_nhds hx)
  refine ⟨U ∩ (fun y ↦ (⟨y, s y⟩ : TotalSpace F V)) ⁻¹' O,
    inter_mem hU hpre, s, hs.mono inter_subset_left, ?_⟩
  exact fun y hy ↦ hy.2

end HolomorphicAnosov
