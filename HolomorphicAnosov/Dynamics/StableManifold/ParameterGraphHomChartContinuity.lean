import Mathlib.Topology.VectorBundle.Hom

/-!
# Continuity in native Hom-bundle coordinates

Source: pinned Mathlib `Topology/VectorBundle/Hom.lean`, `continuousAt_hom_bundle`,
lines 296–302. This specializes the criterion to linear maps over one scalar field
for the Hom-section construction in HPS, *Invariant Manifolds*, p.35 and pp.61–62.
The canonical total-space topology and native bundle charts are retained.
-/

noncomputable section
namespace HolomorphicAnosov
open Bundle Set ContinuousLinearMap Topology _root_.Topology
open scoped Bundle

/-- Pointwise form of the genuine Hom-bundle chart criterion used by HPS
p.35 and pp.61–62. For a map into the original total space of continuous
linear maps, continuity of its base projection and of its operator component
in the Hom trivialization centered at the tested point imply continuity in
the original Hom total-space topology. No replacement topology or global
trivialization is introduced. -/
theorem parameter_graph_hom_chart_continuity
    {𝕜 F₁ F₂ B M : Type*}
    {E₁ : B → Type*} {E₂ : B → Type*}
    [NontriviallyNormedField 𝕜]
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)]
    [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)]
    [∀ x, ContinuousSMul 𝕜 (E₂ x)]
    [TopologicalSpace B]
    [∀ x, TopologicalSpace (E₁ x →L[𝕜] E₂ x)]
    [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [∀ x, AddCommGroup (E₁ x →L[𝕜] E₂ x)]
    [∀ x, Module 𝕜 (E₁ x →L[𝕜] E₂ x)]
    [TopologicalSpace M]
    (f : M → TotalSpace (F₁ →SL[RingHom.id 𝕜] F₂)
      (fun x ↦ E₁ x →L[𝕜] E₂ x)) (x₀ : M)
    (hbase : ContinuousAt (fun x ↦ (f x).1) x₀)
    (hcoord : ContinuousAt
      (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀) :
    ContinuousAt f x₀ := by
  exact (continuousAt_hom_bundle (RingHom.id 𝕜) f).2 ⟨hbase, hcoord⟩

end HolomorphicAnosov
