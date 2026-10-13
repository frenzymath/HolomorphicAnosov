import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Basic

/-!
# A vector bundle from linear trivializations in an existing topology

The finite-dimensional model makes continuity of the operator-valued transition
maps follow from the continuity of the given trivializations. This construction
keeps the given topology on the total space and includes every supplied chart in
its atlas. It supplies the bundle-instance step needed for the continuous unstable
line in Ghys, *Holomorphic Anosov systems*, Lemma 3.3, printed p.592.

DAG node: `geometry.vector_bundle_of_linear_trivializations_g16`.
-/

namespace HolomorphicAnosov.Topology

open Bundle Set _root_.Topology

universe u v w k l

/-- Covering linear trivializations with a finite-dimensional model over a complete
nontrivially normed field define a vector bundle in the given total-space topology, provided each fibre inclusion induces
its given fibre topology. The resulting atlas is exactly the supplied family.

Source: agent-written expansion of the bundle-instance step omitted in
Ghys, *Holomorphic Anosov systems*, Lemma 3.3, printed p.592; parent
`ghys.invariant_jet_section`. Mathlib's `FiberBundle` and `VectorBundle` are the
interfaces being constructed, using its `continuousOn_clm_apply` criterion.

Proof: choose a chart containing each base point and use the whole supplied
family as the fibre-bundle atlas. The fibre-topology assumption is precisely the
remaining fibre-bundle field. All its charts are linear by hypothesis. For two
charts and any fixed model vector v, their coordinate change evaluated at v is
the second coordinate of the first chart's inverse followed by the second
chart. This is continuous on the intersection of their base sets. The first
inverse preserves the base there, so both compositions remain in their chart
domains. Since the model is finite dimensional, continuity of all evaluations
implies operator-norm continuity of the transition maps. These are exactly the
vector-bundle fields. Empty base and zero-dimensional model are allowed; no
compactness, trivialization of the whole bundle, or norm continuity is asserted. -/
theorem exists_vectorBundle_of_linear_trivializations
    {𝕜 : Type k} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {B : Type u} [TopologicalSpace B]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type w} [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [TopologicalSpace (TotalSpace F E)]
    {ι : Type l} (e : ι → Trivialization F (π F E))
    (hcover : ∀ b, ∃ i, b ∈ (e i).baseSet)
    (hlinear : ∀ i, (e i).IsLinear 𝕜)
    (hind : ∀ b, IsInducing (@TotalSpace.mk B F E b)) :
    ∃ fb : FiberBundle F E,
      fb.trivializationAtlas' = range e ∧
      letI := fb
      VectorBundle 𝕜 F E := by
  classical
  let fb : FiberBundle F E := {
    totalSpaceMk_isInducing' := hind
    trivializationAtlas' := range e
    trivializationAt' := fun b ↦ e (hcover b).choose
    mem_baseSet_trivializationAt' := fun b ↦ (hcover b).choose_spec
    trivialization_mem_atlas' := fun b ↦ ⟨(hcover b).choose, rfl⟩ }
  let := fb
  refine ⟨fb, rfl, ?_⟩
  have hlin : ∀ t : Trivialization F (π F E), t ∈ range e → t.IsLinear 𝕜 := by
    rintro t ⟨i, rfl⟩
    exact hlinear i
  exact {
    trivialization_linear' := by
      intro t ht
      exact hlin t ht.out
    continuousOn_coordChange' := by
      intro t t' ht ht'
      have : t.IsLinear 𝕜 := hlin t ht.out
      have : t'.IsLinear 𝕜 := hlin t' ht'.out
      apply continuousOn_clm_apply.mpr
      intro v
      have h := t.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (show MapsTo (fun b : B ↦ (b, v)) (t.baseSet ∩ t'.baseSet)
          t.toOpenPartialHomeomorph.target from fun b hb ↦ t.mem_target.mpr hb.1)
      have h' := t'.continuousOn.comp h (by
        intro b hb
        apply t'.mem_source.mpr
        change (t.toOpenPartialHomeomorph.symm (b, v)).proj ∈ t'.baseSet
        rw [t.proj_symm_apply' hb.1]
        exact hb.2)
      refine h'.snd.congr ?_
      intro b hb
      exact t.coordChangeL_apply' t' hb v }


end HolomorphicAnosov.Topology
