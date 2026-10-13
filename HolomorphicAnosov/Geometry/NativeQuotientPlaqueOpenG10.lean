import HolomorphicAnosov.Geometry.NativeQuotientClassStructuresG10

noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter _root_.Topology

universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- Native open plaques are open embeddings into quotient classes with their transported intrinsic
topologies. (HPS, p. 116) -/
theorem native_quotient_plaque_open_g10 {s : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin s → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (L i)]
    (P : RealTangentDistribution 𝓘(ℝ, E) M)
    (F : HPS.LeafPartition P ι L (fun _ ↦ s)) (R : Setoid M) (q : Quotient R)
    [TopologicalSpace (IntrinsicFoliationLeaf R q)]
    [ChartedSpace (Fin s → ℝ) (IntrinsicFoliationLeaf R q)]
    (i : ι) (e : Diffeomorph 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, Fin s → ℝ)
      (L i) (IntrinsicFoliationLeaf R q) ∞)
    (he : ∀ z : L i, (e z).val = (F.leaf i).inclusion z)
    (k : ι) (j : FoliationCoordinateDisk s → L k) (hj : IsOpenEmbedding j)
    (htag : ∀ z, Quotient.mk R ((F.leaf k).inclusion (j z)) = q) :
    IsOpenEmbedding (fun z ↦
      (⟨(F.leaf k).inclusion (j z), htag z⟩ : IntrinsicFoliationLeaf R q)) := by
  let z0 : FoliationCoordinateDisk s := ⟨0, Metric.mem_ball_self (by norm_num)⟩
  let v0 : IntrinsicFoliationLeaf R q := ⟨(F.leaf k).inclusion (j z0), htag z0⟩
  obtain ⟨a, ha⟩ := e.surjective v0
  have hk : k = i := F.disjoint k i (j z0) a
    ((congrArg Subtype.val ha).symm.trans (he a))
  subst k
  have hfun : (fun z ↦
      (⟨(F.leaf i).inclusion (j z), htag z⟩ : IntrinsicFoliationLeaf R q)) = e ∘ j := by
    funext z
    exact Subtype.ext (he (j z)).symm
  rw [hfun]
  exact e.toHomeomorph.isOpenEmbedding.comp hj



end HolomorphicAnosov
