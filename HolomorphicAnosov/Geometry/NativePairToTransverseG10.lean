import HolomorphicAnosov.Geometry.NativePartitionBoxLeafAtlasesG10
import HolomorphicAnosov.Geometry.NativePartitionGeneratedG10

noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter _root_.Topology

universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- Paired native leaf partitions with compatible product boxes define transverse continuous
foliations with smooth intrinsic leaves and the prescribed tangent distributions. Each quotient
leaf is diffeomorphic to a native leaf, and the foliation retains the given boxes. (HPS,
pp.115–116) -/
theorem native_pair_to_transverse_foliations_with_smooth_leaves {s t : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    {ιs ιu β : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin s → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin t → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin t → ℝ) ∞ (Lu i)]
    (P Q : RealTangentDistribution 𝓘(ℝ, E) M)
    (Fs : HPS.LeafPartition P ιs Ls (fun _ ↦ s))
    (Fu : HPS.LeafPartition Q ιu Lu (fun _ ↦ t))
    (B : β → TransverseFoliationBox s t M)
    (hcover : ∀ x : M, ∃ b, x ∈ (B b).image)
    (hs : ∀ b w, ∃ i : ιs, ∃ j : FoliationCoordinateDisk s → Ls i,
      IsOpenEmbedding j ∧ ∀ z, ((B b).chart (z, w)).val = (Fs.leaf i).inclusion (j z))
    (hu : ∀ b z, ∃ i : ιu, ∃ j : FoliationCoordinateDisk t → Lu i,
      IsOpenEmbedding j ∧ ∀ w, ((B b).chart (z, w)).val = (Fu.leaf i).inclusion (j w)) :
    ∃ F : TransverseContinuousFoliations.{u,u} s t M,
      (∀ x y, F.stablePartition x y ↔ ∃ i a b,
        (Fs.leaf i).inclusion a = x ∧ (Fs.leaf i).inclusion b = y) ∧
      (∀ x y, F.unstablePartition x y ↔ ∃ i a b,
        (Fu.leaf i).inclusion a = x ∧ (Fu.leaf i).inclusion b = y) ∧
      (∀ q : Quotient F.stablePartition,
        letI := F.stableTopology q; letI := F.stableCharts q
        ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
          LinearMap.range (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, E) Subtype.val z).toLinearMap =
            P z.val) ∧
      (∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q; letI := F.unstableCharts q
        ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
          LinearMap.range (mfderiv 𝓘(ℝ, Fin t → ℝ) 𝓘(ℝ, E) Subtype.val z).toLinearMap =
            Q z.val) ∧
      (∀ q : Quotient F.stablePartition,
        letI := F.stableTopology q; letI := F.stableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, Fin s → ℝ)
          (Ls i) (IntrinsicFoliationLeaf F.stablePartition q) ∞,
            ∀ z, (e z).val = (Fs.leaf i).inclusion z) ∧
      (∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q; letI := F.unstableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin t → ℝ) 𝓘(ℝ, Fin t → ℝ)
          (Lu i) (IntrinsicFoliationLeaf F.unstablePartition q) ∞,
            ∀ z, (e z).val = (Fu.leaf i).inclusion z) ∧
      (∀ q : Quotient F.stablePartition,
        letI := F.stableTopology q; letI := F.stableCharts q
        IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (IntrinsicFoliationLeaf F.stablePartition q)) ∧
      (∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q; letI := F.unstableCharts q
        IsManifold 𝓘(ℝ, Fin t → ℝ) ∞ (IntrinsicFoliationLeaf F.unstablePartition q)) ∧
      (∀ b : F.boxIndex, ∃ i : β, F.box b = B i) := by
  classical
  let B' : β → TransverseFoliationBox t s M := fun b ↦
    { image := (B b).image
      isOpen_image := (B b).isOpen_image
      chart := (Homeomorph.prodComm _ _).trans (B b).chart }
  have hcover' : ∀ x : M, ∃ b, x ∈ (B' b).image := hcover
  have hu' : ∀ b w, ∃ i : ιu, ∃ j : FoliationCoordinateDisk t → Lu i,
      IsOpenEmbedding j ∧ ∀ z, ((B' b).chart (z, w)).val = (Fu.leaf i).inclusion (j z) := by
    intro b w
    exact hu b w
  obtain ⟨Rs, hRs, hgenS⟩ := native_partition_generated_by_boxes_g10 P Fs B hcover hs
  obtain ⟨Ru, hRu, hgenU⟩ := native_partition_generated_by_boxes_g10 Q Fu B' hcover' hu'
  have hgenU' : ∀ x y, Ru x y ↔ Relation.EqvGen
      (fun a b ↦ ∃ i : β, ∃ z : FoliationCoordinateDisk s,
        ∃ w w' : FoliationCoordinateDisk t,
          ((B i).chart (z, w)).val = a ∧ ((B i).chart (z, w')).val = b) x y := by
    intro x y
    rw [hgenU x y]
    constructor
    · apply Relation.EqvGen.mono
      rintro a b ⟨i, z, w, w', ha, hb⟩
      exact ⟨i, z, w, w', ha, hb⟩
    · apply Relation.EqvGen.mono
      rintro a b ⟨i, z, w, w', ha, hb⟩
      exact ⟨i, z, w, w', ha, hb⟩
  obtain ⟨ls, hls, ts, cs, hcs, hconts, hops, htops, hms, htans, hids⟩ :=
    native_partition_box_leaf_atlases_g10 P Fs Rs hRs B hcover hs
  let := ts
  let := cs
  obtain ⟨lu, hlu, tu, cu, hcu, hcontu, hopu, htopu, hmu, htanu, hidu⟩ :=
    native_partition_box_leaf_atlases_g10 Q Fu Ru hRu B' hcover' hu'
  let := tu
  let := cu
  let F : TransverseContinuousFoliations.{u,u} s t M :=
    { boxIndex := β
      box := B
      cover := hcover
      stablePartition := Rs
      unstablePartition := Ru
      stable_generated := hgenS
      unstable_generated := hgenU'
      stableTopology := ts
      unstableTopology := tu
      stableCharts := cs
      unstableCharts := cu
      stable_connected := hcs
      unstable_connected := hcu
      stable_inclusion := hconts
      unstable_inclusion := hcontu
      stableLabel := ls
      unstableLabel := lu
      stable_label := hls
      unstable_label := fun b z w ↦ hlu b w z
      stable_plaque := hops
      unstable_plaque := hopu
      stable_topology_generated := htops
      unstable_topology_generated := htopu }
  exact ⟨F, hRs, hRu, htans, htanu, hids, hidu, hms, hmu, fun b ↦ ⟨b,rfl⟩⟩

/-- Paired native leaf partitions with compatible product boxes define transverse continuous
foliations whose intrinsic leaves have the prescribed tangent distributions and are
diffeomorphic to native leaves. -/
theorem native_pair_to_transverse_foliations_g10 {s t : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    {ιs ιu β : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin s → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin t → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin t → ℝ) ∞ (Lu i)]
    (P Q : RealTangentDistribution 𝓘(ℝ, E) M)
    (Fs : HPS.LeafPartition P ιs Ls (fun _ ↦ s))
    (Fu : HPS.LeafPartition Q ιu Lu (fun _ ↦ t))
    (B : β → TransverseFoliationBox s t M)
    (hcover : ∀ x : M, ∃ b, x ∈ (B b).image)
    (hs : ∀ b w, ∃ i : ιs, ∃ j : FoliationCoordinateDisk s → Ls i,
      IsOpenEmbedding j ∧ ∀ z, ((B b).chart (z, w)).val = (Fs.leaf i).inclusion (j z))
    (hu : ∀ b z, ∃ i : ιu, ∃ j : FoliationCoordinateDisk t → Lu i,
      IsOpenEmbedding j ∧ ∀ w, ((B b).chart (z, w)).val = (Fu.leaf i).inclusion (j w)) :
    ∃ F : TransverseContinuousFoliations.{u,u} s t M,
      (∀ x y, F.stablePartition x y ↔ ∃ i a b,
        (Fs.leaf i).inclusion a = x ∧ (Fs.leaf i).inclusion b = y) ∧
      (∀ x y, F.unstablePartition x y ↔ ∃ i a b,
        (Fu.leaf i).inclusion a = x ∧ (Fu.leaf i).inclusion b = y) ∧
      (∀ q : Quotient F.stablePartition,
        letI := F.stableTopology q; letI := F.stableCharts q
        ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
          LinearMap.range (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, E) Subtype.val z).toLinearMap =
            P z.val) ∧
      (∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q; letI := F.unstableCharts q
        ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
          LinearMap.range (mfderiv 𝓘(ℝ, Fin t → ℝ) 𝓘(ℝ, E) Subtype.val z).toLinearMap =
            Q z.val) ∧
      (∀ q : Quotient F.stablePartition,
        letI := F.stableTopology q; letI := F.stableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, Fin s → ℝ)
          (Ls i) (IntrinsicFoliationLeaf F.stablePartition q) ∞,
            ∀ z, (e z).val = (Fs.leaf i).inclusion z) ∧
      (∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q; letI := F.unstableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin t → ℝ) 𝓘(ℝ, Fin t → ℝ)
          (Lu i) (IntrinsicFoliationLeaf F.unstablePartition q) ∞,
            ∀ z, (e z).val = (Fu.leaf i).inclusion z) := by
  obtain ⟨F, hRs, hRu, htans, htanu, hids, hidu, _, _, _⟩ :=
    native_pair_to_transverse_foliations_with_smooth_leaves P Q Fs Fu B hcover hs hu
  exact ⟨F, hRs, hRu, htans, htanu, hids, hidu⟩



end HolomorphicAnosov
