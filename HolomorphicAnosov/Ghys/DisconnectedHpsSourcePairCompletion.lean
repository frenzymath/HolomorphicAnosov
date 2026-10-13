import HolomorphicAnosov.Geometry.NativeLeafOnIntrinsicClass
import HolomorphicAnosov.Geometry.FixedUnitProductNativePlaquesG10
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.original_real_tangent_finrank
import HolomorphicAnosov.Ghys.DisconnectedHpsCommonProductBoxes
import HolomorphicAnosov.Geometry.NativePairToTransverseG10
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification

/-! This file constructs the intrinsic real stable and unstable transverse pair from the source HPS laminations in the disconnected setting. (HPS, §7; Ghys, §2) -/

noncomputable section
open scoped ContDiff Manifold Topology
open Set _root_.Topology
set_option linter.style.haveILetI false
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- For a nonempty compact manifold with rank-one Anosov data, the source stable and unstable laminations yield an intrinsic real transverse pair and common product structure. (HPS, §7; Ghys, §2) -/
theorem disconnected_hps_source_pair_completion
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (_hmetric : (inferInstance : MetricSpace M).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M))
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (hres : ∃ N : ℕ, 0 < N ∧
      (∀ x : M,
        connectedComponent (((f : M → M)^[N]) x) = connectedComponent x) ∧
      (∀ x y : M,
        ForwardAsymptotic (((f : M → M)^[N])) x y ↔
          ForwardAsymptotic (f : M → M) x y) ∧
      (∀ x y : M,
        ForwardAsymptotic (((f.symm : M → M)^[N])) x y ↔
          ForwardAsymptotic (f.symm : M → M) x y)) :
    ∃ B : ComplexModel d ≃L[ℝ] (Fin ((2*d-2)+2) → ℝ),
      letI := realCoordinateRechart (M := M) B
      ∃ F : TransverseContinuousFoliations.{u,u} (2*d-2) 2 M,
        ((∀ x y, F.stablePartition x y ↔ @ForwardAsymptotic M (inferInstance : MetricSpace M) f x y) ∧
          (∀ x y, F.unstablePartition x y ↔ @ForwardAsymptotic M (inferInstance : MetricSpace M) f.symm x y)) ∧
        (∀ q : Quotient F.stablePartition,
          letI := F.stableTopology q
          letI := F.stableCharts q
          ∃ smooth : IsManifold 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞
              (IntrinsicFoliationLeaf F.stablePartition q),
            letI := smooth
            ∃ N : HPS.NativeLeaf (r := 2*d-2)
              a.splitting.stable.toDistribution
              (IntrinsicFoliationLeaf F.stablePartition q),
            N.inclusion = Subtype.val) ∧
        (∀ q : Quotient F.unstablePartition,
          letI := F.unstableTopology q
          letI := F.unstableCharts q
          ∃ smooth : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞
              (IntrinsicFoliationLeaf F.unstablePartition q),
            letI := smooth
            ∃ N : HPS.NativeLeaf (r := 2)
              a.splitting.unstable.toDistribution
              (IntrinsicFoliationLeaf F.unstablePartition q),
    N.inclusion = Subtype.val) := by
  classical
  let x : M := Classical.choice inferInstance
  have htwo := TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank x
  have hbound := (a.splitting.unstable.toDistribution x).finrank_le
  rw [htwo, TheoremAProof.Dimension.original_real_tangent_finrank x] at hbound
  have hdim : (2*d-2)+2 = 2*d := by omega
  let B : ComplexModel d ≃L[ℝ] (Fin ((2*d-2)+2) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [ComplexModel, finrank_real_of_complex, hdim])
  refine ⟨B, ?_⟩
  letI := realCoordinateRechart (M := M) B
  obtain ⟨ιs, ιu, Ls, Lu, topS, topU, h⟩ :=
    disconnected_hps_common_product_boxes f a hRank
  letI := topS
  letI := topU
  obtain ⟨chartS, chartU, h⟩ := h
  letI := chartS
  letI := chartU
  obtain ⟨smoothS, smoothU, Fs, Fu, hrS, hrU, hsource⟩ := h
  letI := smoothS
  letI := smoothU
  have hboxes : ∀ p : M, ∃ C : TransverseFoliationBox (2*d-2) 2 M,
      p ∈ C.image ∧
      (∀ w, ∃ i : ιs, ∃ j : FoliationCoordinateDisk (2*d-2) → Ls i,
        IsOpenEmbedding j ∧ ∀ z, (C.chart (z,w)).val = (Fs.leaf i).inclusion (j z)) ∧
      (∀ z, ∃ i : ιu, ∃ j : FoliationCoordinateDisk 2 → Lu i,
        IsOpenEmbedding j ∧ ∀ w, (C.chart (z,w)).val = (Fu.leaf i).inclusion (j w)) := by
    intro p
    obtain ⟨Ds, Du, O, e, hp, hs, hu⟩ := hsource p
    exact fixed_unit_product_box_native_plaques_g10
      (fun i ↦ (Fs.leaf i).inclusion) (fun i ↦ (Fu.leaf i).inclusion)
      Ds Du O e ⟨p, hp⟩ hs hu
  let C : M → TransverseFoliationBox (2*d-2) 2 M := fun p ↦ (hboxes p).choose
  obtain ⟨F, hRs, hRu, htS, htU, heS, heU, hmS, hmU, _⟩ :=
    native_pair_to_transverse_foliations_with_smooth_leaves
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution Fs Fu C
      (fun p ↦ ⟨p, (hboxes p).choose_spec.1⟩)
      (fun p ↦ (hboxes p).choose_spec.2.1)
      (fun p ↦ (hboxes p).choose_spec.2.2)
  refine ⟨F, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    rw [hRs]
    constructor
    · rintro ⟨i, z, w, rfl, rfl⟩
      have hw : (Fs.leaf i).inclusion w ∈ Set.range (Fs.leaf i).inclusion := ⟨w, rfl⟩
      rw [hrS i z] at hw
      exact hw
    · intro hxy
      obtain ⟨i, z, hz⟩ := Fs.cover x
      have hy : y ∈ Set.range (Fs.leaf i).inclusion := by
        rw [hrS i z, hz]
        exact hxy
      obtain ⟨w, hw⟩ := hy
      exact ⟨i, z, w, hz, hw⟩
  · intro x y
    rw [hRu]
    constructor
    · rintro ⟨i, z, w, rfl, rfl⟩
      have hw : (Fu.leaf i).inclusion w ∈ Set.range (Fu.leaf i).inclusion := ⟨w, rfl⟩
      rw [hrU i z] at hw
      exact hw
    · intro hxy
      obtain ⟨i, z, hz⟩ := Fu.cover x
      have hy : y ∈ Set.range (Fu.leaf i).inclusion := by
        rw [hrU i z, hz]
        exact hxy
      obtain ⟨w, hw⟩ := hy
      exact ⟨i, z, w, hz, hw⟩
  · intro q
    letI := F.stableTopology q
    letI := F.stableCharts q
    letI := hmS q
    refine ⟨hmS q, ?_⟩
    obtain ⟨i, e, he⟩ := heS q
    exact native_leaf_on_intrinsic_class a.splitting.stable.toDistribution
      (Fs.leaf i) F.stablePartition q e he (htS q)
  · intro q
    letI := F.unstableTopology q
    letI := F.unstableCharts q
    letI := hmU q
    refine ⟨hmU q, ?_⟩
    obtain ⟨i, e, he⟩ := heU q
    exact native_leaf_on_intrinsic_class a.splitting.unstable.toDistribution
      (Fu.leaf i) F.unstablePartition q e he (htU q)

end HolomorphicAnosov.Ghys
