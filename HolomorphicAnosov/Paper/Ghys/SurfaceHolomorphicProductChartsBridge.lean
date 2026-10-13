import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveLocalProductChartBridge
import HolomorphicAnosov.Paper.Ghys.ProjectiveNativeIdentificationComplexTransport
import HolomorphicAnosov.Paper.Ghys.NativeAffineTransverseProjectiveAtlas
import HolomorphicAnosov.Geometry.NativeReceivingBiholomorphs
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Ghys.CompleteAffineTransportWithCharts
import HolomorphicAnosov.Ghys.NativeAffineFieldAdapter
import HolomorphicAnosov.Paper.Ghys.NativeTransverseCoordinateScalar
import HolomorphicAnosov.Paper.Ghys.InverseNativeTransverseCoordinateScalar
import HolomorphicAnosov.Paper.Ghys.PairedScalarProjectiveChart
import HolomorphicAnosov.Paper.Ghys.OrderedProductGermsOfTransverseCoordinates
import HolomorphicAnosov.Geometry.ComplexSubmoduleTransfer

/-!
# Bridge for the ordered holomorphic product-chart construction

This file packages the native stable and unstable leaves, their complete affine structures, and compatible local projective product charts into the ordered holomorphic product-chart atlas (Ghys, §§2–5; HPS, §§6B–7).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov.Ghys

open Set Filter _root_.Topology
open scoped ContDiff Manifold

universe u

attribute [local instance] complex_isManifold_real



structure SurfaceProjectiveG3HolomorphicProductChartsBridgeData
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (stable_rank : HasComplexRankOne a.splitting.stable.toDistribution)
    (unstable_rank : HasComplexRankOne a.splitting.unstable.toDistribution) where
  result :
∃ A : OrderedProjectiveProductAtlas.{u, u} f a,
      ∀ (x : S) (α β : ℂ → S) (rα rβ : ℝ),
        0 < rα → 0 < rβ → α 0 = x → β 0 = x →
        ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ α (Metric.ball 0 rα) →
        ContMDiffOn 𝓘(ℂ) (complexModel 2) ∞ β (Metric.ball 0 rβ) →
        IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rα) ↦ α z) →
        IsEmbedding (fun z : ↥(Metric.ball (0 : ℂ) rβ) ↦ β z) →
        (∀ z ∈ Metric.ball (0 : ℂ) rα,
          LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) α z).toLinearMap =
            a.splitting.stable.toDistribution (α z)) →
        (∀ z ∈ Metric.ball (0 : ℂ) rβ,
          LinearMap.range (mfderiv 𝓘(ℝ, ℂ) (realModel 2) β z).toLinearMap =
            a.splitting.unstable.toDistribution (β z)) →
        ∃ (rs ru : ℝ) (e : OpenPartialHomeomorph (ℂ × ℂ) S) (i : A.index),
          0 < rs ∧ rs ≤ rα ∧ 0 < ru ∧ ru ≤ rβ ∧
          e.source = Metric.ball (0 : ℂ) rs ×ˢ Metric.ball (0 : ℂ) ru ∧
          x ∈ e.target ∧
          ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e e.source ∧
          ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e.symm e.target ∧
          ∀ s ∈ Metric.ball (0 : ℂ) rs, ∀ w ∈ Metric.ball (0 : ℂ) ru,
            α s ∈ (A.chart i).source ∧ β w ∈ (A.chart i).source ∧
            e (s, w) ∈ (A.chart i).source ∧
            A.chart i (e (s, w)) = ((A.chart i (α s)).1, (A.chart i (β w)).2) ∧
            e (s, 0) = α s ∧ e (0, w) = β w ∧
            ∀ y ∈ (A.chart i).source,
              ((A.chart i y).1 = (A.chart i (α s)).1 ∧
                (A.chart i y).2 = (A.chart i (β w)).2) ↔ y = e (s, w)


/-- Combines a native asymptotic leaf with its compatible complex charts and complete affine structure. -/
def native_complete_affine_leaf_of_upgrade
    {S : Type u} [MetricSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (g : S ≃ₜ S) (P : RealTangentDistribution (realModel 2) S) (x : S)
    (N : NativeAsymptoticLeafDatum (realModel 2) g P x)
    (hr : N.rank = 2)
    (U : letI := N.topology; letI := N.charts
      NativeLeafComplexUpgrade (d := 2) (r := N.rank) 1
        (Subtype.val : StableAsymptoticLeaf g x → S))
    (A : letI := N.topology; letI := N.charts; letI := U.charts
      ComplexAffineStructure (StableAsymptoticLeaf g x))
    (hA : letI := N.topology; letI := N.charts; letI := U.charts
      ComplexAffineStructure.Complete (StableAsymptoticLeaf g x) A) :
    NativeCompleteAffineAsymptoticLeaf g P x := by
  letI := N.topology
  letI := N.charts
  letI := N.smoothAtlas
  letI := U.charts
  exact { native := N
          rank_two := hr
          complexCharts := U.charts
          complexManifold := U.complex_manifold
          realCompatibility := native_complex_upgrade_identity_mdifferentiable U
          inclusion_holomorphic := U.inclusion_holomorphic
          affineStructure := A
          complete := hA }

/-- The bridge data package an ordered projective atlas whose charts provide the local biholomorphic product and axis properties for holomorphic stable and unstable plaques (Ghys, §§2–5; HPS, §§6B–7). -/
theorem surface_projective_g3_holomorphic_product_charts_bridge_g7
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (stable_rank : HasComplexRankOne a.splitting.stable.toDistribution)
    (unstable_rank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    SurfaceProjectiveG3HolomorphicProductChartsBridgeData f a stable_rank unstable_rank := by
  classical
  rcases isEmpty_or_nonempty S with hEmpty | hNonempty
  · let : IsEmpty S := hEmpty
    let metric : MetricSpace S := MetricSpace.induced (isEmptyElim : S → Empty)
      (by intro x; exact isEmptyElim x) inferInstance
    let A : OrderedProjectiveProductAtlas.{u, u} f a := {
      metric := metric
      metric_topology := Subsingleton.elim _ _
      stableLeaf := fun x ↦ isEmptyElim x
      unstableLeaf := fun x ↦ isEmptyElim x
      index := PEmpty
      chart := fun i ↦ isEmptyElim i
      cover := fun x ↦ isEmptyElim x
      holomorphic := fun i ↦ isEmptyElim i
      transition := fun i ↦ isEmptyElim i
      transition_locallyConstant := fun i ↦ isEmptyElim i
      transition_self := fun i ↦ isEmptyElim i
      transition_comp := fun i ↦ isEmptyElim i
      transition_agrees := fun i ↦ isEmptyElim i
      stable_kernel := fun i ↦ isEmptyElim i
      unstable_kernel := fun i ↦ isEmptyElim i
      stable_affine := fun x ↦ isEmptyElim x
      unstable_affine := fun x ↦ isEmptyElim x }
    exact ⟨⟨A, fun x ↦ isEmptyElim x⟩⟩
  · let : Nonempty S := hNonempty
    let metric : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
    let : MetricSpace S := metric
    have hMetricTopology : (inferInstance : TopologicalSpace S) =
        metric.toUniformSpace.toTopologicalSpace := by
      rfl
    have hUnstableReal : ∀ x : S,
        Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2 := by
      intro x
      exact TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two unstable_rank x
    obtain ⟨s, B, _⟩ := projective_native_identification f a
      (Classical.choice hNonempty) hUnstableReal
    obtain ⟨C, hC, hCompare⟩ :=
      projective_native_identification_complex_transport f a s B
    obtain ⟨affine, hComplete, atlasU, hAtlasU⟩ :=
      native_affine_transverse_projective_atlas f a hUnstableReal s B C hC
    obtain ⟨E, hE⟩ := native_receiving_biholomorphs B C hC
    have hNativeUPoints (x : S) :
        letI := B.realAmbientCharts
        letI := C.charts (Quotient.mk B.F.unstablePartition x)
        letI := B.unstableTopology x
        letI := B.unstableCharts x
        letI := (B.complexU1 x).charts
        ∀ z : B.F.ULeaf x, (E x z).val = z.val := by
      let := B.realAmbientCharts
      let := C.charts (Quotient.mk B.F.unstablePartition x)
      let := B.unstableTopology x
      let := B.unstableCharts x
      let := (B.complexU1 x).charts
      intro z
      change ((E x).toHomeomorph z).val = z.val
      rw [hE]
      exact B.unstable_points x z
    let hNativeU (x : S) : NativeCompleteAffineAsymptoticLeaf
        f.toHomeomorph.symm a.splitting.unstable.toDistribution x := by
      letI := B.realAmbientCharts
      letI := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
      letI := C.charts (Quotient.mk B.F.unstablePartition x)
      letI := (B.nativeU x).topology
      letI := (B.nativeU x).charts
      letI := (B.complexU1 x).charts
      let H := complete_affine_structure_transport_with_charts (E x)
        (affine.atPoint B.F C x) (hComplete (Quotient.mk B.F.unstablePartition x))
      let A := Classical.choose H
      have hA := (Classical.choose_spec H).1
      exact native_complete_affine_leaf_of_upgrade f.toHomeomorph.symm
        a.splitting.unstable.toDistribution x (B.nativeU x)
        (B.rankU x) (B.complexU1 x) A hA
    have hNativeUCharts (x : S) :
        letI := B.realAmbientCharts
        letI := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
        letI := C.charts (Quotient.mk B.F.unstablePartition x)
        letI := B.unstableTopology x
        letI := B.unstableCharts x
        letI := (B.complexU1 x).charts
        ∀ c : OpenPartialHomeomorph (UnstableAsymptoticLeaf f.toHomeomorph x) ℂ,
          c ∈ ComplexAffineStructure.maximalAtlas _ (hNativeU x).affineStructure ↔
            (E x).toHomeomorph.toOpenPartialHomeomorph.trans c ∈
              ComplexAffineStructure.maximalAtlas _ (affine.atPoint B.F C x) := by
      let := B.realAmbientCharts
      let := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
      let := C.charts (Quotient.mk B.F.unstablePartition x)
      let := (B.nativeU x).topology
      let := (B.nativeU x).charts
      let := (B.complexU1 x).charts
      exact (Classical.choose_spec (complete_affine_structure_transport_with_charts (E x)
        (affine.atPoint B.F C x) (hComplete (Quotient.mk B.F.unstablePartition x)))).2
    have hNativeUAffine :
        letI := B.realAmbientCharts
        ∀ cT ∈ atlasU.charts, ∀ x : S,
        letI := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
        letI := C.charts (Quotient.mk B.F.unstablePartition x)
        letI := B.unstableTopology x
        letI := B.unstableCharts x
        letI := (B.complexU1 x).charts
        ∀ y : UnstableAsymptoticLeaf f.toHomeomorph x,
          y.val ∈ cT.domain B.F C →
          ∃ cN ∈ ComplexAffineStructure.maximalAtlas _ (hNativeU x).affineStructure,
            y ∈ cN.source ∧ ∃ g : ComplexMobiusTransformation,
              ∀ᶠ z in 𝓝 y, z ∈ cN.source ∧ z.val ∈ cT.domain B.F C ∧
                cT.transverseCoordinate B.F C z.val =
                  g.apply (complexProjectiveLineFinite (cN z)) := by
      let := B.realAmbientCharts
      intro cT hcT x
      let := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
      let := C.charts (Quotient.mk B.F.unstablePartition x)
      let := B.unstableTopology x
      let := B.unstableCharts x
      let := (B.complexU1 x).charts
      intro y hy
      apply projective_affine_germ_of_transport_with_charts (E x)
        (affine.atPoint B.F C x) (hNativeU x).affineStructure
        (hNativeUCharts x) Subtype.val Subtype.val (hNativeUPoints x)
        (cT.domain B.F C) (cT.transverseCoordinate B.F C) y
      apply hAtlasU cT hcT x ((E x).symm y)
      have hp := hNativeUPoints x ((E x).symm y)
      rw [(E x).apply_symm_apply] at hp
      exact hp ▸ hy
    let ainv := TheoremAProof.inverseAnosovDatum f a
    have hStableReal : ∀ x : S,
        Module.finrank ℝ (ainv.splitting.unstable.toDistribution x) = 2 := by
      intro x
      exact TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two stable_rank x
    obtain ⟨t, Bs, _⟩ := projective_native_identification f.symm ainv
      (Classical.choice hNonempty) hStableReal
    obtain ⟨Cs, hCs, _⟩ :=
      projective_native_identification_complex_transport f.symm ainv t Bs
    obtain ⟨affineS, hCompleteS, atlasS, hAtlasS⟩ :=
      native_affine_transverse_projective_atlas f.symm ainv hStableReal t Bs Cs hCs
    obtain ⟨Es, hEs⟩ := native_receiving_biholomorphs Bs Cs hCs
    have hNativeSPoints (x : S) :
        letI := Bs.realAmbientCharts
        letI := Cs.charts (Quotient.mk Bs.F.unstablePartition x)
        letI := Bs.unstableTopology x
        letI := Bs.unstableCharts x
        letI := (Bs.complexU1 x).charts
        ∀ z : Bs.F.ULeaf x, (Es x z).val = z.val := by
      let := Bs.realAmbientCharts
      let := Cs.charts (Quotient.mk Bs.F.unstablePartition x)
      let := Bs.unstableTopology x
      let := Bs.unstableCharts x
      let := (Bs.complexU1 x).charts
      intro z
      change ((Es x).toHomeomorph z).val = z.val
      rw [hEs]
      exact Bs.unstable_points x z
    let hNativeS (x : S) : NativeCompleteAffineAsymptoticLeaf
        f.toHomeomorph a.splitting.stable.toDistribution x := by
      letI := Bs.realAmbientCharts
      letI := Bs.F.unstableTopology (Quotient.mk Bs.F.unstablePartition x)
      letI := Cs.charts (Quotient.mk Bs.F.unstablePartition x)
      letI := (Bs.nativeU x).topology
      letI := (Bs.nativeU x).charts
      letI := (Bs.complexU1 x).charts
      let H := complete_affine_structure_transport_with_charts (Es x)
        (affineS.atPoint Bs.F Cs x) (hCompleteS (Quotient.mk Bs.F.unstablePartition x))
      let A := Classical.choose H
      have hA := (Classical.choose_spec H).1
      exact native_complete_affine_leaf_of_upgrade f.toHomeomorph
        a.splitting.stable.toDistribution x (Bs.nativeU x)
        (Bs.rankU x) (Bs.complexU1 x) A hA
    have hNativeSCharts (x : S) :
        letI := Bs.realAmbientCharts
        letI := Bs.F.unstableTopology (Quotient.mk Bs.F.unstablePartition x)
        letI := Cs.charts (Quotient.mk Bs.F.unstablePartition x)
        letI := Bs.unstableTopology x
        letI : TopologicalSpace (StableAsymptoticLeaf f.toHomeomorph x) :=
          (hNativeS x).native.topology
        letI := Bs.unstableCharts x
        letI := (Bs.complexU1 x).charts
        letI : ChartedSpace (ComplexModel 1) (StableAsymptoticLeaf f.toHomeomorph x) :=
          (hNativeS x).complexCharts
        ∀ c : OpenPartialHomeomorph (StableAsymptoticLeaf f.toHomeomorph x) ℂ,
          c ∈ ComplexAffineStructure.maximalAtlas _ (hNativeS x).affineStructure ↔
            (Es x).toHomeomorph.toOpenPartialHomeomorph.trans c ∈
              ComplexAffineStructure.maximalAtlas _ (affineS.atPoint Bs.F Cs x) := by
      let := Bs.realAmbientCharts
      let := Bs.F.unstableTopology (Quotient.mk Bs.F.unstablePartition x)
      let := Cs.charts (Quotient.mk Bs.F.unstablePartition x)
      let := (Bs.nativeU x).topology
      let := (Bs.nativeU x).charts
      let := (Bs.complexU1 x).charts
      exact (Classical.choose_spec (complete_affine_structure_transport_with_charts (Es x)
        (affineS.atPoint Bs.F Cs x) (hCompleteS (Quotient.mk Bs.F.unstablePartition x)))).2
    have hNativeSAffine :
        letI := Bs.realAmbientCharts
        ∀ cT ∈ atlasS.charts, ∀ x : S,
        letI := Bs.F.unstableTopology (Quotient.mk Bs.F.unstablePartition x)
        letI := Cs.charts (Quotient.mk Bs.F.unstablePartition x)
        letI := Bs.unstableTopology x
        letI : TopologicalSpace (StableAsymptoticLeaf f.toHomeomorph x) :=
          (hNativeS x).native.topology
        letI := Bs.unstableCharts x
        letI := (Bs.complexU1 x).charts
        letI : ChartedSpace (ComplexModel 1) (StableAsymptoticLeaf f.toHomeomorph x) :=
          (hNativeS x).complexCharts
        ∀ y : UnstableAsymptoticLeaf f.symm.toHomeomorph x,
          y.val ∈ cT.domain Bs.F Cs →
          ∃ cN ∈ ComplexAffineStructure.maximalAtlas _ (hNativeS x).affineStructure,
            y ∈ cN.source ∧ ∃ g : ComplexMobiusTransformation,
              ∀ᶠ z in 𝓝 y, z ∈ cN.source ∧ z.val ∈ cT.domain Bs.F Cs ∧
                cT.transverseCoordinate Bs.F Cs z.val =
                  g.apply (complexProjectiveLineFinite (cN z)) := by
      let := Bs.realAmbientCharts
      intro cT hcT x
      let := Bs.F.unstableTopology (Quotient.mk Bs.F.unstablePartition x)
      let := Cs.charts (Quotient.mk Bs.F.unstablePartition x)
      let := Bs.unstableTopology x
      let := Bs.unstableCharts x
      let := (Bs.complexU1 x).charts
      intro y hy
      apply projective_affine_germ_of_transport_with_charts (Es x)
        (affineS.atPoint Bs.F Cs x) (hNativeS x).affineStructure
        (hNativeSCharts x) Subtype.val Subtype.val (hNativeSPoints x)
        (cT.domain Bs.F Cs) (cT.transverseCoordinate Bs.F Cs) y
      apply hAtlasS cT hcT x ((Es x).symm y)
      have hp := hNativeSPoints x ((Es x).symm y)
      rw [(Es x).apply_symm_apply] at hp
      exact hp ▸ hy
    have hChartAt (x : S) :
        letI := B.realAmbientCharts
        letI := Bs.realAmbientCharts
        ∃ cU ∈ atlasU.charts, ∃ cS ∈ atlasS.charts,
        ∃ e : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine),
          x ∈ e.source ∧ e.source ⊆ cU.domain B.F C ∧
          e.source ⊆ cS.domain Bs.F Cs ∧
          (∀ y ∈ e.source, e y =
            (cS.transverseCoordinate Bs.F Cs y,cU.transverseCoordinate B.F C y)) ∧
          ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞ e e.source ∧
          ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞ e.symm e.target ∧
          (∀ y ∈ e.source,
            (mfderiv (realModel 2) (realModel 1) (fun z ↦ (e z).1) y).ker =
              a.splitting.unstable.toDistribution y) ∧
          (∀ y ∈ e.source,
            (mfderiv (realModel 2) (realModel 1) (fun z ↦ (e z).2) y).ker =
              a.splitting.stable.toDistribution y) ∧
          ∃ (q₁ q₂ : S → ℂ) (R₁ R₂ : ℂ → ComplexProjectiveLine),
            (∀ y ∈ e.source, e y = (R₁ (q₁ y),R₂ (q₂ y))) ∧
            (∀ y ∈ e.source, MDifferentiableAt (realModel 2) 𝓘(ℝ,ℂ) q₁ y ∧
              (mfderiv (realModel 2) 𝓘(ℝ,ℂ) q₁ y).ker = a.splitting.unstable.toDistribution y) ∧
            (∀ y ∈ e.source, MDifferentiableAt (realModel 2) 𝓘(ℝ,ℂ) q₂ y ∧
              (mfderiv (realModel 2) 𝓘(ℝ,ℂ) q₂ y).ker = a.splitting.stable.toDistribution y) := by
      let := B.realAmbientCharts
      let := Bs.realAmbientCharts
      obtain ⟨cU,hcU,hxU⟩ := atlasU.cover x
      obtain ⟨cS,hcS,hxS⟩ := atlasS.cover x
      obtain ⟨k₂,q₂,N₂,hx₂,hN₂,hk₂,hk₂i,hq₂,hv₂,hker₂⟩ :=
        native_transverse_coordinate_scalar_kernel (by omega) f a unstable_rank B C hC cU x hxU
      obtain ⟨k₁,q₁,N₁,hx₁,hN₁,hk₁,hk₁i,hq₁,hv₁,hker₁⟩ :=
        inverse_native_transverse_coordinate_scalar_kernel
          (by omega) f a stable_rank Bs Cs hCs cS x hxS
      let O : Set S := (N₁ : Set S) ∩ N₂
      have hO : IsOpen O := N₁.isOpen.inter N₂.isOpen
      have hxO : x ∈ O := ⟨hx₁,hx₂⟩
      have hcompl : ∀ y ∈ O, IsCompl
          (mfderiv (complexModel 2) 𝓘(ℂ) q₁ y).ker
          (mfderiv (complexModel 2) 𝓘(ℂ) q₂ y).ker := by
        intro y hy
        apply isCompl_of_realifications (complexTangentToReal 2 y).toLinearEquiv
        rw [(hker₁ y hy.1).2,(hker₂ y hy.2).2]
        exact (a.splitting.isCompl y).symm
      obtain ⟨e,hxe,heO,heval,he,hei⟩ :=
        surface_scalar_pair_projective_chart_in_coordinates q₁ q₂ O hO x hxO
          (hq₁.mono Set.inter_subset_left) (hq₂.mono Set.inter_subset_right) hcompl
          k₁ k₂ hk₁ hk₁i hk₂ hk₂i (hv₁ x hx₁).1 (hv₂ x hx₂).1
      refine ⟨cU,hcU,cS,hcS,e,hxe,(fun y hy ↦ hN₂ (heO hy).2),
        (fun y hy ↦ hN₁ (heO hy).1),?_,he,hei,?_,?_,?_⟩
      · intro y hy
        rw [heval y hy,(hv₁ y (heO hy).1).2,(hv₂ y (heO hy).2).2]
      · intro y hy
        have hqc := (hq₁ y (heO hy).1).contMDiffAt (N₁.isOpen.mem_nhds (heO hy).1)
          |>.mdifferentiableAt (by simp)
        have hqr : MDifferentiableAt (realModel 2) 𝓘(ℝ,ℂ) q₁ y :=
          (show HasMFDerivAt (realModel 2) 𝓘(ℝ,ℂ) q₁ y
              ((mfderiv (complexModel 2) 𝓘(ℂ) q₁ y).restrictScalars ℝ) from
            ⟨hqc.continuousAt,hqc.hasMFDerivAt.2.restrictScalars ℝ⟩).mdifferentiableAt
        have hv : (fun z ↦ (e z).1) =ᶠ[𝓝 y] k₁.symm ∘ q₁ := by
          filter_upwards [e.open_source.mem_nhds hy] with z hz
          exact congrArg Prod.fst (heval z hz)
        rw [projective_coordinate_inverse_real_kernel_of_eventuallyEq q₁ _ y hqr
          k₁ hk₁ hk₁i (hv₁ y (heO hy).1).1 hv,
          scalar_real_kernel_eq_complex_kernel q₁ y hqc]
        exact (hker₁ y (heO hy).1).2
      · intro y hy
        have hqc := (hq₂ y (heO hy).2).contMDiffAt (N₂.isOpen.mem_nhds (heO hy).2)
          |>.mdifferentiableAt (by simp)
        have hqr : MDifferentiableAt (realModel 2) 𝓘(ℝ,ℂ) q₂ y :=
          (show HasMFDerivAt (realModel 2) 𝓘(ℝ,ℂ) q₂ y
              ((mfderiv (complexModel 2) 𝓘(ℂ) q₂ y).restrictScalars ℝ) from
            ⟨hqc.continuousAt,hqc.hasMFDerivAt.2.restrictScalars ℝ⟩).mdifferentiableAt
        have hv : (fun z ↦ (e z).2) =ᶠ[𝓝 y] k₂.symm ∘ q₂ := by
          filter_upwards [e.open_source.mem_nhds hy] with z hz
          exact congrArg Prod.snd (heval z hz)
        rw [projective_coordinate_inverse_real_kernel_of_eventuallyEq q₂ _ y hqr
          k₂ hk₂ hk₂i (hv₂ y (heO hy).2).1 hv,
          scalar_real_kernel_eq_complex_kernel q₂ y hqc]
        exact (hker₂ y (heO hy).2).2
      · refine ⟨q₁,q₂,k₁.symm,k₂.symm,heval,?_,?_⟩
        · intro y hy
          have hqc := (hq₁ y (heO hy).1).contMDiffAt (N₁.isOpen.mem_nhds (heO hy).1)
            |>.mdifferentiableAt (by simp)
          refine ⟨?_,(scalar_real_kernel_eq_complex_kernel q₁ y hqc).trans
            (hker₁ y (heO hy).1).2⟩
          exact (show HasMFDerivAt (realModel 2) 𝓘(ℝ,ℂ) q₁ y
              ((mfderiv (complexModel 2) 𝓘(ℂ) q₁ y).restrictScalars ℝ) from
            ⟨hqc.continuousAt,hqc.hasMFDerivAt.2.restrictScalars ℝ⟩).mdifferentiableAt
        · intro y hy
          have hqc := (hq₂ y (heO hy).2).contMDiffAt (N₂.isOpen.mem_nhds (heO hy).2)
            |>.mdifferentiableAt (by simp)
          refine ⟨?_,(scalar_real_kernel_eq_complex_kernel q₂ y hqc).trans
            (hker₂ y (heO hy).2).2⟩
          exact (show HasMFDerivAt (realModel 2) 𝓘(ℝ,ℂ) q₂ y
              ((mfderiv (complexModel 2) 𝓘(ℂ) q₂ y).restrictScalars ℝ) from
            ⟨hqc.continuousAt,hqc.hasMFDerivAt.2.restrictScalars ℝ⟩).mdifferentiableAt
    choose cU hcU cS hcS chart hcover hdomU hdomS hvalues hhol hinv hkerU hkerS hscalar using hChartAt
    let := B.realAmbientCharts
    let := Bs.realAmbientCharts
    obtain ⟨hgerm,hunique⟩ := ordered_product_germs_of_transverse_coordinates chart
      (fun i ↦ (cS i).transverseCoordinate Bs.F Cs)
      (fun i ↦ (cU i).transverseCoordinate B.F C)
      (fun i x hx ↦ Filter.eventuallyEq_of_mem ((chart i).open_source.mem_nhds hx)
        (fun y hy ↦ hvalues i y hy))
      (fun i j x hx ↦ atlasS.compatible (cS i) (hcS i) (cS j) (hcS j) x
        ⟨hdomS i hx.1,hdomS j hx.2⟩)
      (fun i j x hx ↦ atlasU.compatible (cU i) (hcU i) (cU j) (hcU j) x
        ⟨hdomU i hx.1,hdomU j hx.2⟩)

    let D : OrderedProjectiveProductGermData f a := {
      metric := metric
      metric_topology := hMetricTopology
      stableLeaf := hNativeS
      unstableLeaf := hNativeU
      index := S
      chart := chart
      cover := fun x ↦ ⟨x,hcover x⟩
      holomorphic := fun i ↦ ⟨hhol i,hinv i⟩
      local_germ := hgerm
      local_unique := hunique
      stable_kernel := hkerS
      unstable_kernel := hkerU
      stable_affine := by
        intro x i
        dsimp only
        let := (hNativeS x).native.topology
        let := (hNativeS x).complexCharts
        intro y hy
        obtain ⟨q₁,q₂,R₁,R₂,hval,hq₁,hq₂⟩ := hscalar i
        apply native_stable_affine_field_of_transverse_germ f.toHomeomorph
          a.splitting.stable.toDistribution x (hNativeS x) (chart i)
          ((cS i).transverseCoordinate Bs.F Cs) q₂ R₂
          (fun z hz ↦ congrArg Prod.fst (hvalues i z hz))
          (fun z hz ↦ congrArg Prod.snd (hval z hz))
          (fun z hz ↦ (hq₂ z hz).1) (fun z hz v hv ↦ by
            change v ∈ (mfderiv (realModel 2) 𝓘(ℝ,ℂ) q₂ z).ker
            rw [(hq₂ z hz).2]
            exact hv) y hy
        obtain ⟨d,hd,hyd,g,hg⟩ := hNativeSAffine (cS i) (hcS i) x y (hdomS i hy)
        exact ⟨d,hd,hyd,g,hg.mono (fun z hz ↦ ⟨hz.1,hz.2.2⟩)⟩
      unstable_affine := by
        intro x i
        dsimp only
        let := (hNativeU x).native.topology
        let := (hNativeU x).complexCharts
        intro y hy
        obtain ⟨q₁,q₂,R₁,R₂,hval,hq₁,hq₂⟩ := hscalar i
        apply native_unstable_affine_field_of_transverse_germ f.toHomeomorph
          a.splitting.unstable.toDistribution x (hNativeU x) (chart i)
          ((cU i).transverseCoordinate B.F C) q₁ R₁
          (fun z hz ↦ congrArg Prod.snd (hvalues i z hz))
          (fun z hz ↦ congrArg Prod.fst (hval z hz))
          (fun z hz ↦ (hq₁ z hz).1) (fun z hz v hv ↦ by
            change v ∈ (mfderiv (realModel 2) 𝓘(ℝ,ℂ) q₁ z).ker
            rw [(hq₁ z hz).2]
            exact hv) y hy
        obtain ⟨d,hd,hyd,g,hg⟩ := hNativeUAffine (cU i) (hcU i) x y (hdomU i hy)
        exact ⟨d,hd,hyd,g,hg.mono (fun z hz ↦ ⟨hz.1,hz.2.2⟩)⟩ }
    let A := orderedProjectiveProductAtlas_of_germData D
    exact ⟨⟨A, surface_projective_g3_local_product_chart_bridge_g7
      f a stable_rank unstable_rank A⟩⟩

end HolomorphicAnosov.Ghys


