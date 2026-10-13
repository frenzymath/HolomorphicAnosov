import HolomorphicAnosov.Paper.Ghys.NativeTransverseCoordinateScalar
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseAnosovDatum

/-! This module constructs stable transverse scalar coordinates using inverse dynamics. (Ghys, Prop. 2.2) -/

noncomputable section
set_option linter.style.haveILetI false

namespace HolomorphicAnosov.Ghys
universe u
open scoped Manifold ContDiff _root_.Topology
attribute [local instance] complex_isManifold_real
/-- This module scalarizes stable transverse coordinates using inverse dynamics. (Ghys, Prop. 2.2) -/
theorem inverse_native_transverse_coordinate_scalar_kernel
    {d s : ℕ} {M : Type u} [mOriginal : MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (hd : 2 ≤ d) (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.stable.toDistribution)
    (B : NativeTransverseAsymptoticIdentification.{u,u} f.symm.toHomeomorph
      a.splitting.unstable.toDistribution a.splitting.stable.toDistribution s 2)
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (hC : letI := B.realAmbientCharts
      ∀ q : Quotient B.F.unstablePartition,
        letI := B.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) z) :
    letI := B.realAmbientCharts
    ∀ (c : TransverseProjectiveChart B.F C) (x : M), x ∈ c.domain B.F C →
    ∃ (k : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
      (q : M → ℂ) (N : TopologicalSpace.Opens M),
      x ∈ N ∧ (N : Set M) ⊆ c.domain B.F C ∧
      ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source ∧
      ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q N ∧
      (∀ y ∈ N, q y ∈ k.target ∧ k.symm (q y) = c.transverseCoordinate B.F C y) ∧
      ∀ y ∈ N, mfderiv (complexModel d) 𝓘(ℂ) q y ≠ 0 ∧
        ((LinearMap.ker (mfderiv (complexModel d) 𝓘(ℂ) q y).toLinearMap).restrictScalars ℝ).map
          (complexTangentToReal d y).toLinearEquiv.toLinearMap =
            a.splitting.unstable.toDistribution y := by
  exact native_transverse_coordinate_scalar_kernel hd f.symm
    (TheoremAProof.inverseAnosovDatum f a) hRank B C hC

/-- Every stable transverse atlas chart admits a local scalarization preserving its projective values and unstable kernel. (Ghys, Prop. 2.2) -/
theorem inverse_native_atlas_scalar_cover
    {d s : ℕ} {M : Type u} [mOriginal : MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (hd : 2 ≤ d) (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.stable.toDistribution)
    (B : NativeTransverseAsymptoticIdentification.{u,u} f.symm.toHomeomorph
      a.splitting.unstable.toDistribution a.splitting.stable.toDistribution s 2)
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (hC : letI := B.realAmbientCharts
      ∀ q : Quotient B.F.unstablePartition,
        letI := B.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) z) :
    letI := B.realAmbientCharts
    ∀ (atlasS : TransverseProjectiveAtlas B.F C) (x : M),
    ∃ c ∈ atlasS.charts, x ∈ c.domain B.F C ∧
    ∃ (k : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
      (q : M → ℂ) (N : TopologicalSpace.Opens M),
      x ∈ N ∧ (N : Set M) ⊆ c.domain B.F C ∧
      ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source ∧
      ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q N ∧
      (∀ y ∈ N, q y ∈ k.target ∧ k.symm (q y) = c.transverseCoordinate B.F C y) ∧
      ∀ y ∈ N, mfderiv (complexModel d) 𝓘(ℂ) q y ≠ 0 ∧
        ((LinearMap.ker (mfderiv (complexModel d) 𝓘(ℂ) q y).toLinearMap).restrictScalars ℝ).map
          (complexTangentToReal d y).toLinearEquiv.toLinearMap =
            a.splitting.unstable.toDistribution y := by
  letI := B.realAmbientCharts
  intro atlasS x
  obtain ⟨c, hc, hx⟩ := atlasS.cover x
  exact ⟨c, hc, hx, inverse_native_transverse_coordinate_scalar_kernel
    hd f a hRank B C hC c x hx⟩
end HolomorphicAnosov.Ghys
