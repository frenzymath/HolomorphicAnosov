import HolomorphicAnosov.Paper.Ghys.RankOneExpandingPlaqueComparisons
import HolomorphicAnosov.Paper.Ghys.NativeHolonomyComparisonLimit
import HolomorphicAnosov.Paper.Ghys.NativeHolonomyPresentation
import HolomorphicAnosov.Analysis.Complex.PositiveDerivativeConformalLimit
import HolomorphicAnosov.Geometry.NativeHolonomyChainHolomorphic


namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- A nonempty compact holomorphic Anosov system with complex unstable rank one admits a smooth
Hermitian tangent metric and a rank-one foliation presentation satisfying the expanding plaque
comparison estimates (Ghys, Prop. 2.2, p. 590). -/
theorem original_anosov_rank_one_comparisons
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (AD : AnosovDatum f)
    (hRank : HasComplexRankOne AD.splitting.unstable.toDistribution) :
    letI : MetricSpace M := rankComparisonMetric (d := d)
    Nonempty M → ∃ h : HermitianTangentMetricCore d M, IsSmoothHermitianTangentMetric h ∧
      HermitianAllTimeAnosov f h AD.splitting ∧
      ∃ L : RankOneNativeLeaves f AD.splitting, L.ComparisonProperty h := by
  let : MetricSpace M := rankComparisonMetric (d := d)
  intro hM
  obtain ⟨h, hh, C, rate, hC, hrate, hrate1, hs, hu⟩ :=
    native_unstable_hermitian_growth_exists f AD
  have hA : HermitianAllTimeAnosov f h AD.splitting := by
    refine ⟨C, rate⁻¹, hC, (one_lt_inv₀ hrate).mpr hrate1, ?_, ?_⟩
    · intro n hn x v hv
      have hsn := hs n x v hv
      have he : (realIterate (realModel d) f.toReal n : M → M) = (f : M → M)^[n] := rfl
      rw [he] at hsn
      simpa only [givenHermitianNorm, zpow_neg, zpow_natCast, inv_pow, inv_inv] using hsn
    · intro n hn x v hv
      have hun := hu n x v hv
      have he : (realIterate (realModel d) f.toReal.symm n : M → M) = (f.symm : M → M)^[n] := rfl
      rw [he] at hun
      simpa only [givenHermitianNorm, zpow_neg, zpow_natCast, inv_pow, inv_inv] using hun
  obtain ⟨L, hL⟩ := rank_one_expanding_plaque_comparisons f h hh AD.splitting hA hRank hM
  exact ⟨h, hh, hA, L, hL⟩

end HolomorphicAnosov.Ghys

/-! This file proves holomorphicity of stable holonomy between intrinsic unstable leaves when the
unstable distribution has complex rank one (Ghys, Prop. 2.2, pp. 589–590). -/

namespace HolomorphicAnosov.Ghys

open Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold

universe u v

set_option autoImplicit false

attribute [local instance] complex_isManifold_real

/-- For a holomorphic Anosov diffeomorphism of a compact complex manifold with complex unstable rank
one, every finite stable holonomy representative is holomorphic on its open source. (Ghys, Prop.
2.2, pp. 589–590 and pp. 594, 597–598; HPS, §7, pp. 115–116; Ahlfors, pp. 3–5, 24, 27–28;
Lyubich, §3.3, pp. 107–108; Lee, Prop. 11.20, pp. 278–279.) -/

theorem stable_holonomy_holomorphic
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (AD : AnosovDatum f)
    (hRank : HasComplexRankOne AD.splitting.unstable.toDistribution) :
    letI : MetrizableSpace M := Manifold.metrizableSpace (realModel d) M
    letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
    ∀ (s : ℕ) (A : NativeTransverseAsymptoticIdentification.{u, v}
      f.toHomeomorph AD.splitting.stable.toDistribution AD.splitting.unstable.toDistribution s 2),
    letI := A.realAmbientCharts
    ∀ q : Quotient A.F.stablePartition,
    letI := A.F.stableTopology q
    ∀ (x y : IntrinsicFoliationLeaf A.F.stablePartition q) (γ : Path x y)
      (a b : unitInterval) (e : PathHolonomyRepresentative A.F γ a b),
    letI := A.unstableTopology (γ a).val
    letI := A.unstableCharts (γ a).val
    letI := (A.complexU1 (γ a).val).charts
    letI := A.unstableTopology (γ b).val
    letI := A.unstableCharts (γ b).val
    letI := (A.complexU1 (γ b).val).charts
    let h := A.transportUnstableLocalMap (γ a).val (γ b).val e.map
    ContMDiffOn (complexModel 1) (complexModel 1) ∞ h h.source := by
  let : MetrizableSpace M := Manifold.metrizableSpace (realModel d) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  intro s A
  let := A.realAmbientCharts
  intro q
  let := A.F.stableTopology q
  intro x y γ a b e
  have hM : Nonempty M := ⟨x.val⟩
  obtain ⟨H, hH, hAn, L, hL⟩ := original_anosov_rank_one_comparisons f AD hRank hM
  have hcenter : CenteredNativeHolonomyHolomorphic L.identification := by
    exact native_actual_representative_holomorphic_at
      asymptotically_conformal_limit_of_positive_derivatives L H hH hAn hL
  have hcenterA := centered_native_holonomy_transfer A L.identification hcenter
  exact native_holonomy_chain_holomorphic A (native_full_plaque_holomorphic A hcenterA)
    q x y γ a b e.map e.chain

end HolomorphicAnosov.Ghys
