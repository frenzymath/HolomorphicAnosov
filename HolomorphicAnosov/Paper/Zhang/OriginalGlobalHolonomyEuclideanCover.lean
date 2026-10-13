import HolomorphicAnosov.Topology.PointedUniversalCoverOfComplexCharts
import HolomorphicAnosov.Geometry.NativePartitionComplexStructure
import HolomorphicAnosov.Geometry.NativeReceivingBiholomorphs
import HolomorphicAnosov.Geometry.NativeGlobalHolonomyToIntrinsic
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseAnosovDatum
import HolomorphicAnosov.Paper.Ghys.CompleteGlobalHolonomyAffineCover

/-! Global unstable holonomy yields a Euclidean universal cover and a faithful complex translation
representation of the fundamental group. (Zhang, Prop. 2.9, p.10; Ghys, Thm B, p.598; Hatcher,
pp.63–65) -/

noncomputable section
open Set
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov
universe u
attribute [local instance] complex_isManifold_real

/-- Global unstable holonomy for a holomorphic Anosov system with a rank-one stable bundle gives a
pointed universal cover homeomorphic to real Euclidean space and an injective representation of
the fundamental group by complex translations. (Zhang, Prop. 2.9, p.10; Ghys, Thm B, p.598;
Hatcher, pp.63–65) -/
theorem original_global_holonomy_euclidean_cover
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (hholonomy : HasOriginalAnosovGlobalUnstableHolonomy a) (b : X) :
    let E := Σ x : X, Path.Homotopic.Quotient b x
    ∃ t : TopologicalSpace E, letI := t
      SimplyConnectedSpace E ∧ IsCoveringMap (fun e : E ↦ e.1) ∧
      Function.Surjective (fun e : E ↦ e.1) ∧
      ∃ (_e : E ≃ₜ (Fin (2 * d) → ℝ))
        (tau : FundamentalGroup X b →* Multiplicative ℂ), Function.Injective tau := by
  classical
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨B, ⟨G⟩⟩ := hholonomy
  obtain ⟨C, hC⟩ := native_partition_complex_structure B
  obtain ⟨W, hW⟩ := native_receiving_biholomorphs B C hC
  have hGlobal := native_global_holonomy_to_intrinsic B C W hW G
  let ai := TheoremAProof.inverseAnosovDatum f a
  have hrank : HasComplexRankOne ai.splitting.unstable.toDistribution := hstable
  have hAffine := Ghys.complete_global_holonomy_affine_cover.{u, u, u}
    f.symm ai hrank B C hC hGlobal
  let E := Σ x : X, Path.Homotopic.Quotient b x
  obtain ⟨t, ht⟩ := Proposition29Cover.pointed_universal_cover_of_complex_charts (d := d) b
  let : TopologicalSpace E := t
  obtain ⟨hSimply, hp, hsurj⟩ := ht
  let : SimplyConnectedSpace E := hSimply
  let p : E → X := fun e ↦ e.1
  let e0 : E := ⟨b, Path.Homotopic.Quotient.mk (Path.refl b)⟩
  obtain ⟨chartsE, smoothE, hProjection, D, z0, delta, tau,
    hProduct, hD, htau, hLift, hEquivariant, hFibres, hTrivial,
    hStableLift, hUnstableLift, ⟨e⟩, hComm, hTorsion⟩ := hAffine E p hp hsurj e0
  exact ⟨t, hSimply, hp, hsurj, e, tau, htau⟩

end HolomorphicAnosov
