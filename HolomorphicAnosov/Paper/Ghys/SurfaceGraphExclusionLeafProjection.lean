import HolomorphicAnosov.Geometry.SpecifiedNativeLiftRangeEqIntrinsic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeMetric
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.TensorBounds
import HolomorphicAnosov.Geometry.NativeCompatibleMetric
import HolomorphicAnosov.Geometry.IntrinsicPullbackProjectionCovering
import HolomorphicAnosov.Geometry.CoveringPathComponent
import HolomorphicAnosov.Geometry.IntrinsicCoveringLeafProjectionPointwise
import HolomorphicAnosov.Geometry.IntrinsicCoveringLeafInclusionRange
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Metrizable.Uniformity

/-!
Intrinsic stable and unstable asymptotic leaf families and locally homeomorphic
projections from their lifted leaves through a universal covering.
(HPS, §§6B–7, pp. 114–116; Bredon, I Prop. 4.5, pp. 10–11, II §14, pp. 111–112;
Nisoli, Defs. 1.1.2–1.1.3, p. 10; Hatcher, pp. 60–62)
-/

noncomputable section

open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Ghys

universe u v w

set_option autoImplicit false

attribute [local instance] complex_isManifold_real

/-- A compact holomorphic Anosov manifold has intrinsic stable and unstable asymptotic leaf
families whose lifted leaves in any universal cover project locally homeomorphically to
the base leaves. Each lifted leaf has an injective inclusion with range equal to the
intrinsic lifted leaf range, and its projection is the unique map commuting with the
inclusions and the covering map.
(HPS, §§6B–7, pp. 114–116, Thm 3.1, p. 25; Bredon, I Prop. 4.5, pp. 10–11,
II §14, pp. 111–112; Nisoli, Defs. 1.1.2–1.1.3, p. 10; Hatcher, Algebraic Topology,
pp. 60–62, Vector Bundles and K-Theory, p. 6, Lemma 1.1, p. 8, Prop. 1.3, pp. 12–13;
Gallier–Quaintance, Prop. 18.5, pp. 534–535; Lee, Lemma 6.17, pp. 139–140, pp. 275–279) -/
theorem surface_graph_exclusion_leaf_projection
    {d : ℕ} {S : Type u} [TopologicalSpace S]
    [ChartedSpace (ComplexModel d) S] [IsCompactComplexManifold d S]
    (f : Biholomorph d d S S) (a : AnosovDatum f) :
    letI : TopologicalSpace.MetrizableSpace S := Manifold.metrizableSpace (realModel d) S
    letI : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
    ∃ (Ns : ∀ y : S, NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph
        a.splitting.stable.toDistribution y)
      (Nu : ∀ y : S, NativeUnstableAsymptoticLeafDatum (realModel d) f.toHomeomorph
        a.splitting.unstable.toDistribution y),
    ∀ (X : Type v) [TopologicalSpace X] [SimplyConnectedSpace X]
      (π : X → S), IsCoveringMap π →
      (∀ x : X,
        letI := (Ns (π x)).topology
        ∃ (b : StableAsymptoticLeaf f.toHomeomorph (π x)) (hb : b.val = π x),
        let L := IntrinsicCoveringPullbackLeaf
          (Subtype.val : StableAsymptoticLeaf f.toHomeomorph (π x) → S) π b x hb
        let q := intrinsicCoveringLeafProjection
          (Subtype.val : StableAsymptoticLeaf f.toHomeomorph (π x) → S) π b x hb
        let ℓ := intrinsicCoveringLeafInclusion
          (Subtype.val : StableAsymptoticLeaf f.toHomeomorph (π x) → S) π b x hb
        Continuous q ∧ IsLocalHomeomorph q ∧ Function.Injective ℓ ∧
        Set.range ℓ = liftedIntrinsicLeafRange π
          (Subtype.val : StableAsymptoticLeaf f.toHomeomorph (π x) → S) b x ∧
        (∀ z : L, (q z).val = π (ℓ z)) ∧
        (∀ r : L → StableAsymptoticLeaf f.toHomeomorph (π x),
          (∀ z, (r z).val = π (ℓ z)) → r = q)) ∧
      (∀ x : X,
        letI := (Nu (π x)).topology
        ∃ (b : UnstableAsymptoticLeaf f.toHomeomorph (π x)) (hb : b.val = π x),
        let L := IntrinsicCoveringPullbackLeaf
          (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph (π x) → S) π b x hb
        let q := intrinsicCoveringLeafProjection
          (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph (π x) → S) π b x hb
        let ℓ := intrinsicCoveringLeafInclusion
          (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph (π x) → S) π b x hb
        Continuous q ∧ IsLocalHomeomorph q ∧ Function.Injective ℓ ∧
        Set.range ℓ = liftedIntrinsicLeafRange π
          (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph (π x) → S) b x ∧
        (∀ z : L, (q z).val = π (ℓ z)) ∧
        (∀ r : L → UnstableAsymptoticLeaf f.toHomeomorph (π x),
          (∀ z, (r z).val = π (ℓ z)) → r = q)) := by
  classical
  let : TopologicalSpace.MetrizableSpace S := Manifold.metrizableSpace (realModel d) S
  let m₀ : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  obtain ⟨b, _⟩ := covering_conjugacy_tensor_bounds_g15 f a
  obtain ⟨m, hm, ⟨N⟩⟩ := covering_conjugacy_native_metric_g15 f a b
  let : MetricSpace S := m₀
  let Ns := fun y : S ↦ (nativeAsymptoticLeafDatum_compatibleMetric
    (E := ComplexModel d) ⟨m, hm⟩ f.toHomeomorph
      a.splitting.stable.toDistribution y (N false y)).some
  let Nu := fun y : S ↦ (nativeAsymptoticLeafDatum_compatibleMetric
    (E := ComplexModel d) ⟨m, hm⟩ f.toHomeomorph.symm
      a.splitting.unstable.toDistribution y (N true y)).some
  refine ⟨Ns, Nu, ?_⟩
  intro X _ _ π hπ
  constructor
  all_goals
    intro x
  · let D := Ns (π x)
    let : TopologicalSpace (StableAsymptoticLeaf f.toHomeomorph (π x)) := D.topology
    let : ChartedSpace (Fin D.rank → ℝ)
      (StableAsymptoticLeaf f.toHomeomorph (π x)) := D.charts
    have : LocallyPathConnectedSpace (StableAsymptoticLeaf f.toHomeomorph (π x)) :=
      ChartedSpace.locallyPathConnectedSpace (Fin D.rank → ℝ) _
    let b : StableAsymptoticLeaf f.toHomeomorph (π x) :=
      ⟨π x, by simp [ForwardAsymptotic]⟩
    refine ⟨b, rfl, ?_⟩
    obtain ⟨hc, hi, he, hu⟩ := intrinsicCoveringLeafProjection_pointwise
      Subtype.val π b x rfl Subtype.val_injective
    refine ⟨hc, ?_, hi, intrinsicCoveringLeafInclusion_range _ _ _ _ _, he, hu⟩
    exact (isCoveringMap_pathComponent_restrict _
      (intrinsicPullbackProjection_isCoveringMap _ π D.inclusion_smooth.continuous hπ)
      (intrinsicCoveringPullbackPoint Subtype.val π b x rfl)).isLocalHomeomorph
  · let D := Nu (π x)
    let : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph (π x)) := D.topology
    let : ChartedSpace (Fin D.rank → ℝ)
      (UnstableAsymptoticLeaf f.toHomeomorph (π x)) := D.charts
    have : LocallyPathConnectedSpace (UnstableAsymptoticLeaf f.toHomeomorph (π x)) :=
      ChartedSpace.locallyPathConnectedSpace (Fin D.rank → ℝ) _
    let b : UnstableAsymptoticLeaf f.toHomeomorph (π x) :=
      ⟨π x, by simp [ForwardAsymptotic]⟩
    refine ⟨b, rfl, ?_⟩
    obtain ⟨hc, hi, he, hu⟩ := intrinsicCoveringLeafProjection_pointwise
      Subtype.val π b x rfl Subtype.val_injective
    refine ⟨hc, ?_, hi, intrinsicCoveringLeafInclusion_range _ _ _ _ _, he, hu⟩
    exact (isCoveringMap_pathComponent_restrict _
      (intrinsicPullbackProjection_isCoveringMap _ π D.inclusion_smooth.continuous hπ)
      (intrinsicCoveringPullbackPoint Subtype.val π b x rfl)).isLocalHomeomorph

end HolomorphicAnosov.Ghys
