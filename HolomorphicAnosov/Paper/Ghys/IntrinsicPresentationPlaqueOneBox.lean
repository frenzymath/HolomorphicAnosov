import HolomorphicAnosov.Geometry.ComplexHolomorphicImmersionOfInjectiveDerivative
import HolomorphicAnosov.Geometry.ComplexDerivativeInjectiveOfRealCharts
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Ghys.AffineSchwarzianQuadraticForm
import HolomorphicAnosov.Geometry.RealImmersionOfPointwiseIntoComplexModelG1
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.original_real_tangent_finrank
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf
import HolomorphicAnosov.Geometry.ContinuousComplexRankOneSubbundle
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgradeOfComplexTangent
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.LocalPlaquePathRealizationG6
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Geometry.Manifold.Metrizable
/-! This module transports Ghys’s one-box stable holonomy proposition to an intrinsic foliation presentation. (Ghys, Prop. 2.2) -/
noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u v
namespace Ghys
attribute [local instance] complex_isManifold_real

def rechartFoliations {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [C : ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    (C' : ChartedSpace (Fin (s+t) → ℝ) M) :
    letI := C'; TransverseContinuousFoliations.{u,u} s t M :=
  letI := C'
  {
    boxIndex := (letI := C; F.boxIndex)
    box := (letI := C; F.box)
    cover := (letI := C; F.cover)
    stablePartition := (letI := C; F.stablePartition)
    unstablePartition := (letI := C; F.unstablePartition)
    stable_generated := (letI := C; F.stable_generated)
    unstable_generated := (letI := C; F.unstable_generated)
    stableTopology := (letI := C; F.stableTopology)
    unstableTopology := (letI := C; F.unstableTopology)
    stableCharts := (letI := C; F.stableCharts)
    unstableCharts := (letI := C; F.unstableCharts)
    stable_connected := (letI := C; F.stable_connected)
    unstable_connected := (letI := C; F.unstable_connected)
    stable_inclusion := (letI := C; F.stable_inclusion)
    unstable_inclusion := (letI := C; F.unstable_inclusion)
    stableLabel := (letI := C; F.stableLabel)
    unstableLabel := (letI := C; F.unstableLabel)
    stable_label := (letI := C; F.stable_label)
    unstable_label := (letI := C; F.unstable_label)
    stable_plaque := (letI := C; F.stable_plaque)
    unstable_plaque := (letI := C; F.unstable_plaque)
    stable_topology_generated := (letI := C; F.stable_topology_generated)
    unstable_topology_generated := (letI := C; F.unstable_topology_generated)
  }

theorem intrinsicPresentation_one_box_plaque_holomorphic
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a)
:
    letI := P.realCharts
    ∀ (x y : M) (e : LocalPlaqueTransport P.foliations x y),
      letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
      letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition y)
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.map e.map.source := by
  classical
  let := P.realCharts
  intro x y e
  let : Nonempty M := ⟨x⟩
  let : MetrizableSpace M := Manifold.metrizableSpace (realModel d) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hu : P.metric.toUniformSpace = (inferInstance : MetricSpace M).toUniformSpace :=
    unique_uniformity_of_compact P.metric_topology rfl
  have hrel (g : M → M) (x y : M) :
      @ForwardAsymptotic M P.metric g x y ↔ ForwardAsymptotic g x y := by
    have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ P.metric.toPseudoMetricSpace
      (fun n ↦ ((g^[n]) y, (g^[n]) x)) atTop
    have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ
      (inferInstance : MetricSpace M).toPseudoMetricSpace
      (fun n ↦ ((g^[n]) y, (g^[n]) x)) atTop
    unfold ForwardAsymptotic
    rw [← h₁, ← h₂]
    change Tendsto _ _ P.metric.toUniformSpace.uniformity ↔
      Tendsto _ _ (inferInstance : MetricSpace M).toUniformSpace.uniformity
    rw [hu]
  have htwo := TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank x
  have hbound := (a.splitting.unstable.toDistribution x).finrank_le
  rw [htwo, TheoremAProof.Dimension.original_real_tangent_finrank x] at hbound
  have hdim : (2*d-2)+2 = 2*d := by omega
  let B : ComplexModel d ≃L[ℝ] (Fin ((2*d-2)+2) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [ComplexModel, finrank_real_of_complex, hdim])
  let F := rechartFoliations P.foliations (realCoordinateRechart (M := M) B)
  have hNativeS (w : M) :
      ∃ N : NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph
          a.splitting.stable.toDistribution w,
        N.rank = 2 * d - 2 ∧
          (letI := N.topology; letI := N.charts
           letI := P.foliations.stableTopology (Quotient.mk P.foliations.stablePartition w)
           letI := P.foliations.stableCharts (Quotient.mk P.foliations.stablePartition w)
           ∃ e : Diffeomorph 𝓘(ℝ, Fin (2 * d - 2) → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
              (IntrinsicFoliationLeaf P.foliations.stablePartition (Quotient.mk P.foliations.stablePartition w))
              (StableAsymptoticLeaf f.toHomeomorph w) ∞,
             ∀ z, (e z).val = z.val) := by
    let q := Quotient.mk P.foliations.stablePartition w
    let := P.foliations.stableTopology q
    let := P.foliations.stableCharts q
    let := P.stableSmooth q
    let N := P.stableNative q
    have heq := P.stable_inclusion_eq q
    have hrange : Set.range N.inclusion =
        {z | ForwardAsymptotic f.toHomeomorph w z} := by
      rw [heq]
      ext z
      constructor
      · rintro ⟨v, rfl⟩
        exact ((P.stable_asymptotic w v.val).trans (hrel f w v.val)).mp (Quotient.exact v.property.symm)
      · intro hz
        exact ⟨⟨z, (Quotient.sound (((P.stable_asymptotic w z).trans (hrel f w z)).mpr hz)).symm⟩, rfl⟩
    obtain ⟨N', hN, e, he⟩ := native_asymptotic_datum_of_leaf_g15
      a.splitting.stable.toDistribution N f.toHomeomorph w hrange
    refine ⟨N', hN, e, ?_⟩
    intro z
    exact (he z).trans (congrFun heq z)
  have hNativeU (w : M) :
      ∃ N : NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph.symm
          a.splitting.unstable.toDistribution w,
        N.rank = 2 ∧
          (letI := N.topology; letI := N.charts
           letI := P.foliations.unstableTopology (Quotient.mk P.foliations.unstablePartition w)
           letI := P.foliations.unstableCharts (Quotient.mk P.foliations.unstablePartition w)
           ∃ e : Diffeomorph 𝓘(ℝ, Fin (2) → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
              (IntrinsicFoliationLeaf P.foliations.unstablePartition (Quotient.mk P.foliations.unstablePartition w))
              (StableAsymptoticLeaf f.toHomeomorph.symm w) ∞,
             ∀ z, (e z).val = z.val) := by
    let q := Quotient.mk P.foliations.unstablePartition w
    let := P.foliations.unstableTopology q
    let := P.foliations.unstableCharts q
    let := P.unstableSmooth q
    let N := P.unstableNative q
    have heq := P.unstable_inclusion_eq q
    have hrange : Set.range N.inclusion =
        {z | ForwardAsymptotic f.toHomeomorph.symm w z} := by
      rw [heq]
      ext z
      constructor
      · rintro ⟨v, rfl⟩
        exact ((P.unstable_asymptotic w v.val).trans (hrel f.symm w v.val)).mp (Quotient.exact v.property.symm)
      · intro hz
        exact ⟨⟨z, (Quotient.sound (((P.unstable_asymptotic w z).trans (hrel f.symm w z)).mpr hz)).symm⟩, rfl⟩
    obtain ⟨N', hN, e, he⟩ := native_asymptotic_datum_of_leaf_g15
      a.splitting.unstable.toDistribution N f.toHomeomorph.symm w hrange
    refine ⟨N', hN, e, ?_⟩
    intro z
    exact (he z).trans (congrFun heq z)
  choose Ns hNs eS heS using hNativeS
  choose Nu hNu eU heU using hNativeU
  obtain ⟨S, T, hT, _, hreal⟩ :=
    exists_continuous_complex_rank_one_subbundle a.splitting.unstable hRank
  have hUpgrade (w : M)
      (N : NativeUnstableAsymptoticLeafDatum (realModel d) f.toHomeomorph
        a.splitting.unstable.toDistribution w) (hr : N.rank = 2) :
      letI := N.topology
      letI := N.charts
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := N.rank) 1
        (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph w → M)) := by
    rcases N with ⟨r, top, charts, haus, second, conn, smooth, hsmooth, himm, ht⟩
    change r = 2 at hr
    subst r
    let := top
    let := charts
    let := smooth
    apply nativeLeafComplexUpgrade_of_complex_tangent (k := 1)
      Subtype.val a.splitting.unstable
      (real_immersion_of_pointwise_into_complex_model_g1 himm) ht T
    intro z
    rw [ht, hT]
    exact hreal z.val
  let A : NativeTransverseAsymptoticIdentification f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution (2*d-2) 2 :=
    { realCoordinates := B
      F := F
      nativeS := Ns
      nativeU := Nu
      rankS := hNs
      rankU := hNu
      complexU1 := fun x ↦ Classical.choice (hUpgrade x (Nu x) (hNu x))
      stableIdentification := eS
      stable_points := heS
      unstableIdentification := eU
      unstable_points := heU }
  have hbi (w : M) :
      letI := P.foliations.unstableTopology (Quotient.mk P.foliations.unstablePartition w)
      letI := P.foliations.unstableCharts (Quotient.mk P.foliations.unstablePartition w)
      letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition w)
      letI := A.unstableTopology w
      letI := A.unstableCharts w
      letI := (A.complexU1 w).charts
      ContMDiff (complexModel 1) (complexModel 1) ∞ (eU w) ∧
        ContMDiff (complexModel 1) (complexModel 1) ∞ (eU w).symm := by
    let q := Quotient.mk P.foliations.unstablePartition w
    let := P.foliations.unstableTopology q
    let := P.foliations.unstableCharts q
    let := P.unstableSmooth q
    let := P.complexLeaves.charts q
    let := P.complexLeaves.complex_manifold q
    let := A.unstableTopology w
    let := (A.nativeU w).charts
    let := (A.complexU1 w).charts
    let := (A.complexU1 w).complex_manifold
    constructor
    · intro z
      apply (ContMDiffAt.iff_comp_isImmersionAt
        ((A.complexU1 w).inclusion_immersion (eU w z))).mpr
      refine ⟨(eU w).continuous.continuousAt, ?_⟩
      have heq : Subtype.val ∘ eU w = (Subtype.val : P.foliations.ULeaf w → M) :=
        funext (heU w)
      rw [heq]
      exact P.unstable_holomorphic q z
    · intro z
      have hderiv : Function.Injective (mfderiv (complexModel 1) (complexModel d)
          (Subtype.val : P.foliations.ULeaf w → M) ((eU w).symm z)) := by
        apply complexDerivative_injective_of_compatible_real_charts (r := 2)
        · exact ((P.unstable_real_complex_compatible q).1 _).mdifferentiableAt (by simp)
        · exact ((P.unstable_real_complex_compatible q).2 _).mdifferentiableAt (by simp)
        · exact (P.unstable_holomorphic q _).mdifferentiableAt (by simp)
        · rw [← P.unstable_inclusion_eq q]
          exact (P.unstableNative q).immersion.mfderiv_injective (by simp) _
      have himm := complex_holomorphic_immersion_of_injective_derivative
        ((P.unstable_holomorphic q).contMDiffAt (x := (eU w).symm z)) hderiv
      apply (ContMDiffAt.iff_comp_isImmersionAt himm).mpr
      refine ⟨(eU w).symm.continuous.continuousAt, ?_⟩
      have heq : (Subtype.val : P.foliations.ULeaf w → M) ∘ (eU w).symm =
          (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph w → M) := by
        funext z
        have hz := heU w ((eU w).symm z)
        simpa using hz.symm
      rw [heq]
      exact (A.complexU1 w).inclusion_holomorphic z
  let := A.realAmbientCharts
  let (w : M) : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph w) :=
    A.unstableTopology w
  let (w : M) : ChartedSpace (Fin (A.nativeU w).rank → ℝ)
      (UnstableAsymptoticLeaf f.toHomeomorph w) := A.unstableCharts w
  let (w : M) : ChartedSpace (ComplexModel 1)
      (UnstableAsymptoticLeaf f.toHomeomorph w) := (A.complexU1 w).charts
  let e' : LocalPlaqueTransport A.F x y :=
    { e with }
  have hn : let h := A.transportUnstableLocalMap x y e'.map
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ h h.source := by
    apply localPlaqueTransport_of_path_property A.F
      (fun x y h ↦ let h' := A.transportUnstableLocalMap x y h
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ h' h'.source)
      (stable_holonomy_holomorphic f a hRank (2*d-2) A) x y e'
  let := P.realCharts
  let := P.foliations.unstableCharts (Quotient.mk P.foliations.unstablePartition x)
  let := P.foliations.unstableCharts (Quotient.mk P.foliations.unstablePartition y)
  let := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  let := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition y)
  have hc := ((hbi y).2.contMDiffOn (s := Set.univ)).comp'
    (hn.comp' ((hbi x).1.contMDiffOn (s := e.map.source)))
  simp only [Set.preimage_univ, Set.inter_univ] at hc
  have hset : e.map.source ∩ (eU x) ⁻¹'
      (letI := A.realAmbientCharts; (A.transportUnstableLocalMap x y e'.map).source) =
      e.map.source := by
    ext z
    change (z ∈ e.map.source ∧
      ((True ∧ (eU x).symm (eU x z) ∈ e.map.source) ∧ True)) ↔ z ∈ e.map.source
    simp only [Diffeomorph.symm_apply_apply, true_and, and_true, and_self]
  rw [hset] at hc
  change ContMDiffOn (complexModel 1) (complexModel 1) ∞
    (fun z ↦ (eU y).symm (eU y (e.map ((eU x).symm (eU x z))))) e.map.source at hc
  simpa only [Diffeomorph.symm_apply_apply] using hc

/-- This wrapper transports the one-box stable holonomy result to the supplied intrinsic foliation presentation. (Ghys, Prop. 2.2) -/
theorem intrinsicPresentation_plaque_holomorphic
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    ∀ (x y : M) (e : LocalPlaqueTransport P.foliations x y),
      letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
      letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition y)
      IsHolomorphicCurveLocalMap e.map := by
  let := P.realCharts
  intro x y e
  have hforward := intrinsicPresentation_one_box_plaque_holomorphic f a hRank P x y e
  refine ⟨hforward, ?_⟩
  obtain ⟨r, hrmap⟩ : ∃ r : LocalPlaqueTransport P.foliations y x,
      r.map = e.map.symm := by
    refine ⟨{ map := e.map.symm
              source_point := ?_
              map_point := ?_
              box := e.box
              first := e.second
              second := e.first
              transverse := e.transverse
              first_point := e.second_point
              second_point := e.first_point
              source_in_plaque := ?_
              coordinate_map := ?_ }, rfl⟩
    · rw [← e.map_point]
      exact e.map.map_source e.source_point
    · rw [← e.map_point]
      exact e.map.left_inv e.source_point
    · intro z hz
      obtain ⟨w, hw⟩ := e.source_in_plaque (e.map.symm z) (e.map.map_target hz)
      refine ⟨w, ?_⟩
      have h := e.coordinate_map (e.map.symm z) w (e.map.map_target hz) hw
      simpa only [e.map.right_inv hz] using h.symm
    · intro z w hz hw
      obtain ⟨v, hv⟩ := e.source_in_plaque (e.map.symm z) (e.map.map_target hz)
      have h := e.coordinate_map (e.map.symm z) v (e.map.map_target hz) hv
      have heq : (P.foliations.box e.box).chart (e.second, v) =
          (P.foliations.box e.box).chart (e.second, w) := by
        apply Subtype.ext
        exact h.symm.trans ((congrArg Subtype.val (e.map.right_inv hz)).trans hw.symm)
      have hvw : v = w := congrArg Prod.snd ((P.foliations.box e.box).chart.injective heq)
      exact hv.symm.trans (congrArg (fun v ↦ ((P.foliations.box e.box).chart (e.first, v)).val) hvw)
  have hinverse := intrinsicPresentation_one_box_plaque_holomorphic f a hRank P y x r
  rw [hrmap] at hinverse
  exact hinverse

end Ghys
end HolomorphicAnosov
