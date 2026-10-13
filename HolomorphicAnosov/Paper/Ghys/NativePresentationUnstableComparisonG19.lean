import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.CarrierSmoothTransport
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.CarrierTangentImage
import HolomorphicAnosov.Geometry.ContinuousStableLeafLiftG9
import HolomorphicAnosov.Geometry.ContinuousUnstableLeafLiftG1
import HolomorphicAnosov.Geometry.ComplexDerivativeInjectiveOfRealCharts
import HolomorphicAnosov.Geometry.ComplexHolomorphicImmersionOfInjectiveDerivative
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Geometry.NativeIdentificationPartitionAsymptotic
import Mathlib.Topology.UniformSpace.Compact
import HolomorphicAnosov.Ghys.AffineProjectiveStructure

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real
universe u

/-- The unstable partition carriers of two native presentations are point-preservingly biholomorphic. (HPS, §7; Ghys, §2) -/
theorem native_presentation_unstable_comparison
    {d s : ℕ} {M : Type u} [m : MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    (A : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z) :
    letI := P.realCharts
    letI := A.realAmbientCharts
    ∀ x : M,
      letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      ∃ E : Biholomorph 1 1 (P.foliations.ULeaf x) (A.F.ULeaf x),
        ∀ z, (E z).val = z.val := by
  classical
  let := P.realCharts
  let := A.realAmbientCharts
  have hu : P.metric.toUniformSpace = m.toUniformSpace :=
    unique_uniformity_of_compact P.metric_topology rfl
  have hrel (x y : M) : P.foliations.unstablePartition x y ↔
      A.F.unstablePartition x y := by
    rw [P.unstable_asymptotic,
      native_identification_unstable_partition_iff_asymptotic A]
    have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ P.metric.toPseudoMetricSpace
      (fun n ↦ (((f.symm : M → M)^[n]) y, ((f.symm : M → M)^[n]) x)) atTop
    have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m.toPseudoMetricSpace
      (fun n ↦ (((f.symm : M → M)^[n]) y, ((f.symm : M → M)^[n]) x)) atTop
    change @ForwardAsymptotic M P.metric (f.symm : M → M) x y ↔
      @ForwardAsymptotic M m (f.symm : M → M) x y
    unfold ForwardAsymptotic
    rw [← h₁, ← h₂]
    change Tendsto _ _ P.metric.toUniformSpace.uniformity ↔
      Tendsto _ _ m.toUniformSpace.uniformity
    rw [hu]
  intro x
  let q := Quotient.mk P.foliations.unstablePartition x
  let q' := Quotient.mk A.F.unstablePartition x
  let := P.foliations.unstableTopology q
  let := P.foliations.unstableCharts q
  let := P.unstableSmooth q
  let := P.complexLeaves.charts q
  let := P.complexLeaves.complex_manifold q
  let := (P.unstableNative q).countable
  let := A.F.unstableTopology q'
  let := C.charts q'
  let := C.complex_manifold q'
  have hcount : SecondCountableTopology (A.F.ULeaf x) := by
    let := A.unstableTopology x
    let := (A.nativeU x).secondCountable
    exact (A.unstableClassHomeomorph x).secondCountableTopology
  let := hcount
  let : LocallyConnectedSpace (P.foliations.ULeaf x) :=
    ChartedSpace.locallyConnectedSpace (ComplexModel 1) _
  let : LocallyConnectedSpace (A.F.ULeaf x) :=
    ChartedSpace.locallyConnectedSpace (ComplexModel 1) _
  let e : P.foliations.ULeaf x ≃ A.F.ULeaf x :=
    Equiv.subtypeEquiv (Equiv.refl M) (fun y ↦ by
      change Quotient.mk _ y = Quotient.mk _ x ↔ Quotient.mk _ y = Quotient.mk _ x
      rw [Quotient.eq, Quotient.eq]
      exact hrel y x)
  have hc : Continuous e := continuous_unstable_leaf_lift_g1 A.F q' inferInstance e
    (P.foliations.unstable_inclusion q)
  have hi : Continuous e.symm := continuous_unstable_leaf_lift_g1 P.foliations q
    inferInstance e.symm (A.F.unstable_inclusion q')
  have hs : ContMDiff (complexModel 1) (complexModel 1) ∞ e := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt ((hC q').2 (e z))).mpr
    exact ⟨hc.continuousAt, P.unstable_holomorphic q z⟩
  have hs' : ContMDiff (complexModel 1) (complexModel 1) ∞ e.symm := by
    intro z
    have hderiv : Function.Injective (mfderiv (complexModel 1) (complexModel d)
        (Subtype.val : P.foliations.ULeaf x → M) (e.symm z)) := by
      apply complexDerivative_injective_of_compatible_real_charts (r := 2)
      · exact ((P.unstable_real_complex_compatible q).1 (e.symm z)).mdifferentiableAt (by simp)
      · exact ((P.unstable_real_complex_compatible q).2 (e.symm z)).mdifferentiableAt (by simp)
      · exact (P.unstable_holomorphic q (e.symm z)).mdifferentiableAt (by simp)
      · rw [← P.unstable_inclusion_eq q]
        exact (P.unstableNative q).immersion.mfderiv_injective (by simp) (e.symm z)
    have himm := complex_holomorphic_immersion_of_injective_derivative
      ((P.unstable_holomorphic q).contMDiffAt (x := e.symm z)) hderiv
    exact (ContMDiffAt.iff_comp_isImmersionAt himm).mpr ⟨hi.continuousAt, (hC q').1 z⟩
  exact ⟨{e with contMDiff_toFun := hs, contMDiff_invFun := hs'}, fun _ ↦ rfl⟩

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real
/-- The corresponding stable carriers have the same intrinsic topology under the point identification. (HPS, §7) -/
theorem native_presentation_stable_comparison
    {d s : ℕ} {M : Type u} [m : MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    (A : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution s 2) :
    letI := P.realCharts
    letI := A.realAmbientCharts
    ∀ x : M,
      letI := P.foliations.stableTopology (Quotient.mk P.foliations.stablePartition x)
      letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
      ∃ E : IntrinsicFoliationLeaf P.foliations.stablePartition
          (Quotient.mk P.foliations.stablePartition x) ≃ₜ
          IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x),
        ∀ z, (E z).val = z.val := by
  classical
  let := P.realCharts
  let := A.realAmbientCharts
  have hu : P.metric.toUniformSpace = m.toUniformSpace :=
    unique_uniformity_of_compact P.metric_topology rfl
  have hrel (x y : M) : P.foliations.stablePartition x y ↔
      A.F.stablePartition x y := by
    rw [P.stable_asymptotic,
      native_identification_stable_partition_iff_asymptotic A]
    change @ForwardAsymptotic M P.metric (f : M → M) x y ↔
      @ForwardAsymptotic M m (f : M → M) x y
    have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ P.metric.toPseudoMetricSpace
      (fun n ↦ (((f : M → M)^[n]) y, ((f : M → M)^[n]) x)) atTop
    have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m.toPseudoMetricSpace
      (fun n ↦ (((f : M → M)^[n]) y, ((f : M → M)^[n]) x)) atTop
    unfold ForwardAsymptotic
    rw [← h₁, ← h₂]
    change Tendsto _ _ P.metric.toUniformSpace.uniformity ↔
      Tendsto _ _ m.toUniformSpace.uniformity
    rw [hu]
  intro x
  let q := Quotient.mk P.foliations.stablePartition x
  let q' := Quotient.mk A.F.stablePartition x
  let := P.foliations.stableTopology q
  let := P.foliations.stableCharts q
  let := P.stableSmooth q
  let := (P.stableNative q).countable
  let := A.F.stableTopology q'
  let := A.F.stableCharts q'
  have hcount : SecondCountableTopology (IntrinsicFoliationLeaf A.F.stablePartition q') := by
    let := A.stableTopology x
    let := (A.nativeS x).secondCountable
    exact (A.stableClassHomeomorph x).secondCountableTopology
  let := hcount
  let : LocallyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition q) :=
    ChartedSpace.locallyConnectedSpace (Fin (2*d-2) → ℝ) _
  let : LocallyConnectedSpace (IntrinsicFoliationLeaf A.F.stablePartition q') :=
    ChartedSpace.locallyConnectedSpace (Fin s → ℝ) _
  let e : IntrinsicFoliationLeaf P.foliations.stablePartition q ≃
      IntrinsicFoliationLeaf A.F.stablePartition q' :=
    Equiv.subtypeEquiv (Equiv.refl M) (fun y ↦ by
      change Quotient.mk _ y = Quotient.mk _ x ↔ Quotient.mk _ y = Quotient.mk _ x
      rw [Quotient.eq, Quotient.eq]
      exact hrel y x)
  have hc : Continuous e := continuous_stable_leaf_lift_g9 A.F q' inferInstance e
    (P.foliations.stable_inclusion q)
  have hi : Continuous e.symm := continuous_stable_leaf_lift_g9 P.foliations q
    inferInstance e.symm (A.F.stable_inclusion q')
  exact ⟨{e with continuous_toFun := hc, continuous_invFun := hi}, fun _ ↦ rfl⟩
end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- Pulling back a native real atlas along the point-preserving homeomorphism transports its smooth structure and tangent inclusion. (HPS, §7) -/
theorem native_leaf_real_atlas_transport
    {d r : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {L : Type u} [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (D : RealTangentDistribution (realModel d) M) (N : HPS.NativeLeaf (r := r) D L)
    (S : Set M) [tS : TopologicalSpace S] (h : S ≃ₜ L)
    (hh : ∀ z : S, N.inclusion (h z) = z.val) :
    ∃ charts : ChartedSpace (Fin r → ℝ) S, letI := charts
    ∃ hm : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ S, letI := hm
    ∃ N' : HPS.NativeLeaf (r := r) D S,
      N'.inclusion = Subtype.val ∧
      ∃ e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) S L ∞,
        ∀ z, e z = h z := by
  let := N.hausdorff
  let := N.countable
  obtain ⟨charts, hm, e, he⟩ := carrier_smooth_transport_g15 (r := r) h
  let := charts
  let := hm
  have hi : (Subtype.val : S → M) = N.inclusion ∘ e := by
    funext z
    rw [Function.comp_apply, he, hh]
  have he' : ∀ z : L, (e.symm z).val = N.inclusion z := by
    intro z
    have hz := congrFun hi (e.symm z)
    simpa using hz
  have ht := carrier_tangent_image_g15 (realModel d) N.inclusion
    N.immersion.contMDiff S e.symm he' D N.tangent
  refine ⟨charts, hm, {
    inclusion := Subtype.val
    injective := Subtype.val_injective
    immersion := ?_
    connected := h.symm.connectedSpace_iff.mp N.connected
    hausdorff := h.symm.t2Space
    countable := h.secondCountableTopology
    tangent := ht.2 }, rfl, e, he⟩
  rw [hi]
  refine ⟨N.immersion.complement, inferInstance, inferInstance, ?_⟩
  intro z
  have hc := N.immersion.isImmersionOfComplement_complement (e z)
  have hdom : e.toHomeomorph.transOpenPartialHomeomorph hc.domChart ∈
      IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ S := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas).comp
        e.contMDiff.contMDiffOn (fun z hz ↦ hz)
    · exact e.symm.contMDiff.comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas)
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (hc.continuousAt.comp e.contMDiff.continuous.continuousAt) hc.equiv
    (e.toHomeomorph.transOpenPartialHomeomorph hc.domChart) hc.codChart
    (by simpa using hc.mem_domChart_source) hc.mem_codChart_source hdom
    hc.codChart_mem_maximalAtlas
  intro y hy
  simpa [OpenPartialHomeomorph.extend, Function.comp_def] using hc.writtenInCharts hy

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real
/-- The product-box dimensions determine the stable dimension when the unstable disk has real dimension two. -/
theorem native_fixed_stable_dimension
    {d s : ℕ} {M : Type u} [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,u} f Ps Pu s 2) :
    s = 2*d-2 := by
  have h := A.realCoordinates.toLinearEquiv.finrank_eq
  simp [ComplexModel, Module.finrank_pi_fintype] at h
  omega
end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- Auxiliary real atlases on the fixed partition carriers, together with their complex atlases. -/
structure FixedCarrierSmoothData
    {d s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    [ChartedSpace (Fin (s+2) → ℝ) M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F) where
  sCharts : ∀ q : Quotient F.stablePartition, letI := F.stableTopology q
    ChartedSpace (Fin (2*d-2) → ℝ) (IntrinsicFoliationLeaf F.stablePartition q)
  uCharts : ∀ q : Quotient F.unstablePartition, letI := F.unstableTopology q
    ChartedSpace (Fin 2 → ℝ) (IntrinsicFoliationLeaf F.unstablePartition q)
  sSmooth : ∀ q, letI := F.stableTopology q; letI := sCharts q
    IsManifold 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞ (IntrinsicFoliationLeaf F.stablePartition q)
  uSmooth : ∀ q, letI := F.unstableTopology q; letI := uCharts q
    IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (IntrinsicFoliationLeaf F.unstablePartition q)
  sNative : ∀ q, letI := F.stableTopology q; letI := sCharts q; letI := sSmooth q
    HPS.NativeLeaf (r := 2*d-2) a.splitting.stable.toDistribution
      (IntrinsicFoliationLeaf F.stablePartition q)
  uNative : ∀ q, letI := F.unstableTopology q; letI := uCharts q; letI := uSmooth q
    HPS.NativeLeaf (r := 2) a.splitting.unstable.toDistribution
      (IntrinsicFoliationLeaf F.unstablePartition q)
  sIncl : ∀ q, letI := F.stableTopology q; letI := sCharts q; letI := sSmooth q
    (sNative q).inclusion = Subtype.val
  uIncl : ∀ q, letI := F.unstableTopology q; letI := uCharts q; letI := uSmooth q
    (uNative q).inclusion = Subtype.val
  compatible : ∀ q, letI := F.unstableTopology q; letI := uCharts q; letI := C.charts q
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel 1) ∞
      (id : IntrinsicFoliationLeaf F.unstablePartition q → IntrinsicFoliationLeaf F.unstablePartition q) ∧
    ContMDiff (realModel 1) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (id : IntrinsicFoliationLeaf F.unstablePartition q → IntrinsicFoliationLeaf F.unstablePartition q)

/-- Transport the native smooth structures to fixed carriers while preserving topology, complex charts, and tangent inclusions. (HPS, §7; Ghys, §2) -/
theorem native_fixed_carrier_smooth_data
    {d s : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    (A : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q; letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z) :
    letI := A.realAmbientCharts
    Nonempty (FixedCarrierSmoothData f a A.F C) := by
  classical
  let := A.realAmbientCharts
  let := P.realCharts
  have hs (q : Quotient A.F.stablePartition) :
      letI := A.F.stableTopology q
      ∃ charts : ChartedSpace (Fin (2*d-2) → ℝ) (IntrinsicFoliationLeaf A.F.stablePartition q),
      letI := charts
      ∃ hm : IsManifold 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞ (IntrinsicFoliationLeaf A.F.stablePartition q),
      letI := hm
      ∃ N : HPS.NativeLeaf (r := 2*d-2) a.splitting.stable.toDistribution
        (IntrinsicFoliationLeaf A.F.stablePartition q), N.inclusion = Subtype.val := by
    induction q using Quotient.inductionOn with
    | h x =>
      let q := Quotient.mk P.foliations.stablePartition x
      let q' := Quotient.mk A.F.stablePartition x
      let := P.foliations.stableTopology q
      let := P.foliations.stableCharts q
      let := P.stableSmooth q
      let := A.F.stableTopology q'
      obtain ⟨E, hE⟩ := native_presentation_stable_comparison f a P A x
      obtain ⟨charts, hm, N, hN, _⟩ := native_leaf_real_atlas_transport (tS := A.F.stableTopology q')
        a.splitting.stable.toDistribution (P.stableNative q)
        {y : M | Quotient.mk A.F.stablePartition y = q'} E.symm (fun z ↦ by
          rw [P.stable_inclusion_eq]
          have h := hE (E.symm z)
          simpa using h.symm)
      exact ⟨charts, hm, N, hN⟩
  have hu (q : Quotient A.F.unstablePartition) :
      let := A.F.unstableTopology q
      ∃ charts : ChartedSpace (Fin 2 → ℝ) (IntrinsicFoliationLeaf A.F.unstablePartition q),
      let := charts
      ∃ hm : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (IntrinsicFoliationLeaf A.F.unstablePartition q),
      let := hm
      ∃ N : HPS.NativeLeaf (r := 2) a.splitting.unstable.toDistribution
        (IntrinsicFoliationLeaf A.F.unstablePartition q),
      N.inclusion = Subtype.val ∧
      (let := C.charts q
       ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel 1) ∞
         (id : IntrinsicFoliationLeaf A.F.unstablePartition q → IntrinsicFoliationLeaf A.F.unstablePartition q) ∧
       ContMDiff (realModel 1) 𝓘(ℝ, Fin 2 → ℝ) ∞
         (id : IntrinsicFoliationLeaf A.F.unstablePartition q → IntrinsicFoliationLeaf A.F.unstablePartition q)) := by
    induction q using Quotient.inductionOn with
    | h x =>
      let q := Quotient.mk P.foliations.unstablePartition x
      let q' := Quotient.mk A.F.unstablePartition x
      let := P.foliations.unstableTopology q
      let := P.foliations.unstableCharts q
      let := P.unstableSmooth q
      let := P.complexLeaves.charts q
      let := A.F.unstableTopology q'
      let := C.charts q'
      obtain ⟨E, hE⟩ := native_presentation_unstable_comparison f a P A C hC x
      obtain ⟨charts, hm, N, hN, e, he⟩ := native_leaf_real_atlas_transport (tS := A.F.unstableTopology q')
        a.splitting.unstable.toDistribution (P.unstableNative q)
        {y : M | Quotient.mk A.F.unstablePartition y = q'} E.symm.toHomeomorph
        (fun z ↦ by
          rw [P.unstable_inclusion_eq]
          have h := hE (E.symm z)
          simpa using h.symm)
      let : TopologicalSpace { y : M // Quotient.mk A.F.unstablePartition y = q' } :=
        A.F.unstableTopology q'
      let : ChartedSpace (ComplexModel 1) { y : M // Quotient.mk A.F.unstablePartition y = q' } :=
        C.charts q'
      let : TopologicalSpace (A.F.ULeaf x) := A.F.unstableTopology q'
      let : ChartedSpace (ComplexModel 1) (A.F.ULeaf x) := C.charts q'
      let : ChartedSpace (Fin 2 → ℝ) (A.F.ULeaf x) := charts
      let : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (A.F.ULeaf x) := hm
      let e' : Diffeomorph 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ)
          (A.F.ULeaf x) (P.foliations.ULeaf x) ∞ := e
      have he' (z : A.F.ULeaf x) : e' z = E.symm z := he z
      refine ⟨charts, hm, N, hN, ?_, ?_⟩
      · have heSmooth : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞
            (fun z : A.F.ULeaf x ↦ e' z) := e'.contMDiff_toFun
        have hmid : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel 1) ∞
            (fun z : A.F.ULeaf x ↦ e' z) :=
          (P.unstable_real_complex_compatible q).1.comp heSmooth
        have hh : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel 1) ∞
            (fun z : A.F.ULeaf x ↦ E (e' z)) :=
          (contMDiff_complex_to_real E.contMDiff_toFun).comp hmid
        apply hh.congr
        intro z
        symm
        change E (e' z) = z
        rw [he']
        exact E.apply_symm_apply z
      · have hmid : ContMDiff (realModel 1) 𝓘(ℝ, Fin 2 → ℝ) ∞
            (fun z : A.F.ULeaf x ↦ E.symm z) :=
          (P.unstable_real_complex_compatible q).2.comp
            (contMDiff_complex_to_real E.contMDiff_invFun)
        have hh : ContMDiff (realModel 1) 𝓘(ℝ, Fin 2 → ℝ) ∞
            (fun z : A.F.ULeaf x ↦ e'.symm (E.symm z)) :=
          e'.contMDiff_invFun.comp hmid
        apply hh.congr
        intro z
        symm
        change e'.symm (E.symm z) = z
        rw [← he' z]
        exact e'.symm_apply_apply z
  choose cs hs ns hns using hs
  choose cu hu nu hnu hc using hu
  exact ⟨⟨cs, cu, hs, hu, ns, nu, hns, hnu, hc⟩⟩
end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

section FixedPresentation
variable {d : ℕ} {M : Type u} [MetricSpace M] [SecondCountableTopology M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  (A : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
    a.splitting.stable.toDistribution a.splitting.unstable.toDistribution (2*d-2) 2)
  (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
  (B : letI := A.realAmbientCharts; FixedCarrierSmoothData f a A.F C)

/-- Retains the fixed product-box and leaf-topology data while installing transported native real charts. -/
def fixedCarrierFoliations : letI := A.realAmbientCharts
    TransverseContinuousFoliations.{u,u} (2*d-2) 2 M :=
  letI := A.realAmbientCharts
  { A.F with stableCharts := B.sCharts, unstableCharts := B.uCharts }

/-- Retains the same complex charts on the same intrinsic unstable topology. -/
def fixedCarrierComplexLeaves : letI := A.realAmbientCharts
    IntrinsicComplexUnstableLeaves (fixedCarrierFoliations f a A C B) :=
  letI := A.realAmbientCharts
  ⟨C.real_dimension, C.charts, C.complex_manifold⟩

/-- Repackages the fixed native boxes as a Ghys presentation with compatible smooth real leaf atlases. (HPS, §7; Ghys, §2) -/
def fixedCarrierPresentation
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q; letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M)) :
    AnosovIntrinsicFoliationPresentation f a := by
  let := A.realAmbientCharts
  exact {
  realCharts := A.realAmbientCharts
  foliations := fixedCarrierFoliations f a A C B
  complexLeaves := fixedCarrierComplexLeaves f a A C B
  metric := inferInstance
  metric_topology := rfl
  stable_asymptotic := native_identification_stable_partition_iff_asymptotic A
  unstable_asymptotic := native_identification_unstable_partition_iff_asymptotic A
  stableSmooth := B.sSmooth
  unstableSmooth := B.uSmooth
  stableNative := B.sNative
  unstableNative := B.uNative
  stable_inclusion_eq := B.sIncl
  unstable_inclusion_eq := B.uIncl
  unstable_real_complex_compatible := B.compatible
  unstable_holomorphic := hC }
/-- Changing only the auxiliary real leaf charts preserves the affine and transverse projective data. (HPS, §§4–5; Ghys, §§4–5) -/
theorem fixedCarrier_transverse_atlas_transport
    (affine : letI := A.realAmbientCharts
      AffineUnstableLeafStructures (fixedCarrierFoliations f a A C B)
        (fixedCarrierComplexLeaves f a A C B))
    (hcomplete : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := (fixedCarrierFoliations f a A C B).unstableTopology q; letI := (fixedCarrierComplexLeaves f a A C B).charts q
        ComplexAffineStructure.Complete _ (affine.structureAt q))
    (atlas : letI := A.realAmbientCharts
      TransverseProjectiveAtlas (fixedCarrierFoliations f a A C B)
        (fixedCarrierComplexLeaves f a A C B))
    (hAtlas : letI := A.realAmbientCharts
      ∀ c ∈ atlas.charts, ∀ x : M, ∀ z : (fixedCarrierFoliations f a A C B).ULeaf x,
        letI := (fixedCarrierFoliations f a A C B).unstableTopology (Quotient.mk A.F.unstablePartition x)
        letI := (fixedCarrierComplexLeaves f a A C B).charts (Quotient.mk A.F.unstablePartition x)
        z.val ∈ c.domain (fixedCarrierFoliations f a A C B) (fixedCarrierComplexLeaves f a A C B) →
        ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.structureAt (Quotient.mk A.F.unstablePartition x)),
          z ∈ b.source ∧ ∃ g : ComplexMobiusTransformation,
            ∀ᶠ w in 𝓝 z,
              w ∈ b.source ∧ w.val ∈ c.domain (fixedCarrierFoliations f a A C B) (fixedCarrierComplexLeaves f a A C B) ∧
                c.transverseCoordinate (fixedCarrierFoliations f a A C B) (fixedCarrierComplexLeaves f a A C B) w.val =
                  g.apply (complexProjectiveLineFinite (b w))) :
    letI := A.realAmbientCharts
    ∃ affine' : AffineUnstableLeafStructures A.F C,
      (∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q; letI := C.charts q
        ComplexAffineStructure.Complete _ (affine'.structureAt q)) ∧
      ∃ atlas' : TransverseProjectiveAtlas A.F C,
        ∀ c ∈ atlas'.charts, ∀ x : M, ∀ z : A.F.ULeaf x,
          letI := C.charts (Quotient.mk A.F.unstablePartition x)
          z.val ∈ c.domain A.F C →
          ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine'.atPoint A.F C x),
            z ∈ b.source ∧ ∃ g : ComplexMobiusTransformation,
              ∀ᶠ w in 𝓝 z,
                w ∈ b.source ∧ w.val ∈ c.domain A.F C ∧
                  c.transverseCoordinate A.F C w.val = g.apply (complexProjectiveLineFinite (b w)) := by
  let := A.realAmbientCharts
  let affine' : AffineUnstableLeafStructures A.F C := ⟨affine.structureAt⟩
  let liftChart (c : TransverseProjectiveChart (fixedCarrierFoliations f a A C B)
      (fixedCarrierComplexLeaves f a A C B)) : TransverseProjectiveChart A.F C := {
    box := c.box
    stableDomain := c.stableDomain
    coordinate := c.coordinate
    holomorphic_on_plaque := c.holomorphic_on_plaque }
  let atlas' : TransverseProjectiveAtlas A.F C := {
    charts := liftChart '' atlas.charts
    cover := by
      intro x
      obtain ⟨c,hc,hx⟩ := atlas.cover x
      exact ⟨liftChart c, ⟨c,hc,rfl⟩, hx⟩
    compatible := by
      rintro _ ⟨c,hc,rfl⟩ _ ⟨d,hd,rfl⟩
      exact atlas.compatible c hc d hd }
  refine ⟨affine',hcomplete,atlas',?_⟩
  rintro _ ⟨c,hc,rfl⟩ x z hz
  exact hAtlas c hc x z hz

end FixedPresentation
end HolomorphicAnosov.Ghys

