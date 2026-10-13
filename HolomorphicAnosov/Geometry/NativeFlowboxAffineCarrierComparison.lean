import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeBijectiveInverseContmdiff
import HolomorphicAnosov.Geometry.ContinuousUnstableLeafLiftG1
import HolomorphicAnosov.Geometry.NativeIdentificationPartitionAsymptotic
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgradeOfComplexTangent
import HolomorphicAnosov.Geometry.ContinuousComplexRankOneSubbundle
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.UniformSpace.Compact

/-! This file compares immersed complex curve carriers with intrinsic partition classes by
point-preserving biholomorphisms. -/

noncomputable section
open Set _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- An immersed complex curve with the specified asymptotic image is point-preservingly
biholomorphic to the corresponding intrinsic partition class. (Hirsch–Pugh–Shub, §7, pp.
115–116; Ghys, §2, pp. 588–590) -/
theorem native_flowbox_curve_fixed_carrier_biholomorph
    {d s : ℕ} {M : Type u} [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,u} f Ps Pu s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z)
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
    (j : L → M) (hj : ContMDiff 𝓘(ℂ) (complexModel d) ∞ j)
    (hji : Function.Injective j)
    (hjd : ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) j z))
    (x : M) (hrange : Set.range j = {y | ForwardAsymptotic f.symm x y}) :
    letI := A.realAmbientCharts
    letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
    letI := C.charts (Quotient.mk A.F.unstablePartition x)
    ∃ E : Diffeomorph 𝓘(ℂ) (complexModel 1) L (A.F.ULeaf x) ∞,
      ∀ z, (E z).val = j z := by
  classical
  let :=  A.realAmbientCharts
  let q := Quotient.mk A.F.unstablePartition x
  let :=  A.F.unstableTopology q
  let :=  C.charts q
  let :=  C.complex_manifold q
  have hlabel (y : M) : y ∈ Set.range j ↔ Quotient.mk A.F.unstablePartition y = q := by
    rw [hrange]
    change ForwardAsymptotic f.symm x y ↔ _
    rw [← native_identification_unstable_partition_iff_asymptotic A x y]
    exact ⟨fun h ↦ (Quotient.sound h).symm, fun h ↦ Quotient.exact h.symm⟩
  let g : L → A.F.ULeaf x := fun z ↦ ⟨j z, (hlabel _).mp (Set.mem_range_self z)⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro z w h
      exact hji (congrArg Subtype.val h)
    · intro y
      obtain ⟨z, hz⟩ := (hlabel y.val).mpr y.property
      exact ⟨z, Subtype.ext hz⟩
  let e := Equiv.ofBijective g hbij
  have he (z : L) : (e z).val = j z := rfl
  have hcount : SecondCountableTopology (A.F.ULeaf x) := by
    let :=  A.unstableTopology x
    let :=  (A.nativeU x).secondCountable
    exact (A.unstableClassHomeomorph x).secondCountableTopology
  let :=  hcount
  let : LocallyConnectedSpace L := ChartedSpace.locallyConnectedSpace ℂ L
  have hcont : Continuous e := by
    apply continuous_unstable_leaf_lift_g1 A.F q inferInstance e
    exact hj.continuous.congr (fun z ↦ (he z).symm)
  have heq : (Subtype.val : A.F.ULeaf x → M) ∘ e = j := funext he
  have hs : ContMDiff 𝓘(ℂ) (complexModel 1) ∞ e := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt ((hC q).2 (e z))).mpr
    refine ⟨hcont.continuousAt, ?_⟩
    rw [heq]
    exact hj z
  have hb (z : L) : Function.Bijective (mfderiv 𝓘(ℂ) (complexModel 1) e z) := by
    have hd := mfderiv_comp z
      (((hC q).1 (e z)).mdifferentiableAt (by simp))
      ((hs z).mdifferentiableAt (by simp))
    rw [heq] at hd
    have hinj : Function.Injective (mfderiv 𝓘(ℂ) (complexModel 1) e z) := by
      intro v w hvw
      apply hjd z
      rw [hd]
      exact congrArg (mfderiv (complexModel 1) (complexModel d)
        (Subtype.val : A.F.ULeaf x → M) (e z)) hvw
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      change Module.finrank ℂ ℂ = Module.finrank ℂ (Fin 1 → ℂ)
      simp)).mp hinj
  exact ⟨{ e with
    contMDiff_toFun := hs
    contMDiff_invFun := native_bijective_inverse_contMDiff 𝓘(ℂ) (complexModel 1) e hs hb }, he⟩

/-- An immersed curve in the one-coordinate complex model with the specified asymptotic image is
point-preservingly biholomorphic to the corresponding intrinsic partition class.
(Hirsch–Pugh–Shub, §7, pp. 115–116; Ghys, §2, pp. 588–590) -/
theorem native_flowbox_model_curve_fixed_carrier_biholomorph
    {d s : ℕ} {M : Type u} [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,u} f Ps Pu s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z)
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L] [IsManifold (complexModel 1) ∞ L]
    (j : L → M) (hj : ContMDiff (complexModel 1) (complexModel d) ∞ j)
    (hji : Function.Injective j)
    (hjd : ∀ z, Function.Injective (mfderiv (complexModel 1) (complexModel d) j z))
    (x : M) (hrange : Set.range j = {y | ForwardAsymptotic f.symm x y}) :
    letI := A.realAmbientCharts
    letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
    letI := C.charts (Quotient.mk A.F.unstablePartition x)
    ∃ E : Diffeomorph (complexModel 1) (complexModel 1) L (A.F.ULeaf x) ∞,
      ∀ z, (E z).val = j z := by
  classical
  let :=  A.realAmbientCharts
  let q := Quotient.mk A.F.unstablePartition x
  let :=  A.F.unstableTopology q
  let :=  C.charts q
  let :=  C.complex_manifold q
  have hlabel (y : M) : y ∈ Set.range j ↔ Quotient.mk A.F.unstablePartition y = q := by
    rw [hrange]
    change ForwardAsymptotic f.symm x y ↔ _
    rw [← native_identification_unstable_partition_iff_asymptotic A x y]
    exact ⟨fun h ↦ (Quotient.sound h).symm, fun h ↦ Quotient.exact h.symm⟩
  let g : L → A.F.ULeaf x := fun z ↦ ⟨j z, (hlabel _).mp (Set.mem_range_self z)⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro z w h
      exact hji (congrArg Subtype.val h)
    · intro y
      obtain ⟨z, hz⟩ := (hlabel y.val).mpr y.property
      exact ⟨z, Subtype.ext hz⟩
  let e := Equiv.ofBijective g hbij
  have he (z : L) : (e z).val = j z := rfl
  have hcount : SecondCountableTopology (A.F.ULeaf x) := by
    let :=  A.unstableTopology x
    let :=  (A.nativeU x).secondCountable
    exact (A.unstableClassHomeomorph x).secondCountableTopology
  let :=  hcount
  let : LocallyConnectedSpace L := ChartedSpace.locallyConnectedSpace (ComplexModel 1) L
  have hcont : Continuous e := by
    apply continuous_unstable_leaf_lift_g1 A.F q inferInstance e
    exact hj.continuous.congr (fun z ↦ (he z).symm)
  have heq : (Subtype.val : A.F.ULeaf x → M) ∘ e = j := funext he
  have hs : ContMDiff (complexModel 1) (complexModel 1) ∞ e := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt ((hC q).2 (e z))).mpr
    refine ⟨hcont.continuousAt, ?_⟩
    rw [heq]
    exact hj z
  have hb (z : L) : Function.Bijective (mfderiv (complexModel 1) (complexModel 1) e z) := by
    have hd := mfderiv_comp z
      (((hC q).1 (e z)).mdifferentiableAt (by simp))
      ((hs z).mdifferentiableAt (by simp))
    rw [heq] at hd
    have hinj : Function.Injective (mfderiv (complexModel 1) (complexModel 1) e z) := by
      intro v w hvw
      apply hjd z
      rw [hd]
      exact congrArg (mfderiv (complexModel 1) (complexModel d)
        (Subtype.val : A.F.ULeaf x → M) (e z)) hvw
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      change Module.finrank ℂ (Fin 1 → ℂ) = Module.finrank ℂ (Fin 1 → ℂ)
      simp)).mp hinj
  exact ⟨{ e with
    contMDiff_toFun := hs
    contMDiff_invFun := native_bijective_inverse_contMDiff (complexModel 1) (complexModel 1) e hs hb }, he⟩

/-- Metrics inducing the same topology on a compact space define the same asymptotic relation. -/
theorem native_flowbox_asymptotic_metric_iff
    {M : Type u} [m : MetricSpace M] [CompactSpace M]
    (mG : MetricSpace M)
    (hmetric : mG.toUniformSpace.toTopologicalSpace = m.toUniformSpace.toTopologicalSpace)
    (f : M → M) (x y : M) :
    @ForwardAsymptotic M mG f x y ↔ @ForwardAsymptotic M m f x y := by
  have hu : mG.toUniformSpace = m.toUniformSpace :=
    @unique_uniformity_of_compact M m.toUniformSpace.toTopologicalSpace inferInstance
      mG.toUniformSpace m.toUniformSpace hmetric rfl
  have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ mG.toPseudoMetricSpace
    (fun n ↦ ((f^[n]) y, (f^[n]) x)) Filter.atTop
  have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m.toPseudoMetricSpace
    (fun n ↦ ((f^[n]) y, (f^[n]) x)) Filter.atTop
  unfold ForwardAsymptotic
  rw [← h₁, ← h₂]
  change Filter.Tendsto _ _ mG.toUniformSpace.uniformity ↔
    Filter.Tendsto _ _ m.toUniformSpace.uniformity
  rw [hu]

/-- A real rank-two immersed stable leaf with complex tangent images and the specified asymptotic
image admits a point-preserving biholomorphism to the inverse presentation's affine carrier.
(Demailly, I Lemma 7.15; Hirsch–Pugh–Shub, §7, pp. 115–116; Ghys, §2, pp. 588–590) -/
theorem native_flowbox_stable_fixed_carrier_biholomorph
    {d s : ℕ} {M : Type u} [m : MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : M ≃ₜ M) (Ps : ContinuousRealTangentSubbundle (realModel d) M)
    (hRank : HasComplexRankOne Ps.toDistribution)
    (Pu : RealTangentDistribution (realModel d) M)
    (A : NativeTransverseAsymptoticIdentification.{u,u} f.symm Pu Ps.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z)
    {L : Type u} [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ L]
    (leaf : HPS.NativeLeaf (r := 2) Ps.toDistribution L)
    (mG : MetricSpace M)
    (hmetric : mG.toUniformSpace.toTopologicalSpace = m.toUniformSpace.toTopologicalSpace)
    (x : M)
    (hrange : letI : MetricSpace M := m
      Set.range leaf.inclusion = {y | @ForwardAsymptotic M mG f x y}) :
    letI : MetricSpace M := m
    ∃ U : NativeLeafComplexUpgrade (d := d) (r := 2) 1 leaf.inclusion,
      letI := U.charts
      letI := A.realAmbientCharts
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      ∃ E : Diffeomorph (complexModel 1) (complexModel 1) L (A.F.ULeaf x) ∞,
        ∀ z, (E z).val = leaf.inclusion z := by
  let : MetricSpace M := m
  obtain ⟨K, T, hT, _, hreal⟩ := exists_continuous_complex_rank_one_subbundle Ps hRank
  obtain ⟨U⟩ := nativeLeafComplexUpgrade_of_complex_tangent (k := 1)
    leaf.inclusion Ps leaf.immersion leaf.tangent T (fun z ↦ by
      rw [leaf.tangent, hT]
      exact hreal (leaf.inclusion z))
  refine ⟨U, ?_⟩
  let := U.charts
  let := U.complex_manifold
  have hrange' : Set.range leaf.inclusion = {y | ForwardAsymptotic f.symm.symm x y} := by
    rw [hrange]
    ext y
    exact native_flowbox_asymptotic_metric_iff mG hmetric f x y
  exact native_flowbox_model_curve_fixed_carrier_biholomorph A C hC
    leaf.inclusion U.inclusion_holomorphic leaf.injective
    (fun z ↦ (U.inclusion_immersion z).mfderiv_injective (by simp)) x hrange'

end HolomorphicAnosov.Ghys

