import HolomorphicAnosov.Ghys.DisconnectedNativeTransverseFoliations
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Geometry.ComplexSubbundleChart
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgradeOfComplexTangent
import HolomorphicAnosov.Paper.Ghys.NativeUnstableComplexRankOneFromRealRankTwo

/-! Holomorphic Anosov data with complex unstable rank one admit an intrinsic stable and unstable
foliation presentation. (Ghys, Prop.3.1) -/

noncomputable section
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

universe u

attribute [local instance] complex_isManifold_real

/-- Holomorphic Anosov data with complex unstable rank one admit an intrinsic foliation presentation
with holomorphic unstable leaves. (Ghys, §2 pp.588–590 and Prop.3.1; Hirsch–Pugh–Shub, §§6B–7
pp.114–116; Demailly, Ch.I §7 Lemma 7.15 p.60) -/
theorem proposition31_native_presentation
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    ∃ _P : AnosovIntrinsicFoliationPresentation f a, True := by
  classical
  rcases isEmpty_or_nonempty M with hEmpty | hNonempty
  · let := hEmpty
    let realCharts : ChartedSpace (Fin ((2*d-2)+2) → ℝ) M :=
      ChartedSpace.empty _ _
    let F : TransverseContinuousFoliations.{u, u} (2*d-2) 2 M := {
      boxIndex := PEmpty
      box := fun i ↦ isEmptyElim i
      cover := fun x ↦ isEmptyElim x
      stablePartition := ⊥
      unstablePartition := ⊥
      stable_generated := fun x ↦ isEmptyElim x
      unstable_generated := fun x ↦ isEmptyElim x
      stableTopology := fun q ↦ isEmptyElim q
      unstableTopology := fun q ↦ isEmptyElim q
      stableCharts := fun q ↦ isEmptyElim q
      unstableCharts := fun q ↦ isEmptyElim q
      stable_connected := fun q ↦ isEmptyElim q
      unstable_connected := fun q ↦ isEmptyElim q
      stable_inclusion := fun q ↦ isEmptyElim q
      unstable_inclusion := fun q ↦ isEmptyElim q
      stableLabel := fun i ↦ isEmptyElim i
      unstableLabel := fun i ↦ isEmptyElim i
      stable_label := fun i ↦ isEmptyElim i
      unstable_label := fun i ↦ isEmptyElim i
      stable_plaque := fun i ↦ isEmptyElim i
      unstable_plaque := fun i ↦ isEmptyElim i
      stable_topology_generated := fun q ↦ isEmptyElim q
      unstable_topology_generated := fun q ↦ isEmptyElim q }
    let C : IntrinsicComplexUnstableLeaves F := {
      real_dimension := rfl
      charts := fun q ↦ isEmptyElim q
      complex_manifold := fun q ↦ isEmptyElim q }
    let P : AnosovIntrinsicFoliationPresentation f a := {
      realCharts := realCharts
      foliations := F
      complexLeaves := C
      metric := MetricSpace.induced (isEmptyElim : M → Empty) (by
        intro x
        exact isEmptyElim x) inferInstance
      metric_topology := Subsingleton.elim _ _
      stable_asymptotic := fun x ↦ isEmptyElim x
      unstable_asymptotic := fun x ↦ isEmptyElim x
      stableSmooth := fun q ↦ isEmptyElim q
      unstableSmooth := fun q ↦ isEmptyElim q
      stableNative := fun q ↦ isEmptyElim q
      unstableNative := fun q ↦ isEmptyElim q
      stable_inclusion_eq := fun q ↦ isEmptyElim q
      unstable_inclusion_eq := fun q ↦ isEmptyElim q
      unstable_real_complex_compatible := fun q ↦ isEmptyElim q
      unstable_holomorphic := fun q ↦ isEmptyElim q }
    exact ⟨P, trivial⟩
  · let := hNonempty
    let metric : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
    let := metric
    obtain ⟨B, hB⟩ := disconnected_native_transverse_foliations f a (by rfl) hRank
    let := realCoordinateRechart (M := M) B
    obtain ⟨F, hparts, hs, hu⟩ := hB
    choose smS NS hNS using hs
    choose smU NU hNU using hu
    choose K _hdim hK using hRank
    obtain ⟨S, hS⟩ := complex_subbundle_of_realification a.splitting.unstable K hK
    have upgrades : ∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q
        letI := F.unstableCharts q
        Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2) 1
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M)) := by
      intro q
      let := F.unstableTopology q
      let := F.unstableCharts q
      let := smU q
      have hn : (NU q).inclusion =
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) := hNU q
      have hi : Manifold.IsImmersion 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) := by
        simpa only [hn] using (NU q).immersion
      have ht : ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) Subtype.val z).range =
            a.splitting.unstable.toDistribution z.val := by
        intro z
        have hz := (NU q).tangent z
        rw [hn] at hz
        exact hz
      apply nativeLeafComplexUpgrade_of_complex_tangent (k := 1)
        Subtype.val a.splitting.unstable hi ht S
      intro z
      rw [ht z, hS]
      exact hK z.val
    let U q := Classical.choice (upgrades q)
    let C : IntrinsicComplexUnstableLeaves F := {
      real_dimension := rfl
      charts := fun q ↦ by
        let := F.unstableTopology q
        let := F.unstableCharts q
        exact (U q).charts
      complex_manifold := fun q ↦ by
        let := F.unstableTopology q
        let := F.unstableCharts q
        exact (U q).complex_manifold }
    refine ⟨{
      realCharts := realCoordinateRechart B
      foliations := F
      complexLeaves := C
      metric := metric
      metric_topology := rfl
      stable_asymptotic := hparts.1
      unstable_asymptotic := hparts.2
      stableSmooth := smS
      unstableSmooth := smU
      stableNative := NS
      unstableNative := NU
      stable_inclusion_eq := hNS
      unstable_inclusion_eq := hNU
      unstable_real_complex_compatible := ?_
      unstable_holomorphic := ?_ }, trivial⟩
    · intro q
      let := F.unstableTopology q
      let := F.unstableCharts q
      let := smU q
      exact native_complex_upgrade_identity_mdifferentiable (U q)
    · intro q
      let := F.unstableTopology q
      let := F.unstableCharts q
      exact (U q).inclusion_holomorphic


end HolomorphicAnosov.Ghys
