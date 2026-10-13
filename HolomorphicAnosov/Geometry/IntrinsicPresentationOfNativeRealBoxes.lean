import HolomorphicAnosov.Geometry.NativePairToTransverseG10
import HolomorphicAnosov.Geometry.FixedUnitProductNativePlaquesG10
import HolomorphicAnosov.Geometry.NativeLeafOnIntrinsicClass
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgradeOfComplexTangent
import HolomorphicAnosov.Geometry.ContinuousComplexRankOneSubbundle
import HolomorphicAnosov.Paper.Ghys.NativeUnstableComplexRankOneFromRealRankTwo
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.original_real_tangent_finrank
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter TopologicalSpace _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real
/-- The actual native pair and common real boxes give an intrinsic complex foliation presentation, retaining original points and intrinsic structures (HPS, Invariant Manifolds (1977), pp.115–116, intrinsic foliations and plaque-generated leaf topology; Ghys, Holomorphic Anosov Systems (1995), §2 pp.588–589, original complex unstable leaves; Demailly, Complex Analytic and Differential Geometry, I §3.A,C and §7 Lemma 7.15).-/
theorem intrinsicPresentation_of_native_real_boxes
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin (2*d-2) → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i)]
    (S : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls (fun _ ↦ 2*d-2))
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu (fun _ ↦ 2))
    (m : MetricSpace M)
    (hm : m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (hrS : ∀ i (x : Ls i) y, (∃ z, (S.leaf i).inclusion z = y) ↔
      @ForwardAsymptotic M m f ((S.leaf i).inclusion x) y)
    (hrU : ∀ i (x : Lu i) y, (∃ z, (U.leaf i).inclusion z = y) ↔
      @ForwardAsymptotic M m f.symm ((U.leaf i).inclusion x) y)
    (hsource : ∀ p : M,
      ∃ (Ds : Opens (Fin (2*d-2) → ℝ)) (Du : Opens (Fin 2 → ℝ))
        (O : Opens M) (e : (Ds × Du) ≃ₜ O), p ∈ O ∧
        (∀ w : Du, ∃ (i : ιs) (V : Opens (Ls i)) (c : Ds ≃ₜ V),
          ∀ z : Ds, (e (z,w)).val = (S.leaf i).inclusion (c z).val) ∧
        (∀ z : Ds, ∃ (i : ιu) (V : Opens (Lu i)) (c : Du ≃ₜ V),
          ∀ w : Du, (e (z,w)).val = (U.leaf i).inclusion (c w).val)) :
    ∃ P : AnosovIntrinsicFoliationPresentation f a,
      letI := P.realCharts
      (∀ x y, P.foliations.stablePartition x y ↔
        ∃ i z w, (S.leaf i).inclusion z = x ∧ (S.leaf i).inclusion w = y) ∧
      (∀ x y, P.foliations.unstablePartition x y ↔
        ∃ i z w, (U.leaf i).inclusion z = x ∧ (U.leaf i).inclusion w = y) ∧
      (∀ q : Quotient P.foliations.stablePartition,
        letI := P.foliations.stableTopology q; letI := P.foliations.stableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin (2*d-2) → ℝ) 𝓘(ℝ, Fin (2*d-2) → ℝ)
          (Ls i) (IntrinsicFoliationLeaf P.foliations.stablePartition q) ∞,
          ∀ z, (e z).val = (S.leaf i).inclusion z) ∧
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q; letI := P.foliations.unstableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ)
          (Lu i) (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞,
          ∀ z, (e z).val = (U.leaf i).inclusion z) := by
  classical
  let : MetricSpace M := m.replaceTopology hm.symm
  let x : M := Classical.choice inferInstance
  have htwo := TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank x
  have hbound := (a.splitting.unstable.toDistribution x).finrank_le
  rw [htwo, TheoremAProof.Dimension.original_real_tangent_finrank x] at hbound
  have hdim : (2*d-2)+2 = 2*d := by omega
  let B : ComplexModel d ≃L[ℝ] (Fin ((2*d-2)+2) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [ComplexModel, finrank_real_of_complex, hdim])
  let := realCoordinateRechart (d := d) (s := 2*d-2) (t := 2) (M := M) B
  have hboxes : ∀ p : M, ∃ C : TransverseFoliationBox (2*d-2) 2 M,
      p ∈ C.image ∧
      (∀ w, ∃ i : ιs, ∃ j : FoliationCoordinateDisk (2*d-2) → Ls i,
        IsOpenEmbedding j ∧ ∀ z, (C.chart (z,w)).val = (S.leaf i).inclusion (j z)) ∧
      (∀ z, ∃ i : ιu, ∃ j : FoliationCoordinateDisk 2 → Lu i,
        IsOpenEmbedding j ∧ ∀ w, (C.chart (z,w)).val = (U.leaf i).inclusion (j w)) := by
    intro p
    obtain ⟨Ds, Du, O, e, hp, hs, hu⟩ := hsource p
    exact fixed_unit_product_box_native_plaques_g10
      (fun i ↦ (S.leaf i).inclusion) (fun i ↦ (U.leaf i).inclusion)
      Ds Du O e ⟨p, hp⟩ hs hu
  let C : M → TransverseFoliationBox (2*d-2) 2 M := fun p ↦ (hboxes p).choose
  obtain ⟨F, hRs, hRu, htS, htU, heS, heU, hmS, hmU, _⟩ :=
    native_pair_to_transverse_foliations_with_smooth_leaves
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution S U C
      (fun p ↦ ⟨p, (hboxes p).choose_spec.1⟩)
      (fun p ↦ (hboxes p).choose_spec.2.1)
      (fun p ↦ (hboxes p).choose_spec.2.2)
  have hNS (q : Quotient F.stablePartition) :
      letI := F.stableTopology q; letI := F.stableCharts q; letI := hmS q
      ∃ N : HPS.NativeLeaf (r := 2*d-2) a.splitting.stable.toDistribution
        (IntrinsicFoliationLeaf F.stablePartition q), N.inclusion = Subtype.val := by
    let := F.stableTopology q; let := F.stableCharts q; let := hmS q
    obtain ⟨i, e, he⟩ := heS q
    exact native_leaf_on_intrinsic_class a.splitting.stable.toDistribution
      (S.leaf i) F.stablePartition q e he (htS q)
  have hNU (q : Quotient F.unstablePartition) :
      letI := F.unstableTopology q; letI := F.unstableCharts q; letI := hmU q
      ∃ N : HPS.NativeLeaf (r := 2) a.splitting.unstable.toDistribution
        (IntrinsicFoliationLeaf F.unstablePartition q), N.inclusion = Subtype.val := by
    let := F.unstableTopology q; let := F.unstableCharts q; let := hmU q
    obtain ⟨i, e, he⟩ := heU q
    exact native_leaf_on_intrinsic_class a.splitting.unstable.toDistribution
      (U.leaf i) F.unstablePartition q e he (htU q)
  choose NS hNS using hNS
  choose NU hNU using hNU
  obtain ⟨K, T, hT, hTdim, hreal⟩ :=
    exists_continuous_complex_rank_one_subbundle a.splitting.unstable hRank
  have upgrades (q : Quotient F.unstablePartition) :
      letI := F.unstableTopology q; letI := F.unstableCharts q
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M)) := by
    let := F.unstableTopology q; let := F.unstableCharts q; let := hmU q
    have hi : Manifold.IsImmersion 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
        (Subtype.val : IntrinsicFoliationLeaf F.unstablePartition q → M) := by
      simpa only [hNU q] using (NU q).immersion
    apply nativeLeafComplexUpgrade_of_complex_tangent (k := 1)
      Subtype.val a.splitting.unstable hi (htU q) T
    intro z
    rw [htU q, hT]
    exact hreal z.val
  let upgrades' q := Classical.choice (upgrades q)
  let complexLeaves : IntrinsicComplexUnstableLeaves F := {
    real_dimension := rfl
    charts := fun q ↦ by
      letI := F.unstableTopology q; letI := F.unstableCharts q
      exact (upgrades' q).charts
    complex_manifold := fun q ↦ by
      let := F.unstableTopology q; let := F.unstableCharts q
      exact (upgrades' q).complex_manifold }
  let P : AnosovIntrinsicFoliationPresentation f a := {
    realCharts := realCoordinateRechart (d := d) (s := 2*d-2) (t := 2) B
    foliations := F
    complexLeaves := complexLeaves
    metric := m
    metric_topology := hm
    stable_asymptotic := by
      intro x y; rw [hRs]
      constructor
      · rintro ⟨i, z, w, rfl, rfl⟩
        exact (hrS i z _).mp ⟨w, rfl⟩
      · intro hxy
        obtain ⟨i, z, hz⟩ := S.cover x
        obtain ⟨w, hw⟩ := (hrS i z y).mpr (hz ▸ hxy)
        exact ⟨i, z, w, hz, hw⟩
    unstable_asymptotic := by
      intro x y; rw [hRu]
      constructor
      · rintro ⟨i, z, w, rfl, rfl⟩
        exact (hrU i z _).mp ⟨w, rfl⟩
      · intro hxy
        obtain ⟨i, z, hz⟩ := U.cover x
        obtain ⟨w, hw⟩ := (hrU i z y).mpr (hz ▸ hxy)
        exact ⟨i, z, w, hz, hw⟩
    stableSmooth := hmS
    unstableSmooth := hmU
    stableNative := NS
    unstableNative := NU
    stable_inclusion_eq := hNS
    unstable_inclusion_eq := hNU
    unstable_real_complex_compatible := fun q ↦ by
      let := F.unstableTopology q; let := F.unstableCharts q; let := hmU q
      exact native_complex_upgrade_identity_mdifferentiable (upgrades' q)
    unstable_holomorphic := fun q ↦ by
      let := F.unstableTopology q; let := F.unstableCharts q
      exact (upgrades' q).inclusion_holomorphic }
  exact ⟨P, hRs, hRu, heS, heU⟩
end HolomorphicAnosov.Ghys
