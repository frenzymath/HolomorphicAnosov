import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Geometry.Holonomy.CompleteLinearCoordinatesGlobalHolonomyG8
import HolomorphicAnosov.Geometry.Holonomy.NativeLinearCoordinateAssemblyG8
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgradeOfComplexTangent
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf
import HolomorphicAnosov.Geometry.NativePartitionAsymptoticRelationG10
import HolomorphicAnosov.Geometry.NativePairToTransverseG10
import HolomorphicAnosov.Geometry.FixedUnitProductNativePlaquesG10
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! This file constructs global unstable holonomy on the intrinsic stable leaves. (Zhang, Lemmas 2.4–2.10) -/

noncomputable section
open scoped ContDiff Manifold _root_.Topology
open Set Filter _root_.Topology

universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- Choose a source-selected HPS leaf through each original point and transport it to the literal original asymptotic carrier. -/
private theorem native_asymptotic_data_of_partition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
    (P : RealTangentDistribution 𝓘(ℝ, E) M) (F : HPS.LeafPartition P ι L r)
    (f : M ≃ₜ M)
    (hrange : ∀ i z, Set.range (F.leaf i).inclusion =
      {y | ForwardAsymptotic f ((F.leaf i).inclusion z) y}) (x : M) :
    ∃ i : ι, ∃ N : NativeAsymptoticLeafDatum 𝓘(ℝ, E) f P x, N.rank = r i ∧
      (letI := N.topology; letI := N.charts
       ∃ e : Diffeomorph 𝓘(ℝ, Fin (r i) → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
          (L i) (StableAsymptoticLeaf f x) ∞,
          ∀ z : L i, (e z).val = (F.leaf i).inclusion z) := by
  obtain ⟨i, z, hz⟩ := F.cover x
  have h := hrange i z
  rw [hz] at h
  obtain ⟨N, hN, e, he⟩ := native_asymptotic_datum_of_leaf_g15 P (F.leaf i) f x h
  exact ⟨i, N, hN, e, he⟩


/-- Construct the fixed-unit pair interface directly from the simultaneous source-native open product boxes printed in the stable-foliation theorem. -/
theorem native_source_product_pair_to_transverse {s t : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin s → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin t → ℝ) (Lu i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (Ls i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin t → ℝ) ∞ (Lu i)]
    (P Q : RealTangentDistribution 𝓘(ℝ, E) M)
    (Fs : HPS.LeafPartition P ιs Ls (fun _ ↦ s))
    (Fu : HPS.LeafPartition Q ιu Lu (fun _ ↦ t))
    (hsource : ∀ p : M, ∃ (Ds : TopologicalSpace.Opens (Fin s → ℝ))
      (Du : TopologicalSpace.Opens (Fin t → ℝ)) (O : TopologicalSpace.Opens M)
      (e : (Ds × Du) ≃ₜ O), p ∈ O ∧
      (∀ w : Du, ∃ i : ιs, ∃ V : TopologicalSpace.Opens (Ls i),
        ∃ c : Ds ≃ₜ V,
          ∀ z : Ds, (e (z, w)).val = (Fs.leaf i).inclusion (c z)) ∧
      (∀ z : Ds, ∃ i : ιu, ∃ V : TopologicalSpace.Opens (Lu i),
        ∃ c : Du ≃ₜ V,
          ∀ w : Du, (e (z, w)).val = (Fu.leaf i).inclusion (c w))) :
    ∃ F : TransverseContinuousFoliations.{u,u} s t M,
      (∀ x y, F.stablePartition x y ↔ ∃ i a b,
        (Fs.leaf i).inclusion a = x ∧ (Fs.leaf i).inclusion b = y) ∧
      (∀ x y, F.unstablePartition x y ↔ ∃ i a b,
        (Fu.leaf i).inclusion a = x ∧ (Fu.leaf i).inclusion b = y) ∧
      (∀ q : Quotient F.stablePartition,
        letI := F.stableTopology q; letI := F.stableCharts q
        ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
          LinearMap.range (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, E) Subtype.val z).toLinearMap =
            P z.val) ∧
      (∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q; letI := F.unstableCharts q
        ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
          LinearMap.range (mfderiv 𝓘(ℝ, Fin t → ℝ) 𝓘(ℝ, E) Subtype.val z).toLinearMap =
            Q z.val) ∧
      (∀ q : Quotient F.stablePartition,
        letI := F.stableTopology q; letI := F.stableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, Fin s → ℝ)
          (Ls i) (IntrinsicFoliationLeaf F.stablePartition q) ∞,
            ∀ z, (e z).val = (Fs.leaf i).inclusion z) ∧
      (∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q; letI := F.unstableCharts q
        ∃ i, ∃ e : Diffeomorph 𝓘(ℝ, Fin t → ℝ) 𝓘(ℝ, Fin t → ℝ)
          (Lu i) (IntrinsicFoliationLeaf F.unstablePartition q) ∞,
            ∀ z, (e z).val = (Fu.leaf i).inclusion z) := by
  classical
  have hboxes : ∀ p : M, ∃ B : TransverseFoliationBox s t M, p ∈ B.image ∧
      (∀ w, ∃ i : ιs, ∃ j : FoliationCoordinateDisk s → Ls i,
        IsOpenEmbedding j ∧ ∀ z, (B.chart (z, w)).val = (Fs.leaf i).inclusion (j z)) ∧
      (∀ z, ∃ i : ιu, ∃ j : FoliationCoordinateDisk t → Lu i,
        IsOpenEmbedding j ∧ ∀ w, (B.chart (z, w)).val = (Fu.leaf i).inclusion (j w)) := by
    intro p
    obtain ⟨Ds, Du, O, e, hp, hs, hu⟩ := hsource p
    exact fixed_unit_product_box_native_plaques_g10
      (fun i ↦ (Fs.leaf i).inclusion) (fun i ↦ (Fu.leaf i).inclusion)
      Ds Du O e ⟨p, hp⟩ hs hu
  let B : M → TransverseFoliationBox s t M := fun p ↦ (hboxes p).choose
  exact native_pair_to_transverse_foliations_g10 P Q Fs Fu B
    (fun p ↦ ⟨p, (hboxes p).choose_spec.1⟩)
    (fun p ↦ (hboxes p).choose_spec.2.1)
    (fun p ↦ (hboxes p).choose_spec.2.2)


/-- Global unstable holonomy on the original intrinsic stable leaves. -/
theorem global_unstable_holonomy
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (hd : 3 ≤ d) (f : Biholomorph d d M M) (A : AnosovDatum f)
    (hstable : ∀ x : M,
      Module.finrank ℝ (A.splitting.stable.toDistribution x) = 2) :
    ∃ B : ComplexModel d ≃L[ℝ] (Fin ((2 * (d - 1)) + 2) → ℝ),
      letI := realCoordinateRechart (M := M) B
      ∃ F : TransverseContinuousFoliations.{u, u} (2 * (d - 1)) 2 M,
        (∀ x y : M, F.stablePartition x y ↔ ForwardAsymptotic f.symm x y) ∧
        (∀ x y : M, F.unstablePartition x y ↔ ForwardAsymptotic f x y) ∧
        (∀ q : Quotient F.stablePartition,
          letI := F.stableTopology q
          letI := F.stableCharts q
          ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
            LinearMap.range
              (mfderiv 𝓘(ℝ, Fin (2 * (d - 1)) → ℝ) (realModel d)
                (fun w : IntrinsicFoliationLeaf F.stablePartition q ↦ w.val) z).toLinearMap =
              A.splitting.unstable.toDistribution z.val) ∧
        (∀ q : Quotient F.unstablePartition,
          letI := F.unstableTopology q
          letI := F.unstableCharts q
          ∀ z : IntrinsicFoliationLeaf F.unstablePartition q,
            LinearMap.range
              (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d)
                (fun w : IntrinsicFoliationLeaf F.unstablePartition q ↦ w.val) z).toLinearMap =
              A.splitting.stable.toDistribution z.val) ∧
        (∀ q : Quotient F.stablePartition,
          letI := F.stableTopology q
          letI := F.stableCharts q
          Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2 * (d - 1)) (d - 1)
            (fun w : IntrinsicFoliationLeaf F.stablePartition q ↦ w.val))) ∧
        ∃ C : IntrinsicComplexUnstableLeaves F,
          (∀ q : Quotient F.unstablePartition,
            letI := F.unstableTopology q
            letI := F.unstableCharts q
            ∃ U : NativeLeafComplexUpgrade (d := d) (r := 2) 1
                (fun w : IntrinsicFoliationLeaf F.unstablePartition q ↦ w.val),
              U.charts = C.charts q) ∧
          ∃ G : GlobalSHolonomyData F C,
            (∀ (q : Quotient F.stablePartition)
              (x y : IntrinsicFoliationLeaf F.stablePartition q)
              (γ η : Path x y) (z : F.ULeaf x.val),
              G.transport γ z = G.transport η z) ∧
            (∀ (q : Quotient F.stablePartition)
              (x : IntrinsicFoliationLeaf F.stablePartition q) (z : F.ULeaf x.val),
              G.transport (Path.refl x) z = z) ∧
            (∀ (q : Quotient F.stablePartition)
              (x y : IntrinsicFoliationLeaf F.stablePartition q) (γ : Path x y)
              (e : PathHolonomyRepresentative F γ 0 1),
              (Filter.Germ.ofFun (fun z : F.ULeaf x.val ↦ G.transport γ z) :
                Filter.Germ (𝓝 (F.uPoint x.val)) (F.ULeaf y.val)) =
                Filter.Germ.ofFun (fun z : F.ULeaf x.val ↦
                  castIntrinsicULeaf F (congrArg Subtype.val γ.target)
                    (e.map (castIntrinsicULeaf F
                      (congrArg Subtype.val γ.source).symm z)))) := by
  classical
  let originalMetric : MetricSpace M := inferInstance
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (realModel d) M
  let canonicalMetric : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hmetric (g : M → M) (x y : M) :
      @ForwardAsymptotic M originalMetric g x y ↔
        @ForwardAsymptotic M canonicalMetric g x y := by
    let e : @Homeomorph M M originalMetric.toUniformSpace.toTopologicalSpace
        canonicalMetric.toUniformSpace.toTopologicalSpace := Homeomorph.refl M
    exact @paired_distance_zero_iff_of_homeomorph M M originalMetric canonicalMetric
      inferInstance inferInstance e (fun n ↦ g^[n] y) (fun n ↦ g^[n] x)
  let : MetricSpace M := canonicalMetric
  obtain ⟨h,hh⟩ := OneFormBundle.original_smooth_tangent_metric_exists (d := d) (M := M)
  obtain ⟨K,rate,hK,hrate,hs,hu⟩ := OneFormBundle.original_all_iterates_hermitian f A h hh
  obtain ⟨s,t,hst,S,U,hranks,hSr,hUr,hfamily⟩ :=
    stableFoliations f h hh A.splitting K rate hK hrate hs hu
  have hs1 : s = 1 := by
    let x : M := Classical.arbitrary M
    have hx := hstable x
    rw [← hSr x,LinearEquiv.finrank_map_eq,
      (((S.toDistribution x).restrictScalarsEquiv ℝ).restrictScalars ℝ).finrank_eq,
      finrank_real_of_complex,(hranks x).1] at hx
    omega
  subst s
  have ht : t = d-1 := by omega
  subst t
  have hrank : HasComplexRankOne A.splitting.stable.toDistribution :=
    fun x ↦ ⟨S.toDistribution x,(hranks x).1,hSr x⟩
  have hsplit (x : M) : IsCompl (S.toDistribution x) (U.toDistribution x) := by
    apply (Submodule.isCompl_restrictScalars_iff ℝ).mp
    apply (Submodule.orderIsoMapComap (complexTangentToReal d x).toLinearEquiv).isCompl_iff.mpr
    change IsCompl (((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap)
      (((U.toDistribution x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap)
    rw [hSr,hUr]
    exact A.splitting.isCompl x
  obtain ⟨U',hUhol,hU'real⟩ := rank_one_stable_holomorphic_unstable (by omega) f A hrank
  have hUeq : U' = U.toDistribution := by
    funext x
    apply Submodule.restrictScalars_injective ℝ ℂ _
    apply Submodule.map_injective_of_injective (complexTangentToReal d x).injective
    exact (hU'real x).trans (hUr x).symm
  subst U'
  obtain ⟨_,hU,nabla,hncont,hncompat,hninv,_,_⟩ :=
    lemma_2_2_invariant_connection hd f A hrank U.toDistribution hUr hUhol
  have hlocal := Paper.Zhang.transverse_parallel_coordinates hd M f A hrank U.toDistribution
    hUr hU nabla hncont hncompat hninv
  rcases hfamily with ⟨ιs,ιu,Ls,Lu,ts,tu,hfamily⟩
  let : ∀ i, TopologicalSpace (Ls i) := ts
  let : ∀ i, TopologicalSpace (Lu i) := tu
  rcases hfamily with ⟨cs,cu,hfamily⟩
  let : ∀ i, ChartedSpace (Fin 2 → ℝ) (Ls i) := cs
  let : ∀ i, ChartedSpace (Fin (2*(d-1)) → ℝ) (Lu i) := cu
  rcases hfamily with ⟨ms,mu,Fs,Fu,hstableAsymptotic,hunstableAsymptotic,
    hstableEuclidean,hunstableEuclidean,hstableAction,hunstableAction,
    hboxes,hproducts,hstableJets,hunstableJets,hstableComplex,hunstableComplex⟩
  let : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Ls i) := ms
  let : ∀ i, IsManifold 𝓘(ℝ, Fin (2*(d-1)) → ℝ) ∞ (Lu i) := mu
  let valid (V : TopologicalSpace.Opens M)
      (σ : (x : M) → QuotientLineConnection.Fibre U.toDistribution x) (τ : M → ℂ) : Prop :=
    QuotientLineConnection.IsHolomorphicSection U.toDistribution V σ ∧
    (∀ x ∈ V, σ x ≠ 0) ∧ QuotientLineConnection.IsParallelOn nabla V σ ∧
    ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ τ V ∧
    ∀ x ∈ V, (∀ v : TangentSpace (complexModel d) x,
      QuotientLineConnection.projection U.toDistribution x v =
        Paper.Zhang.transverseScalarDifferential τ x v • σ x) ∧
      (Paper.Zhang.transverseScalarDifferential τ x).ker = U.toDistribution x
  have hbox (p : M) : ∃ D : TransverseFoliationBox (2*(d-1)) 2 M,
      p ∈ D.image ∧
      (∀ w, ∃ i : ιu, ∃ j : FoliationCoordinateDisk (2*(d-1)) → Lu i,
        IsOpenEmbedding j ∧ ∀ z, (D.chart (z,w)).val = (Fu.leaf i).inclusion (j z)) ∧
      (∀ z, ∃ i : ιs, ∃ j : FoliationCoordinateDisk 2 → Ls i,
        IsOpenEmbedding j ∧ ∀ w, (D.chart (z,w)).val = (Fs.leaf i).inclusion (j w)) ∧
      ∃ (V : TopologicalSpace.Opens M)
        (σ : (x : M) → QuotientLineConnection.Fibre U.toDistribution x) (τ : M → ℂ),
        valid V σ τ ∧ D.image ⊆ V := by
    obtain ⟨V,hpV,σ,τ,hσ,hσ0,hσpar,hτ,_,hπτ⟩ := hlocal p
    obtain ⟨Ds,Du,O,e,hp,_,_,hps,hpu,_,_⟩ := hproducts p
    let e' : (Du × Ds) ≃ₜ O := (Homeomorph.prodComm Du Ds).trans e
    have hfirst : ∀ w : Ds, ∃ i : ιu, ∃ W : TopologicalSpace.Opens (Lu i),
        ∃ c : Du ≃ₜ W, ∀ z : Du, (e' (z,w)).val = (Fu.leaf i).inclusion (c z) := by
      intro w
      obtain ⟨i,W,c,hc⟩ := hpu w
      exact ⟨i,W,c,hc⟩
    have hsecond : ∀ z : Du, ∃ i : ιs, ∃ W : TopologicalSpace.Opens (Ls i),
        ∃ c : Ds ≃ₜ W, ∀ w : Ds, (e' (z,w)).val = (Fs.leaf i).inclusion (c w) := by
      intro z
      obtain ⟨i,W,c,hc⟩ := hps z
      exact ⟨i,W,c,hc⟩
    obtain ⟨D,hpD,hDV,hDU,hDS⟩ := fixed_unit_product_box_native_plaques_within
      (fun i ↦ (Fu.leaf i).inclusion) (fun i ↦ (Fs.leaf i).inclusion)
      Du Ds O e' ⟨p,hp⟩ V V.isOpen hpV hfirst hsecond
    exact ⟨D,hpD,hDU,hDS,V,σ,τ,⟨hσ,hσ0,hσpar,hτ,hπτ⟩,hDV⟩
  choose boxes hboxesCover hboxesU hboxesS V σ τ hvalid hboxV using hbox
  let B : ComplexModel d ≃L[ℝ] (Fin ((2*(d-1))+2) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [finrank_real_of_complex]
      simp only [ComplexModel,Module.finrank_pi,Fintype.card_fin]
      omega)
  refine ⟨B,?_⟩
  let := realCoordinateRechart (M := M) B
  obtain ⟨F,hRs,hRu,hTanS,hTanU,hIdS,hIdU,hManS,hManU,hPres⟩ :=
    native_pair_to_transverse_foliations_with_smooth_leaves
      A.splitting.unstable.toDistribution A.splitting.stable.toDistribution Fu Fs boxes
      (fun p ↦ ⟨p,hboxesCover p⟩) hboxesU hboxesS
  have hFs (x y : M) : F.stablePartition x y ↔ ForwardAsymptotic f.symm x y :=
    (hRs x y).trans (native_partition_asymptotic_relation_g10
      A.splitting.unstable.toDistribution Fu f.toHomeomorph.symm hunstableAsymptotic x y)
  have hFu (x y : M) : F.unstablePartition x y ↔ ForwardAsymptotic f x y :=
    (hRu x y).trans (native_partition_asymptotic_relation_g10
      A.splitting.stable.toDistribution Fs f.toHomeomorph hstableAsymptotic x y)
  have hUpgradeS (q : Quotient F.stablePartition) :
      letI := F.stableTopology q
      letI := F.stableCharts q
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2*(d-1)) (d-1)
        (fun w : IntrinsicFoliationLeaf F.stablePartition q ↦ w.val)) := by
    let := F.stableTopology q
    let := F.stableCharts q
    let := hManS q
    obtain ⟨i,e,he⟩ := hIdS q
    have hinc : (Fu.leaf i).inclusion ∘ e.symm = Subtype.val := by
      funext z
      exact (he (e.symm z)).symm.trans (congrArg Subtype.val (e.apply_symm_apply z))
    have him := immersion_precompose_diffeomorph_global (realModel d)
      (Fu.leaf i).inclusion e.symm (Fu.leaf i).immersion
    rw [hinc] at him
    exact nativeLeafComplexUpgrade_of_complex_tangent Subtype.val A.splitting.unstable
      him (hTanS q) U (fun z ↦ (hUr z.val).trans (hTanS q z).symm)
  have hUpgradeU (q : Quotient F.unstablePartition) :
      letI := F.unstableTopology q
      letI := F.unstableCharts q
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (fun w : IntrinsicFoliationLeaf F.unstablePartition q ↦ w.val)) := by
    let := F.unstableTopology q
    let := F.unstableCharts q
    let := hManU q
    obtain ⟨i,e,he⟩ := hIdU q
    have hinc : (Fs.leaf i).inclusion ∘ e.symm = Subtype.val := by
      funext z
      exact (he (e.symm z)).symm.trans (congrArg Subtype.val (e.apply_symm_apply z))
    have him := immersion_precompose_diffeomorph_global (realModel d)
      (Fs.leaf i).inclusion e.symm (Fs.leaf i).immersion
    rw [hinc] at him
    exact nativeLeafComplexUpgrade_of_complex_tangent Subtype.val A.splitting.stable
      him (hTanU q) S (fun z ↦ (hSr z.val).trans (hTanU q z).symm)
  let upgrades q := (hUpgradeU q).some
  let C : IntrinsicComplexUnstableLeaves F :=
    { real_dimension := rfl
      charts := fun q ↦ letI := F.unstableTopology q; letI := F.unstableCharts q
        (upgrades q).charts
      complex_manifold := fun q ↦ letI := F.unstableTopology q; letI := F.unstableCharts q
        (upgrades q).complex_manifold }
  have hSrfun : complexStableRealDistribution S = A.splitting.stable.toDistribution :=
    funext hSr
  have nativeStableDatum : ∃ N : NativeComplexStableLeafDatum f.toHomeomorph S ιs Ls,
      ∀ i, (N.partition.leaf i).inclusion = (Fs.leaf i).inclusion := by
    generalize hP : A.splitting.stable.toDistribution = P at Fs hstableAsymptotic hstableComplex hboxes hstableJets ⊢
    have hPS : P = complexStableRealDistribution S := hP.symm.trans hSrfun.symm
    clear hP
    subst P
    rcases hboxes with ⟨βs,βu,Ts,Tu,tts,ttu,⟨Bs⟩,⟨Bu⟩⟩
    let : ∀ b, TopologicalSpace (Ts b) := tts
    let : ∀ b, TopologicalSpace (Tu b) := ttu
    have hupgrade : ∀ i, ∃ up : NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (Fs.leaf i).inclusion,
        letI := up.charts
        ∀ z : Ls i, (mfderiv (complexModel 1) (complexModel d)
          (Fs.leaf i).inclusion z).range = S.toDistribution ((Fs.leaf i).inclusion z) := by
      intro i
      rcases hstableComplex i with ⟨c,hm,him,up,hc,htangent⟩
      subst c
      exact ⟨up,htangent⟩
    choose upgrade tangent using hupgrade
    exact ⟨{ partition := Fs
             complexUpgrade := upgrade
             asymptotic := hstableAsymptotic
             complex_tangent := tangent
             boxIndex := βs
             transversal := Ts
             transversalTopology := tts
             boxes := Bs
             local_first_jets := hstableJets },fun _ ↦ rfl⟩
  obtain ⟨nativeStable,hnativeInc⟩ := nativeStableDatum
  let : ∀ x : M, NormedAddCommGroup (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
  let : ∀ x : M, NormedSpace ℂ (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
  have hcoords := Paper.Zhang.complete_stable_coordinates hd M f A hrank S hSr U.toDistribution hUr
    hU nabla hncont hncompat hninv ιs Ls nativeStable
  refine ⟨F,(fun x y ↦ (hFs x y).trans (hmetric f.symm x y).symm),
    (fun x y ↦ (hFu x y).trans (hmetric f x y).symm),hTanS,hTanU,hUpgradeS,C,?_,?_⟩
  · intro q
    exact ⟨upgrades q,rfl⟩
  have hpaths (q : Quotient F.stablePartition)
      (x y : IntrinsicFoliationLeaf F.stablePartition q) (γ η : Path x y) :
      Nonempty (Path.Homotopy γ η) := by
    let := F.stableTopology q
    let := F.stableCharts q
    obtain ⟨i,e,he⟩ := hIdS q
    obtain ⟨r⟩ := hunstableEuclidean i
    let : ContractibleSpace (IntrinsicFoliationLeaf F.stablePartition q) :=
      (e.symm.toHomeomorph.trans r.symm.toHomeomorph).contractibleSpace
    exact SimplyConnectedSpace.paths_homotopic γ η
  let : ∀ i, ChartedSpace (ComplexModel 1) (Ls i) :=
    fun i ↦ (nativeStable.complexUpgrade i).charts
  let : ∀ i, IsManifold (complexModel 1) ∞ (Ls i) :=
    fun i ↦ (nativeStable.complexUpgrade i).complex_manifold
  let inc := fun i ↦ (nativeStable.partition.leaf i).inclusion
  obtain ⟨φraw,_,_,_,hzraw,_,hgermraw,_⟩ := hcoords
  have hreceive (x : M) :
      letI := C.charts (Quotient.mk F.unstablePartition x)
      ∃ i : ιs, ∃ e : Biholomorph 1 1 (F.ULeaf x) (Ls i),
        ∀ z, inc i (e z) = z.val := by
    let q := Quotient.mk F.unstablePartition x
    let := F.unstableCharts q
    let := C.charts q
    let := C.complex_manifold q
    obtain ⟨i,e,he⟩ := hIdU q
    have hi : ∀ z : F.ULeaf x, inc i (e.symm z) = z.val := by
      intro z
      dsimp only [inc]
      rw [hnativeInc]
      exact (he (e.symm z)).symm.trans (congrArg Subtype.val (e.apply_symm_apply z))
    obtain ⟨E,hE⟩ := biholomorph_of_immersed_homeomorph
      (fun z : F.ULeaf x ↦ z.val) (inc i)
      (upgrades q).inclusion_holomorphic (nativeStable.complexUpgrade i).inclusion_holomorphic
      (upgrades q).inclusion_immersion (nativeStable.complexUpgrade i).inclusion_immersion
      e.symm.toHomeomorph hi
    refine ⟨i,E,?_⟩
    intro z
    change inc i (E.toHomeomorph z) = z.val
    rw [hE]
    exact hi z
  choose idx receive hreceive using hreceive
  let base (x : M) := inc (idx x) (receive x (F.uPoint x))
  have hbase (x : M) : base x = x := hreceive x (F.uPoint x)
  let scalar (x : M) : S.toDistribution (base x) ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using (hranks (base x)).1)
  let φ (x : M) : letI := C.charts (Quotient.mk F.unstablePartition x)
      Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ) (F.ULeaf x) ℂ ∞ :=
    letI := C.charts (Quotient.mk F.unstablePartition x)
    let ψ : Diffeomorph (complexModel 1) 𝓘(ℂ, S.toDistribution (base x))
        (Ls (idx x)) (S.toDistribution (base x)) ∞ :=
      φraw (idx x) (receive x (F.uPoint x))
    ((receive x).trans ψ).trans (scalar x).toDiffeomorph
  have hzero (x : M) : φ x (F.uPoint x) = 0 := by
    change scalar x (φraw (idx x) (receive x (F.uPoint x)) (receive x (F.uPoint x))) = 0
    rw [hzraw,map_zero]
  have hnormalized (V : TopologicalSpace.Opens M)
      (σ : (x : M) → QuotientLineConnection.Fibre U.toDistribution x) (τ : M → ℂ)
      (hv : valid V σ τ) (x : M) (hx : x ∈ V) :
      ∃ D : ℂ ≃L[ℂ] ℂ,
        ∀ᶠ p in 𝓝 (F.uPoint x), φ x p = D.symm (τ p.val - τ x) := by
    have hxb : base x ∈ V := (hbase x).symm ▸ hx
    have hinv := LinearHolonomyPreparation.restricted_differential_invertible
      (S.toDistribution (base x)) (U.toDistribution (base x))
      (Paper.Zhang.transverseScalarDifferential τ (base x))
      (hranks (base x)).1 (hsplit (base x)) (hv.2.2.2.2 (base x) hxb).2
    obtain ⟨D,hD⟩ := hinv
    refine ⟨(scalar x).symm.trans D,?_⟩
    have hg := hgermraw V σ τ
      ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,
        (fun z hz ↦ (hv.2.2.2.2 z hz).1),(fun z hz ↦ (hv.2.2.2.2 z hz).2)⟩
      (idx x) (receive x (F.uPoint x)) hxb
    let := C.charts (Quotient.mk F.unstablePartition x)
    have hg' := (receive x).continuous.continuousAt.tendsto.eventually hg
    filter_upwards [hg'] with p hp
    change scalar x (φraw (idx x) (receive x (F.uPoint x)) (receive x p)) = _
    rw [hp.2]
    change scalar x ((localStableCoordinateDerivative S.toDistribution τ (base x)).inverse
      (τ (inc (idx x) (receive x p)) - τ (base x))) = _
    have hD' : D.toContinuousLinearMap = localStableCoordinateDerivative S.toDistribution τ (base x) := hD
    rw [← hD',ContinuousLinearMap.inverse_equiv,hreceive,congrArg τ (hbase x)]
    rfl
  have hrealS (q : Quotient F.stablePartition) :
      letI := F.stableTopology q; letI := F.stableCharts q
      ContMDiff 𝓘(ℝ, Fin (2*(d-1)) → ℝ) (realModel d) ∞
        (fun z : IntrinsicFoliationLeaf F.stablePartition q ↦ z.val) := by
    let := F.stableTopology q
    let := F.stableCharts q
    obtain ⟨i,e,he⟩ := hIdS q
    have hinc : (Fu.leaf i).inclusion ∘ e.symm = Subtype.val := by
      funext z
      exact (he (e.symm z)).symm.trans (congrArg Subtype.val (e.apply_symm_apply z))
    rw [← hinc]
    exact (Fu.leaf i).immersion.contMDiff.comp e.symm.contMDiff
  have hloc_of_boxes (hpres : ∀ b : F.boxIndex, ∃ a : M, F.box b = boxes a) :
      ∀ (x y : M) (e : LocalPlaqueTransport F x y),
        ∃ D : ℂ ≃L[ℂ] ℂ,
          ∀ᶠ z in 𝓝 (F.uPoint x), φ y (e.map z) = D (φ x z) := by
    intro x y e
    obtain ⟨a,ha⟩ := hpres e.box
    have hbox : (F.box e.box).image ⊆ V a := by
      rw [ha]
      exact hboxV a
    have hx : x ∈ V a := by
      rw [← e.first_point]
      exact hbox ((F.box e.box).chart (e.first,e.transverse)).property
    have hy : y ∈ V a := by
      rw [← e.second_point]
      exact hbox ((F.box e.box).chart (e.second,e.transverse)).property
    have hconst := HolonomyTransverseConstancy.plaque_transport_scalar_germ F x y e (τ a)
      Set.univ isOpen_univ (Set.mem_univ _) (fun w _ ↦
        intrinsic_plaque_transverse_eq F U hManS hrealS
          (fun q z ↦ (hTanS q z).trans (hUr z.val).symm)
          (V a) (τ a) (hvalid a).2.2.2.1
          (fun z hz ↦ ((hvalid a).2.2.2.2 z hz).2) e.box hbox w e.second e.first)
    obtain ⟨Dx,hDx⟩ := hnormalized (V a) (σ a) (τ a) (hvalid a) x hx
    obtain ⟨Dy,hDy⟩ := hnormalized (V a) (σ a) (τ a) (hvalid a) y hy
    refine ⟨Dx.trans Dy.symm,?_⟩
    apply LinearHolonomyPreparation.normalized_germ_conjugacy
      (F.uPoint x) (F.uPoint y) e.map (e.map.continuousAt e.source_point) e.map_point
      (fun z : F.ULeaf x ↦ τ a z.val) (fun z : F.ULeaf y ↦ τ a z.val) (τ a x)
      Dx Dy (φ x) (φ y) hDx
    · simpa only [hconst.1] using hDy
    · exact hconst.2.mono (fun _ hp ↦ hp.2)
  exact global_holonomy_of_complete_linear_coordinates F C φ hzero (hloc_of_boxes hPres) hpaths


end HolomorphicAnosov
