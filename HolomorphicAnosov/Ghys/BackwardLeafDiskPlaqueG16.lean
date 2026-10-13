import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import HolomorphicAnosov.Ghys.NativeHolomorphicCurveTangency
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter Bundle Manifold MeasureTheory TopologicalSpace
open scoped ContDiff Manifold Bundle Topology ENNReal
universe u
attribute [local instance] complex_isManifold_real

/-- Backward iterates of a compact convex coordinate disk in an unstable leaf eventually lie in a
single flowbox core and have one common transverse coordinate throughout the disk. (Ghys, Lemma
3.3, pp.592–593) -/
theorem backward_leaf_disk_one_plaque {d : ℕ} {M ι : Type u} {J T : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (L : ι → Type u) [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    [TopologicalSpace T]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (hhol : ∀ i, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion)
    (perm : ι → ι)
    (G : ∀ i, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (perm i)) ∞)
    (hG : ∀ i x, (U.leaf (perm i)).inclusion (G i x) = f.symm ((U.leaf i).inclusion x))
    (boxes : J → OpenPartialHomeomorph M (ℂ × T)) (O : J → Opens T)
    (label : ∀ j, O j → ι) (branch : ∀ j t, Opens (L (label j t)))
    (param : ∀ j t, {z : ℂ // (z, t.val) ∈ (boxes j).target} ≃ₜ branch j t)
    (htrans : ∀ j p, p ∈ (boxes j).target → p.2 ∈ O j)
    (hparam : ∀ j (t : O j) (z : {z : ℂ // (z, t.val) ∈ (boxes j).target}),
      (boxes j).symm (z.val, t.val) = (U.leaf (label j t)).inclusion (param j t z).val)
    (cores : J → Set M) (hcore : ∀ j, cores j ⊆ (boxes j).source)
    (hcover : (univ : Set M) ⊆ ⋃ j, interior (cores j))
    (i : ι) (c : LeafChart (L i)) (K : Set ℂ) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKc : K ⊆ c.val.target) (p : ℂ) (hp : p ∈ K) :
    ∀ᶠ n in atTop, ∃ (j : J) (t : O j), ∀ z ∈ K,
      (f.symm : M → M)^[n] ((U.leaf i).inclusion (c.val.symm z)) ∈ cores j ∧
      (boxes j ((f.symm : M → M)^[n] ((U.leaf i).inclusion (c.val.symm z)))).2 = t.val := by
  have curveDistanceBound {E : Type} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
      (γ : ℝ → M) (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc 0 1))
      (F : M → M) (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 F)
      (B : ℝ)
      (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F (γ t)
          (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ (Icc 0 1) t 1)‖ ≤ B) :
      riemannianEDist 𝓘(ℝ, E) (F (γ 0)) (F (γ 1)) ≤ ENNReal.ofReal B := by
    apply (riemannianEDist_le_pathELength (hF.comp_contMDiffOn hγ) rfl rfl zero_le_one).trans
    rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal B := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have hchain := mfderiv_comp_mfderivWithin t
          (hF.mdifferentiable one_ne_zero (γ t))
          (hγ.mdifferentiableOn one_ne_zero t ht)
          ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
        rw [hchain, ContinuousLinearMap.comp_apply]
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hbound t ht)
      _ = ENNReal.ofReal B := by simp
  have compactDerivativeBound {E F : Type} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
      [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
      (s : Set F) (hs : IsOpen s) (ψ : F → M)
      (hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 ψ s)
      (K V : Set F) (hK : IsCompact K) (hV : IsCompact V) (hKs : K ⊆ s) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ∀ v ∈ V,
        ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ z v‖ ≤ R := by
    have hv : ContinuousOn (fun p : F × F ↦
        (⟨ψ p.1, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M))
        (s ×ˢ univ) := by
      have hmaps : MapsTo (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm
          (s ×ˢ univ) (Bundle.TotalSpace.proj ⁻¹' s) := fun _ hp ↦ hp.1
      have hc := (hψ.continuousOn_tangentMapWithin le_rfl hs.uniqueMDiffOn).comp
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm.continuous.continuousOn
        hmaps
      apply hc.congr
      intro p hp
      change (⟨ψ p.1, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M) =
        ⟨ψ p.1, mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, E) ψ s p.1 p.2⟩
      rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hp.1)]
    have hn : ContinuousOn (fun p : F × F ↦
        ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ p.1 p.2‖) (s ×ˢ univ) := by
      simpa only [norm_eq_sqrt_real_inner] using (hv.inner_bundle hv).sqrt
    obtain ⟨R, hR⟩ := (hK.prod hV).exists_bound_of_continuousOn
      (hn.mono (by intro p hp; exact ⟨hKs hp.1, mem_univ _⟩))
    refine ⟨max R 0, le_max_right _ _, ?_⟩
    intro z hz v hv
    have hh : ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ z v‖ ≤ R := by
      simpa only [Real.norm_eq_abs, abs_norm] using hR (z, v) ⟨hz, hv⟩
    exact hh.trans (le_max_left _ _)
  have uniformCoordinateContraction {E F : Type} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
      [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
      (s : Set F) (hs : IsOpen s) (ψ : F → M)
      (hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 ψ s)
      (K : Set F) (hK : IsCompact K) (hconv : Convex ℝ K) (hKs : K ⊆ s)
      (p : F) (hp : p ∈ K) (f : ℕ → M → M)
      (hf : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (f n))
      (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
      (hbound : ∀ n z, z ∈ K → ∀ v : F,
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (f n) (ψ z)
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ z v)‖ ≤
          a n * ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ z v‖) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ n z, z ∈ K →
        riemannianEDist 𝓘(ℝ, E) (f n (ψ p)) (f n (ψ z)) ≤ ENNReal.ofReal (a n * R) := by
    obtain ⟨R, hR, hspeed⟩ := compactDerivativeBound s hs ψ hψ K ((fun z ↦ z - p) '' K)
      hK (hK.image (continuous_id.sub continuous_const)) hKs
    refine ⟨R, hR, ?_⟩
    intro n z hz
    let η : ℝ →ᵃ[ℝ] F := AffineMap.lineMap p z
    have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ, F) 1 η :=
      contMDiff_iff_contDiff.mpr (AffineMap.contDiff_lineMap p z)
    have hmemK : MapsTo η (Icc 0 1) K := by
      intro t ht
      exact hconv.segment_subset hp hz (by rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩)
    have hmem : MapsTo η (Icc 0 1) s := fun t ht ↦ hKs (hmemK ht)
    have hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 (ψ ∘ η) (Icc 0 1) :=
      hψ.comp hη.contMDiffOn hmem
    have hvel : ∀ t ∈ Icc (0 : ℝ) 1,
        mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) (ψ ∘ η) (Icc 0 1) t (1 : ℝ) =
          mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ (η t) (z - p) := by
      intro t ht
      have hchain := mfderiv_comp_mfderivWithin t
        ((hψ (η t) (hmem ht)).contMDiffAt (hs.mem_nhds (hmem ht)) |>.mdifferentiableAt one_ne_zero)
        (hη.contMDiffOn.mdifferentiableOn one_ne_zero t ht)
        ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
      have hder : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, F) η (Icc 0 1) t (1 : ℝ) = z - p := by
        rw [mfderivWithin_eq_fderivWithin]
        rw [(AffineMap.hasDerivWithinAt_lineMap (a := p) (b := z)).hasFDerivWithinAt.fderivWithin
          (uniqueDiffOn_Icc zero_lt_one t ht)]
        exact one_smul ℝ (z - p)
      exact (congrArg (fun f ↦ f (1 : ℝ)) hchain).trans
        (congrArg (fun v ↦ mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ (η t) v) hder)
    have hd := curveDistanceBound (ψ ∘ η) hγ (f n) (hf n) (a n * R) (by
      intro t ht
      change ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (f n) (ψ (η t))
        (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) (ψ ∘ η) (Icc 0 1) t 1)‖ ≤ _
      have he := congrArg (fun v : TangentSpace 𝓘(ℝ, E) (ψ (η t)) ↦
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (f n) (ψ (η t)) v‖) (hvel t ht)
      apply he.trans_le
      exact (hbound n (η t) (hmemK ht) (z - p)).trans
        (mul_le_mul_of_nonneg_left (hspeed (η t) (hmemK ht) (z - p) ⟨z, hz, rfl⟩) (ha n)))
    simpa [η, Function.comp_apply] using hd
  have leafCoordinateTangency {d : ℕ} {M L : Type u} [TopologicalSpace M]
      [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
      [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
      [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ L]
      [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
      {D : RealTangentDistribution (realModel d) M}
      (N : HPS.NativeLeaf (r := 2) D L)
      (hhol : ContMDiff 𝓘(ℂ) (complexModel d) ∞ N.inclusion)
      (g : ℂ → L) (z : ℂ) (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ g z) :
      ContMDiffAt 𝓘(ℝ, ℂ) (realModel d) ∞ (N.inclusion ∘ g) z ∧
        ∀ v : TangentSpace 𝓘(ℝ, ℂ) z,
          mfderiv 𝓘(ℝ, ℂ) (realModel d) (N.inclusion ∘ g) z v ∈ D (N.inclusion (g z)) := by
    have hc := hhol.contMDiffAt.comp z hg
    have hr : ContMDiffAt 𝓘(ℝ, ℂ) (realModel d) ∞ (N.inclusion ∘ g) z := by
      obtain ⟨hcont, hsmooth⟩ := contMDiffAt_iff.mp hc
      exact contMDiffAt_iff.mpr ⟨hcont, hsmooth.restrict_scalars ℝ⟩
    have hgr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞ g z :=
      (ContMDiffAt.iff_comp_isImmersionAt (N.immersion.isImmersionAt (g z))).mpr
        ⟨hg.continuousAt, hr⟩
    refine ⟨hr, fun v ↦ ?_⟩
    rw [mfderiv_comp z (N.immersion.contMDiff.mdifferentiable (by simp) _)
      (hgr.mdifferentiableAt (by simp)), ← N.tangent]
    exact ⟨mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) g z v, rfl⟩
  have originalCoordinateContraction {d : ℕ} {M L : Type u} [TopologicalSpace M]
      [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M]
      [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
      [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ L]
      [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
      (f : Biholomorph d d M M) (a : AnosovDatum f)
      (N : HPS.NativeLeaf (r := 2) a.splitting.unstable.toDistribution L)
      (hhol : ContMDiff 𝓘(ℂ) (complexModel d) ∞ N.inclusion)
      (c : LeafChart L) (K : Set ℂ) (hK : IsCompact K) (hconv : Convex ℝ K)
      (hKc : K ⊆ c.val.target) (p : ℂ) (hp : p ∈ K) :
      let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
        ⟨a.metric.toRiemannianMetric⟩
      ∃ C q R : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ 0 ≤ R ∧ ∀ n z, z ∈ K →
        riemannianEDist (realModel d)
          ((f.symm : M → M)^[n] (N.inclusion (c.val.symm p)))
          ((f.symm : M → M)^[n] (N.inclusion (c.val.symm z))) ≤
            ENNReal.ofReal (C * q ^ n * R) := by
    let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (ComplexModel d)
        (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.inner, a.metric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    obtain ⟨C, q, hC, hq, hq1, _, hdecay⟩ := fixed_block_uniform_anosov_estimates f a
    let ψ := N.inclusion ∘ c.val.symm
    have hc (z : ℂ) (hz : z ∈ c.val.target) :=
      leafCoordinateTangency N hhol c.val.symm z
        (contMDiffAt_symm_of_mem_maximalAtlas c.property hz)
    have hψ : ContMDiffOn 𝓘(ℝ, ℂ) (realModel d) 1 ψ c.val.target := by
      intro z hz
      exact ((hc z hz).1.of_le (by simp)).contMDiffWithinAt
    obtain ⟨R, hR, hbound⟩ := uniformCoordinateContraction c.val.target c.val.open_target ψ hψ
      K hK hconv hKc p hp (fun n ↦ (f.symm : M → M)^[n])
      (fun n ↦ (f.toReal.symm.contMDiff.iterate n).of_le (by simp))
      (fun n ↦ C * q ^ n) (fun n ↦ mul_nonneg hC.le (pow_nonneg hq.le n))
      (fun n z hz v ↦ hdecay n (ψ z) _ ((hc z (hKc hz)).2 v))
    exact ⟨C, q, R, hC, hq, hq1, hR, hbound⟩
  have commonReceivingCoreEDist {X : Type} {Y : Type u} {ι : Type} [EMetricSpace Y] [CompactSpace Y]
      (K : ι → Set Y) (hcover : (univ : Set Y) ⊆ ⋃ i, interior (K i))
      (f : ℕ → X → Y) (V : Set X) (x : X) (C q R : ℝ)
      (hq : 0 ≤ q) (hq1 : q < 1)
      (hbound : ∀ n z, z ∈ V → edist (f n z) (f n x) ≤ ENNReal.ofReal (C * q ^ n * R)) :
      ∀ᶠ n in atTop, ∃ i, MapsTo (f n) V (K i) := by
    obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_emetric isCompact_univ
      (fun i ↦ isOpen_interior (s := K i)) hcover
    have hlim : Tendsto (fun n : ℕ ↦ C * q ^ n * R) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).const_mul C).mul_const R
    have helim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C * q ^ n * R)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hlim
    filter_upwards [helim.eventually_lt_const hδ] with n hn
    obtain ⟨i, hi⟩ := hball (f n x) (mem_univ _)
    exact ⟨i, fun z hz ↦ interior_subset (hi ((hbound n z hz).trans_lt hn))⟩
  have originalReceivingCore {d : ℕ} {M L : Type u} {J : Type} [TopologicalSpace M]
      [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M]
      [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
      [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ L]
      [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
      (f : Biholomorph d d M M) (a : AnosovDatum f)
      (N : HPS.NativeLeaf (r := 2) a.splitting.unstable.toDistribution L)
      (hhol : ContMDiff 𝓘(ℂ) (complexModel d) ∞ N.inclusion)
      (c : LeafChart L) (K : Set ℂ) (hK : IsCompact K) (hconv : Convex ℝ K)
      (hKc : K ⊆ c.val.target) (p : ℂ) (hp : p ∈ K)
      (cores : J → Set M) (hcover : (univ : Set M) ⊆ ⋃ j, interior (cores j)) :
      ∀ᶠ n in atTop, ∃ j, ∀ z ∈ K,
        (f.symm : M → M)^[n] (N.inclusion (c.val.symm z)) ∈ cores j := by
    let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (ComplexModel d)
        (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.inner, a.metric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (realModel d) M
    obtain ⟨C, q, R, _, hq, hq1, _, hbound⟩ :=
      originalCoordinateContraction f a N hhol c K hK hconv hKc p hp
    exact commonReceivingCoreEDist cores hcover
      (fun n z ↦ (f.symm : M → M)^[n] (N.inclusion (c.val.symm z))) K p C q R
      hq.le hq1 (by
        intro n z hz
        rw [edist_comm]
        exact hbound n z hz)
  have plaqueConstancy {M ι : Type u} {E T X : Type} [TopologicalSpace M] [TopologicalSpace E]
      [TopologicalSpace T] [TopologicalSpace X] [PreconnectedSpace X]
      (L : ι → Type u) [∀ i, TopologicalSpace (L i)]
      (inclusion : ∀ i, L i → M) (hinj : ∀ i, Function.Injective (inclusion i))
      (hdisj : ∀ i j x y, inclusion i x = inclusion j y → i = j)
      (c : OpenPartialHomeomorph M (E × T)) (O : Opens T)
      (label : O → ι) (branch : ∀ t : O, Opens (L (label t)))
      (param : ∀ t : O, {z : E // (z, t.val) ∈ c.target} ≃ₜ branch t)
      (htrans : ∀ p ∈ c.target, p.2 ∈ O)
      (hparam : ∀ (t : O) (z : {z : E // (z, t.val) ∈ c.target}),
        c.symm (z.val, t.val) = inclusion (label t) (param t z).val)
      (i : ι) (g : X → L i) (hg : Continuous g)
      (hsource : ∀ x, inclusion i (g x) ∈ c.source) :
      ∀ x y, (c (inclusion i (g x))).2 = (c (inclusion i (g y))).2 := by
    have hlocal (i : ι) (y : L i) (hy : inclusion i y ∈ c.source) :
        ∃ V : Opens (L i), y ∈ V ∧
          ∀ w : V, (c (inclusion i w.val)).2 = (c (inclusion i y)).2 := by
      let p := c (inclusion i y)
      have hp : p ∈ c.target := c.map_source hy
      let t : O := ⟨p.2, htrans p hp⟩
      let z : {z : E // (z, t.val) ∈ c.target} := ⟨p.1, hp⟩
      have he : inclusion (label t) (param t z).val = inclusion i y := by
        rw [← hparam]
        exact c.left_inv hy
      have hi : label t = i := hdisj _ _ _ _ he
      clear_value z t p
      subst i
      have hyparam : (param t z).val = y := hinj _ he
      have hybranch : y ∈ branch t := hyparam ▸ (param t z).property
      have hcoord (v : branch t) : (c (inclusion (label t) v.val)).2 = t.val := by
        let w := (param t).symm v
        have hw : (param t w).val = v.val := congrArg Subtype.val ((param t).apply_symm_apply v)
        rw [← hw, ← hparam]
        exact congrArg Prod.snd (c.right_inv w.property)
      exact ⟨branch t, hybranch, fun w ↦ (hcoord w).trans (hcoord ⟨y, hybranch⟩).symm⟩
    have hconstant : IsLocallyConstant (fun x ↦ (c (inclusion i (g x))).2) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      obtain ⟨V, hx, hV⟩ := hlocal i (g x) (hsource x)
      filter_upwards [hg.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hx)] with y hy
      exact hV ⟨g y, hy⟩
    intro x y
    exact hconstant.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ x) (mem_univ y)
  have iteratedLeafMaps {M ι : Type u} (L : ι → Type u) [∀ i, TopologicalSpace (L i)]
      [∀ i, ChartedSpace ℂ (L i)] (inclusion : ∀ i, L i → M)
      (g : M → M) (perm : ι → ι)
      (G : ∀ i, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L (perm i)) ∞)
      (hG : ∀ i x, inclusion (perm i) (G i x) = g (inclusion i x)) :
      ∀ n i, ∃ (j : ι) (H : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L j) ∞),
        ∀ x, inclusion j (H x) = g^[n] (inclusion i x) := by
    intro n
    induction n with
    | zero =>
      intro i
      exact ⟨i, Diffeomorph.refl _ _ _, fun _ ↦ rfl⟩
    | succ n ih =>
      intro i
      obtain ⟨j, H, hH⟩ := ih i
      refine ⟨perm j, H.trans (G j), ?_⟩
      intro x
      change inclusion (perm j) (G j (H x)) = _
      rw [hG, hH, Function.iterate_succ_apply']
  have : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hconv.isPreconnected
  have hcoreEventually := originalReceivingCore f a (U.leaf i) (hhol i)
    c K hK hconv hKc p hp cores hcover
  filter_upwards [hcoreEventually] with n hn
  obtain ⟨j, hj⟩ := hn
  obtain ⟨k, H, hH⟩ := iteratedLeafMaps L (fun i ↦ (U.leaf i).inclusion)
    (f.symm : M → M) perm G hG n i
  let g : K → L k := fun z ↦ H (c.val.symm z.val)
  have hg : Continuous g := H.continuous.comp
    (continuousOn_iff_continuous_domRestrict.mp (c.val.continuousOn_symm.mono hKc))
  have hs (z : K) : (U.leaf k).inclusion (g z) ∈ (boxes j).source := by
    change (U.leaf k).inclusion (H (c.val.symm z.val)) ∈ _
    rw [hH]
    exact hcore j (hj z.val z.property)
  have ht := plaqueConstancy L (fun i ↦ (U.leaf i).inclusion)
    (fun i ↦ (U.leaf i).injective) U.disjoint (boxes j) (O j) (label j) (branch j)
    (param j) (htrans j) (hparam j) k g hg hs
  let t : O j := ⟨(boxes j ((U.leaf k).inclusion (g ⟨p, hp⟩))).2,
    htrans j _ ((boxes j).map_source (hs ⟨p, hp⟩))⟩
  refine ⟨j, t, fun z hz ↦ ⟨hj z hz, ?_⟩⟩
  have hh := ht ⟨z, hz⟩ ⟨p, hp⟩
  change (boxes j ((U.leaf k).inclusion (H (c.val.symm z)))).2 = t.val at hh
  rw [hH] at hh
  exact hh

end HolomorphicAnosov.Ghys

