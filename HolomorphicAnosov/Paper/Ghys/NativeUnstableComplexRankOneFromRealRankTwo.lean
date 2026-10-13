import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.StableFoliationsComplexSubmoduleOfJInvariant
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalStableJInvariant
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseSplitting
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalNormComparison

noncomputable section
namespace HolomorphicAnosov.Ghys
open Bundle Set
open HolomorphicAnosov.OneFormBundle
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology
universe u
attribute [local instance] complex_isManifold_real

/-- A compatible native complex upgrade makes the identity smooth in both atlas directions. (Demailly, §3.C) -/
theorem native_complex_upgrade_identity_mdifferentiable
    {r k d : ℕ} {L : Type u} {M : Type u}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {inc : L → M}
    (U : HolomorphicAnosov.NativeLeafComplexUpgrade (d := d) (r := r) k inc) :
    letI := U.charts
    ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel k) ∞ (id : L → L) ∧
      ContMDiff (realModel k) 𝓘(ℝ, Fin r → ℝ) ∞ (id : L → L) := by
  let := U.charts
  constructor
  · intro x
    apply contMDiffAt_iff.mpr
    refine ⟨continuousAt_id, ?_⟩
    let e := chartAt (Fin r → ℝ) x
    let c := chartAt (ComplexModel k) x
    have hd := U.real_to_complex e (ChartedSpace.chart_mem_atlas x)
      c (ChartedSpace.chart_mem_atlas x)
    have hx : e x ∈ (e.symm.trans c).source := by
      simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · exact e.map_source (ChartedSpace.mem_chart_source x)
      · rw [e.left_inv (ChartedSpace.mem_chart_source x)]
        exact ChartedSpace.mem_chart_source x
    have hn : e.target ∩ e.symm ⁻¹' c.source ∈ nhds (e x) :=
      (e.symm.trans c).open_source.mem_nhds hx
    have hda := hd.contDiffAt hn
    simpa only [extChartAt, realModel, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, Function.comp_id, Function.id_comp,
      id_eq, Set.range_id, e, c] using hda.contDiffWithinAt
  · intro x
    apply contMDiffAt_iff.mpr
    refine ⟨continuousAt_id, ?_⟩
    let e := chartAt (Fin r → ℝ) x
    let c := chartAt (ComplexModel k) x
    have hd := U.complex_to_real c (ChartedSpace.chart_mem_atlas x)
      e (ChartedSpace.chart_mem_atlas x)
    have hx : c x ∈ (c.symm.trans e).source := by
      change c x ∈ c.target ∧ c.symm (c x) ∈ e.source
      constructor
      · exact c.map_source (ChartedSpace.mem_chart_source x)
      · rw [c.left_inv (ChartedSpace.mem_chart_source x)]
        exact ChartedSpace.mem_chart_source x
    have hn : c.target ∩ c.symm ⁻¹' e.source ∈ nhds (c x) :=
      (c.symm.trans e).open_source.mem_nhds hx
    have hda := hd.contDiffAt hn
    simpa only [extChartAt, realModel, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, Function.comp_id, Function.id_comp,
      id_eq, Set.range_id, e, c] using hda.contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
/-- The Anosov block bounds yield all-time estimates in a smooth ambient Hermitian metric. (Ghys, Lemma 2.1) -/
theorem native_unstable_hermitian_growth_exists
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) :
    ∃ (h : HermitianTangentMetricCore d M), IsSmoothHermitianTangentMetric h ∧
    ∃ C rate : ℝ, 0 < C ∧ 0 < rate ∧ rate < 1 ∧
      (∀ n x v, v ∈ a.splitting.stable.toDistribution x →
        Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
          (mfderiv (realModel d) (realModel d)
            (realIterate (realModel d) f.toReal n) x v)
          (mfderiv (realModel d) (realModel d)
            (realIterate (realModel d) f.toReal n) x v)) ≤
          C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) ∧
      (∀ n x v, v ∈ a.splitting.unstable.toDistribution x →
        Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] x)
          (mfderiv (realModel d) (realModel d)
            (realIterate (realModel d) f.toReal.symm n) x v)
          (mfderiv (realModel d) (realModel d)
            (realIterate (realModel d) f.toReal.symm n) x v)) ≤
          C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) := by
  have hmetric : ∃ g : HermitianTangentMetricCore d M,
      IsSmoothHermitianTangentMetric g := by
    let : IsManifold (realModel d) ∞ M := complex_isManifold_real d M
    let : VectorBundle ℝ (ComplexModel d) (fun x : M ↦ TangentSpace (complexModel d) x) :=
      real_vector_bundle
    let : ContMDiffVectorBundle ∞ (ComplexModel d)
        (fun x : M ↦ TangentSpace (complexModel d) x) (realModel d) :=
      real_tangent_smooth
    obtain ⟨g, hp, _, _⟩ := smooth_complex_bundle_hermitian_metric
      (B := ComplexModel d) (M := M)
      (E := fun x : M ↦ TangentSpace (complexModel d) x) d
    refine ⟨g, ?_⟩
    intro e he i j
    have hframe (i : Fin d) :
        ContMDiffOn (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
          (fun x ↦ TotalSpace.mk' (E := fun x : M ↦ TangentSpace (complexModel d) x)
            (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
      have hs := contMDiffOn_symm_of_mem_maximalAtlas he
      have htm := hs.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
        e.open_target.uniqueMDiffOn
      have hinput : ContMDiffOn (complexModel d) ((complexModel d).tangent) ∞
          (fun x ↦ (tangentBundleModelSpaceHomeomorph (complexModel d)).symm
            (e x, Pi.single i 1)) e.source :=
        contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp_contMDiffOn
          ((contMDiffOn_of_mem_maximalAtlas he).prodMk_space contMDiffOn_const)
      have hc := htm.comp hinput (fun x hx ↦ e.map_source hx)
      have hc' : ContMDiffOn (complexModel d) ((complexModel d).prod 𝓘(ℂ, ComplexModel d)) ∞
          (fun x ↦ TotalSpace.mk' (E := fun x : M ↦ TangentSpace (complexModel d) x)
            (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
        apply hc.congr
        intro x hx
        simp only [Function.comp_apply, tangentBundleModelSpaceHomeomorph_coe_symm,
          tangentMapWithin]
        dsimp only [TotalSpace.toProd, Equiv.coe_fn_symm_mk]
        rw [mfderivWithin_eq_mfderiv (e.open_target.uniqueMDiffOn _ (e.map_source hx))
          (((hs _ (e.map_source hx)).contMDiffAt
            (e.open_target.mem_nhds (e.map_source hx))).mdifferentiableAt (by simp))]
        simp only [hermitianTangentChartFrame]
        apply TotalSpace.ext (e.left_inv hx).symm
        rfl
      intro x hx
      obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hc' x hx)
      exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
    have hpair := hp e.source e.open_source
      (fun x ↦ hermitianTangentChartFrame e (e x) i)
      (fun x ↦ hermitianTangentChartFrame e (e x) j) (hframe i) (hframe j)
    have hinv := real_contMDiffOn_map (contMDiffOn_symm_of_mem_maximalAtlas he)
    have hcoeff := hpair.comp hinv (fun z hz ↦ e.map_target hz)
    have hc : ContMDiffOn 𝓘(ℝ, ComplexModel d) 𝓘(ℝ, ℂ) ∞
        (hermitianTangentChartCoefficient g e i j) e.target := by
      apply hcoeff.congr
      intro z hz
      simp only [Function.comp_apply,
        hermitianTangentChartCoefficient, hermitianTangentPairing]
      rw [e.right_inv hz]
    exact hc.contDiffOn
  obtain ⟨h, hh⟩ := hmetric
  have hcomparison :
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
        ⟨a.metric.toRiemannianMetric⟩
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ 1 ≤ C ∧ ∀ x v,
        c * Real.sqrt (((h x).inner v v).re) ≤ ‖complexTangentToReal d x v‖ ∧
        ‖complexTangentToReal d x v‖ ≤ C * Real.sqrt (((h x).inner v v).re) := by
    exact original_norm_comparison f a h hh
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C₀, rate, hC₀, hrate, hrate1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
  obtain ⟨c, C₁, hc, hcC₁, hC₁, hcompare⟩ := hcomparison
  have hcomp (x : M) (v : TangentSpace (realModel d) x) :
      c * Real.sqrt (hermitianTangentRealPairing h x v v) ≤ ‖v‖ ∧
      ‖v‖ ≤ C₁ * Real.sqrt (hermitianTangentRealPairing h x v v) := by
    simpa only [hermitianTangentRealPairing, hermitianTangentPairing,
      ContinuousLinearEquiv.apply_symm_apply] using
      hcompare x ((complexTangentToReal d x).symm v)
  have transport (n : ℕ) (x y : M) (v : TangentSpace (realModel d) x)
      (w : TangentSpace (realModel d) y) (hb : ‖w‖ ≤ C₀ * rate ^ n * ‖v‖) :
      Real.sqrt (hermitianTangentRealPairing h y w w) ≤
        (C₀ * C₁ / c) * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v) := by
    have hbound := (hcomp y w).1.trans (hb.trans
      (mul_le_mul_of_nonneg_left (hcomp x v).2
        (mul_nonneg hC₀.le (pow_nonneg hrate.le n))))
    have hquot : Real.sqrt (hermitianTangentRealPairing h y w w) ≤
        (C₀ * rate ^ n * (C₁ * Real.sqrt (hermitianTangentRealPairing h x v v))) / c := by
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hbound
    convert hquot using 1; ring
  refine ⟨h, hh, C₀ * C₁ / c, rate, div_pos (mul_pos hC₀ (lt_of_lt_of_le zero_lt_one hC₁)) hc,
    hrate, hrate1, ?_, ?_⟩
  · intro n x v hv
    exact transport n x _ v _ (hs n x v hv)
  · intro n x v hv
    exact transport n x _ v _ (hu n x v hv)

/-- The stable-space J-invariance theorem transfers to the unstable summand under inversion. (Ghys, Lemma 2.1; HPS, Lemma 2.7) -/
theorem native_unstable_J_invariant_of_hermitian_growth
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M)
    (h : HermitianTangentMetricCore d M)
    (P : InvariantRealTangentSplitting f.toReal)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate ∧ rate < 1)
    (hs : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.stable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal n) x v)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v))
    (hu : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.unstable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) :
    ∀ x (v : TangentSpace (realModel d) x),
      v ∈ P.unstable.toDistribution x →
      complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v) ∈
        P.unstable.toDistribution x := by
  let Q : InvariantRealTangentSplitting (Biholomorph.toReal f.symm) :=
    TheoremAProof.inverseSplitting f.toReal P
  apply StableFoliationsSupport.original_stable_J_invariant
    f.symm h Q C rate hC hrate
  · intro n x v hv
    convert hu n x v hv using 1; rfl
  · intro n x v hv
    convert hs n x v hv using 1; rfl

/-- The real unstable Anosov fibre is invariant under the ambient complex structure. (Ghys, Lemma 2.1) -/
theorem native_unstable_real_J_invariant_from_anov
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) :
    ∀ x (v : TangentSpace (realModel d) x),
      v ∈ a.splitting.unstable.toDistribution x →
      complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v) ∈
        a.splitting.unstable.toDistribution x := by
  obtain ⟨h, _hh, C, rate, hC, hr0, hr1, hs, hu⟩ :=
    native_unstable_hermitian_growth_exists f a
  exact native_unstable_J_invariant_of_hermitian_growth f h a.splitting C rate hC ⟨hr0, hr1⟩ hs hu

/-- Real rank two of the unstable Anosov summand implies complex rank one. (Ghys, Lemma 2.1; Proposition 2.2) -/
theorem native_unstable_complex_rank_one_from_real_rank_two
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hu : ∀ x : M, Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2) :
    HasComplexRankOne a.splitting.unstable.toDistribution := by
  intro x
  let e : TangentSpace (complexModel d) x ≃ₗ[ℝ]
      TangentSpace (realModel d) x := (complexTangentToReal d x).toLinearEquiv
  obtain ⟨K, hK, hKeq⟩ :=
    HolomorphicAnosov.StableFoliationsSupport.existsUnique_complexSubmodule_of_J_invariant
      e (a.splitting.unstable.toDistribution x) (fun w hw ↦
        native_unstable_real_J_invariant_from_anov f a x w hw)
  have hrealmap : Module.finrank ℝ
      (Submodule.map e.toLinearMap (K.restrictScalars ℝ)) = 2 := by
    rw [hK]
    exact hu x
  have hreal : Module.finrank ℝ (K.restrictScalars ℝ) = 2 := by
    rw [← e.finrank_map_eq]
    exact hrealmap
  have hcomplex : 2 * Module.finrank ℂ K = 2 := by
    rw [← finrank_real_of_complex]
    exact hreal
  have hdim : Module.finrank ℂ K = 1 := by omega
  exact ⟨K, hdim, hK⟩

end HolomorphicAnosov.Ghys
