import HolomorphicAnosov.Paper.Zhang.NormalizedVectorDolbeaultPullback
import HolomorphicAnosov.Paper.Zhang.NormalizedHermitianJacobian
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealTangentSmooth
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NormalizedPullbackConvergence
import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion

open scoped ContDiff Topology Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov
noncomputable section
universe u
open Bundle Filter MeasureTheory DistributionalSection

/-! Smooth tangent-section coordinates, compact frame comparison, and complex-fibre Anosov seminorm
bounds. (Zhang, Lemma 4.3, pp. 15–16) -/

/-- Smooth tangent sections have smooth coefficients in every holomorphic frame. -/
theorem smooth_section_frame_coefficient
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (s : (x : X) → TangentSpace (complexModel d) x)
    (hs : ContMDiff (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (fun x ↦ TotalSpace.mk' (ComplexModel d) x (s x)))
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (fr : Trivialization (ComplexModel d)
      (TotalSpace.proj : TangentBundle (complexModel d) X → X))
    (hfr : IsHolomorphicFrame (d := d) fr) (k : Fin d) :
    ContDiffOn ℝ ∞ (coefficient s c fr k) (frameDomain c fr) := by
  have hcR : ContMDiffOn (realModel d) (realModel d) ∞ c.symm c.target := by
    intro z hz
    obtain ⟨hcont, hd⟩ := contMDiffWithinAt_iff.mp
      (contMDiffOn_symm_of_mem_maximalAtlas hc z hz)
    exact contMDiffWithinAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
  have hfR : ContMDiffOn ((realModel d).prod 𝓘(ℝ, ComplexModel d))
      ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞ fr fr.source := by
    intro p hp
    obtain ⟨hcont, hd⟩ := contMDiffWithinAt_iff.mp (hfr.2.1 p hp)
    exact contMDiffWithinAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
  have hsection : ContMDiffOn (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (fun z ↦ TotalSpace.mk' (ComplexModel d) (c.symm z) (s (c.symm z)))
      (frameDomain c fr) := hs.comp_contMDiffOn (hcR.mono Set.inter_subset_left)
  have hcomp := hfR.comp hsection
    (show Set.MapsTo (fun z ↦ TotalSpace.mk' (ComplexModel d) (c.symm z) (s (c.symm z)))
      (frameDomain c fr) fr.source from fun z hz ↦ (fr.mem_source).mpr hz.2)
  exact (((ContinuousLinearMap.proj k : ComplexModel d →L[ℝ] ℂ).contMDiff).comp_contMDiffOn
    (contMDiff_snd.comp_contMDiffOn hcomp)).contDiffOn

/-- A tangent section is smooth if and only if all its preferred coordinate coefficients are smooth. -/
theorem smooth_section_iff_preferred_coefficients
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (s : (x : X) → TangentSpace (complexModel d) x) :
    ContMDiff (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (fun x ↦ TotalSpace.mk' (ComplexModel d) x (s x)) ↔
    ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients s a)
      (chartAt (ComplexModel d) a).target := by
  let : VectorBundle ℝ (ComplexModel d) (TangentSpace (complexModel d) : X → Type _) :=
    OneFormBundle.real_vector_bundle
  let : ContMDiffVectorBundle ∞ (ComplexModel d) (TangentSpace (complexModel d) : X → Type _)
      (realModel d) := OneFormBundle.real_tangent_smooth
  constructor
  · intro hs a
    apply contDiffOn_pi.mpr
    intro k
    let fr := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
    have hfr : IsHolomorphicFrame (d := d) fr :=
      ⟨inferInstance, fr.contMDiffOn, fr.contMDiffOn_symm⟩
    have hc := smooth_section_frame_coefficient s hs (chartAt (ComplexModel d) a)
      (IsManifold.chart_mem_maximalAtlas a) fr hfr k
    apply hc.mono
    intro z hz
    exact ⟨hz, (chartAt (ComplexModel d) a).map_target hz⟩
  · intro hs a
    apply (contMDiffAt_section a).mpr
    rw [contMDiffAt_iff_source]
    have hc := (hs a).contDiffAt
      ((chartAt (ComplexModel d) a).open_target.mem_nhds (mem_chart_target _ a))
    change ContDiffAt ℝ ∞ ((fun x ↦ (trivializationAt (ComplexModel d)
      (TangentSpace (complexModel d)) a ⟨x, s x⟩).2) ∘ (chartAt (ComplexModel d) a).symm)
      (chartAt (ComplexModel d) a a) at hc
    simpa only [extChartAt, realModel, modelWithCornersSelf_coe_symm,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      OpenPartialHomeomorph.extend_coe, Function.id_comp, Function.comp_id,
      Set.range_id, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt,
      preferredVectorCoefficients] using hc

/-- The chart differential gives smooth coordinates for a smooth tangent section. -/
theorem smooth_section_tangent_chart_coefficient
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (s : (x : X) → TangentSpace (complexModel d) x)
    (hs : ContMDiff (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (fun x ↦ TotalSpace.mk' (ComplexModel d) x (s x)))
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) (k : Fin d) :
    ContDiffOn ℝ ∞ (tangentSectionChartCoefficient s c k) c.target := by
  have hcinv : ContMDiffOn (realModel d) (realModel d) ∞ c.symm c.target := by
    intro z hz
    obtain ⟨hcont, hd⟩ := contMDiffWithinAt_iff.mp
      (contMDiffOn_symm_of_mem_maximalAtlas hc z hz)
    exact contMDiffWithinAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
  have ht := (contMDiffOn_of_mem_maximalAtlas hc).contMDiffOn_tangentMapWithin
    (m := ∞) (by simp) c.open_source.uniqueMDiffOn
  have htR : ContMDiffOn ((realModel d).prod 𝓘(ℝ, ComplexModel d))
      ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (tangentMapWithin (complexModel d) (complexModel d) c c.source)
      (TotalSpace.proj ⁻¹' c.source) := by
    intro p hp
    obtain ⟨hcont, hd⟩ := contMDiffWithinAt_iff.mp (ht p hp)
    exact contMDiffWithinAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
  have hcomp := htR.comp (hs.comp_contMDiffOn hcinv)
    (show Set.MapsTo (fun z ↦ TotalSpace.mk' (ComplexModel d) (c.symm z) (s (c.symm z)))
      c.target (TotalSpace.proj ⁻¹' c.source) from fun z hz ↦ c.map_target hz)
  intro z hz
  have hcoords := (contMDiffWithinAt_totalSpace.mp (hcomp z hz)).2
  have hscalar := (ContinuousLinearMap.proj k : ComplexModel d →L[ℝ] ℂ).contMDiffAt
    |>.comp_contMDiffWithinAt z hcoords
  apply hscalar.contDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Function.comp_apply, tangentMapWithin, trivializationAt_model_space_apply]
    change (mfderiv (complexModel d) (complexModel d) c (c.symm w) (s (c.symm w))) k =
      (mfderivWithin (complexModel d) (complexModel d) c c.source (c.symm w)
        (s (c.symm w))) k
    rw [mfderivWithin_of_mem_nhds (c.open_source.mem_nhds (c.map_target hw))]
  · simp only [Function.comp_apply, tangentMapWithin, trivializationAt_model_space_apply]
    change (mfderiv (complexModel d) (complexModel d) c (c.symm z) (s (c.symm z))) k =
      (mfderivWithin (complexModel d) (complexModel d) c c.source (c.symm z)
        (s (c.symm z))) k
    rw [mfderivWithin_of_mem_nhds (c.open_source.mem_nhds (c.map_target hz))]

/-- A continuous positive fibre seminorm bounds frame coefficients uniformly on a compact subset. -/
theorem compact_frame_coefficient_bound
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (p : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    (hp : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd))
    (hppos : ∀ x v, v ≠ 0 → 0 < p x v)
    (fr : Trivialization (ComplexModel d)
      (TotalSpace.proj : TangentBundle (complexModel d) X → X))
    [fr.IsLinear ℂ] (K : Set X) (hK : IsCompact K) (hKfr : K ⊆ fr.baseSet) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ∀ v : TangentSpace (complexModel d) x,
      ∀ k : Fin d, ‖(fr (TotalSpace.mk' (ComplexModel d) x v)).2 k‖ ≤ C * p x v := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let frame (x : K) : ComplexModel d →ₗ[ℝ] TangentSpace (complexModel d) x.val :=
    ((fr.linearEquivAt ℂ x.val (hKfr x.property)).symm.toLinearMap).restrictScalars ℝ
  let q : K → Seminorm ℝ (ComplexModel d) := fun x ↦ (p x.val).comp (frame x)
  have hf : Continuous (fun z : K × ComplexModel d ↦
      (TotalSpace.mk' (ComplexModel d) z.1.val (frame z.1 z.2))) := by
    exact fr.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ ⟨hKfr z.1.property, Set.mem_univ _⟩)
  have hq : Continuous (fun z : K × ComplexModel d ↦ q z.1 z.2) := hp.comp hf
  have hqpos : ∀ x v, v ≠ 0 → 0 < q x v := by
    intro x v hv
    apply hppos
    intro hz
    exact hv ((fr.linearEquivAt ℂ x.val (hKfr x.property)).symm.map_eq_zero_iff.mp hz)
  obtain ⟨C, hC, hbound⟩ := Preparation.uniform_seminorm_upper_bound
    (fun _ : K ↦ normSeminorm ℝ (ComplexModel d)) q
    (by exact continuous_snd.norm) hq hqpos
  refine ⟨C, hC, ?_⟩
  intro x hx v k
  let xK : K := ⟨x, hx⟩
  have hv := hbound xK (fr.linearEquivAt ℂ x (hKfr hx) v)
  have he : frame xK (fr.linearEquivAt ℂ x (hKfr hx) v) = v :=
    (fr.linearEquivAt ℂ x (hKfr hx)).symm_apply_apply v
  have hnorm : ‖fr.linearEquivAt ℂ x (hKfr hx) v‖ ≤ C * p x v := by
    simpa only [q, Seminorm.comp_apply, he, coe_normSeminorm] using hv
  have hval : fr.linearEquivAt ℂ x (hKfr hx) v =
      (fr (TotalSpace.mk' (ComplexModel d) x v)).2 := rfl
  rw [hval] at hnorm
  exact (norm_le_pi_norm _ k).trans hnorm

/-- Uniform convergence in a continuous positive fibre seminorm implies uniform convergence of frame
coefficients on compact test supports. -/
theorem frame_coefficient_error_tendsto
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (p : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    (hp : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd))
    (hppos : ∀ x v, v ≠ 0 → 0 < p x v)
    (sn : ℕ → (x : X) → TangentSpace (complexModel d) x)
    (s : (x : X) → TangentSpace (complexModel d) x)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ x, p x (sn n x - s x) ≤ ε n)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (fr : Trivialization (ComplexModel d)
      (TotalSpace.proj : TangentBundle (complexModel d) X → X))
    [fr.IsLinear ℂ] (k : Fin d) (φ : TestFunction (frameDomain c fr) ℂ ⊤) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ z ∈ tsupport φ,
        ‖coefficient (sn n) c fr k z - coefficient s c fr k z‖ ≤ ε' n := by
  have hK : IsCompact (c.symm '' tsupport φ) :=
    φ.hasCompactSupport.isCompact.image_of_continuousOn
      (c.symm.continuousOn.mono (fun z hz ↦ (φ.tsupport_subset hz).1))
  have hKfr : c.symm '' tsupport φ ⊆ fr.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact (φ.tsupport_subset hz).2
  obtain ⟨C, hC, hnorm⟩ := compact_frame_coefficient_bound p hp hppos fr _ hK hKfr
  refine ⟨fun n ↦ C * ε n, by simpa using hε.const_mul C, ?_⟩
  filter_upwards [hbound] with n hn
  intro z hz
  have hx := hKfr (Set.mem_image_of_mem c.symm hz)
  have hsub : (fr (TotalSpace.mk' (ComplexModel d) (c.symm z)
      (sn n (c.symm z) - s (c.symm z)))).2 =
      (fr (TotalSpace.mk' (ComplexModel d) (c.symm z) (sn n (c.symm z)))).2 -
      (fr (TotalSpace.mk' (ComplexModel d) (c.symm z) (s (c.symm z)))).2 :=
    (fr.linearEquivAt ℂ (c.symm z) hx).map_sub _ _
  calc
    _ = ‖(fr (TotalSpace.mk' (ComplexModel d) (c.symm z)
        (sn n (c.symm z) - s (c.symm z)))).2 k‖ := by rw [hsub]; rfl
    _ ≤ C * p (c.symm z) (sn n (c.symm z) - s (c.symm z)) :=
      hnorm _ (Set.mem_image_of_mem c.symm hz) _ k
    _ ≤ C * ε n := mul_le_mul_of_nonneg_left (hn _) (zero_le_one.trans hC)

/-- The real Anosov metric induces a continuous positive seminorm on complex tangent fibres with the
stable and unstable contraction bounds. -/
theorem anosov_original_complex_block_bounds
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hS : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x)
    (hU : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x) :
    ∃ p : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x),
      (∀ x v, v ≠ 0 → 0 < p x v) ∧
      Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) ∧
      ∀ x,
        fibreNormOperator (p x) (p (hermitianBoundsIterate f a.k x)) (S x)
            (hermitianBoundsDerivative f a.k x) < 1 ∧
        fibreNormOperator (p (hermitianBoundsIterate f a.k x)) (p x)
            (U (hermitianBoundsIterate f a.k x))
            (hermitianBoundsDerivative f a.k x).symm < 1 := by
  let : RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  let T := fun x : X ↦ complexTangentToReal d x
  let p : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x) := fun x ↦
    (normSeminorm ℝ (TangentSpace (realModel d) x)).comp (T x).toLinearEquiv.toLinearMap
  refine ⟨p, ?_, ?_, ?_⟩
  · intro x v hv
    exact norm_pos_iff.mpr ((T x).map_ne_zero_iff.mpr hv)
  · exact FixedBlockEstimates.Native.continuous_original_norm a.metric
      (fun z : TangentBundle (complexModel d) X ↦ z.proj)
      (fun z ↦ T z.proj z.snd) continuous_complexTangentToReal
  · intro x
    let F := hermitianBoundsDerivative f a.k x
    let R := (realIterate (realModel d) f.toReal a.k).mfderivToContinuousLinearEquiv (by simp) x
    let DS := restrictedIterateDerivative f.toReal a.splitting.stable.toDistribution
      a.splitting.stable_map a.k x
    let DU := restrictedIterateDerivative f.toReal a.splitting.unstable.toDistribution
      a.splitting.unstable_map a.k x
    have hreal (v : TangentSpace (complexModel d) x) :
        R (T x v) = T (hermitianBoundsIterate f a.k x) (F v) := by
      exact (hermitianBoundsIterate f a.k).real_mfderiv_realification x v
    have hback (v : TangentSpace (realModel d) (hermitianBoundsIterate f a.k x)) :
        T x (F.symm ((T (hermitianBoundsIterate f a.k x)).symm v)) = R.symm v := by
      apply R.injective
      rw [hreal, F.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
      exact (R.apply_symm_apply v).symm
    constructor
    · apply lt_of_le_of_lt _ (a.stable_contracting x)
      apply CompactHermitianBoundsScratch.operator_le_of_pointwise
        (p x) (p (hermitianBoundsIterate f a.k x)) (S x)
        (F.toLinearMap.restrictScalars ℝ) (norm_nonneg DS.toContinuousLinearMap)
      intro v hv
      have hvR : T x v ∈ a.splitting.stable.toDistribution x := by
        rw [← hS x]
        exact ⟨v, hv, rfl⟩
      have he : (DS ⟨T x v, hvR⟩).val = T (hermitianBoundsIterate f a.k x) (F v) :=
        hreal v
      change ‖T (hermitianBoundsIterate f a.k x) (F v)‖ ≤
        ‖DS.toContinuousLinearMap‖ * ‖T x v‖
      rw [← he]
      exact DS.toContinuousLinearMap.le_opNorm ⟨T x v, hvR⟩
    · apply lt_of_le_of_lt _ (a.unstable_contracting x)
      apply CompactHermitianBoundsScratch.operator_le_of_pointwise
        (p (hermitianBoundsIterate f a.k x)) (p x) (U (hermitianBoundsIterate f a.k x))
        (F.symm.toLinearMap.restrictScalars ℝ) (norm_nonneg DU.symm.toContinuousLinearMap)
      intro v hv
      have hvR : T (hermitianBoundsIterate f a.k x) v ∈
          a.splitting.unstable.toDistribution (hermitianBoundsIterate f a.k x) := by
        rw [← hU (hermitianBoundsIterate f a.k x)]
        exact ⟨v, hv, rfl⟩
      have he : (DU.symm ⟨T (hermitianBoundsIterate f a.k x) v, hvR⟩).val =
          T x (F.symm v) := by
        change R.symm (T (hermitianBoundsIterate f a.k x) v) = _
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using
          (hback (T (hermitianBoundsIterate f a.k x) v)).symm
      change ‖T x (F.symm v)‖ ≤ ‖DU.symm.toContinuousLinearMap‖ *
        ‖T (hermitianBoundsIterate f a.k x) v‖
      rw [← he]
      exact DU.symm.toContinuousLinearMap.le_opNorm ⟨T (hermitianBoundsIterate f a.k x) v, hvR⟩


end
end HolomorphicAnosov
