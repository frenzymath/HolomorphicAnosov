import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.NativeSmoothPullbackCurvatureL2Decay
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.SmoothCurvaturePairing
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.SmoothOneFormFlatOfWeakClosed
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientHolomorphicDbar
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ClosedTypeOneDbar
import HolomorphicAnosov.Paper.Zhang.InvariantConnection
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus
import HolomorphicAnosov.Geometry.NativeUnstableLeafDataOfAnosov
import HolomorphicAnosov.Geometry.NativeSingleBundleFoliationChart
import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.SubmoduleRealification
import HolomorphicAnosov.Analysis.Distribution.RegularPairingL2Bound
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.CurvatureDecayFactorTendsto
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.CurvatureConormJacobian

open Filter MeasureTheory TopologicalSpace Set
open scoped Manifold ContDiff Topology _root_.Topology BigOperators Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov.ConnectionFlatEstimates
open HolomorphicAnosov QuotientLineConnection

/-- A real-linear map satisfying `L (Complex.I • v) = Complex.I * L v` equals the complex linear
combination of its coordinate values. -/
theorem real_linear_type_one_coordinate_sum {n : ℕ}
    (L : (Fin n → ℂ) →L[ℝ] ℂ)
    (hI : ∀ v, L (Complex.I • v) = Complex.I * L v) (v : Fin n → ℂ) :
    L v = ∑ k : Fin n, v k • L (Pi.single k 1) := by
  classical
  have hmap_smul (a : ℂ) (u : Fin n → ℂ) : L (a • u) = a • L u := by
    have ha : a • u = (a.re : ℝ) • u + (a.im : ℝ) • (Complex.I • u) := by
      ext k
      simp [Complex.ext_iff]
      ring
    rw [ha, map_add, L.map_smul (R₁ := ℝ), L.map_smul (R₁ := ℝ), hI]
    apply Complex.ext <;> simp [smul_eq_mul]; ring
  have hv : v = ∑ k : Fin n, v k • (Pi.single k 1 : Fin n → ℂ) := by
    rw [← Finset.univ_sum_single v]
    congr 1
    funext k j
    simp [Pi.single_apply]
  calc
    L v = L (∑ k : Fin n, v k • (Pi.single k 1 : Fin n → ℂ)) := congrArg L hv
    _ = ∑ k : Fin n, v k • L (Pi.single k 1) := by
      rw [map_sum]
      simp_rw [hmap_smul]


/-- The inverse-chart coordinate form of a compatible quotient connection satisfies the type-(1,0)
identity. -/
theorem native_coordinate_form_type_one
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : Connection U) (hcompatible : IsCompatible nabla)
    (V : Opens X) (e : HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) :
    ∀ z ∈ c.target ∩ c.symm ⁻¹' (V : Set X), ∀ v : ComplexModel d,
      coordinateForm nabla e c z (Complex.I • v) =
        Complex.I * coordinateForm nabla e c z v := by
  intro z hz v
  have hf := (contMDiffAt_symm_of_mem_maximalAtlas hc hz.1).mdifferentiableAt (by simp)
  let D : ComplexModel d →L[ℂ] TangentSpace (complexModel d) (c.symm z) :=
    (mfderiv (complexModel d) (complexModel d) c.symm z).comp
      (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap
  have hD (w : ComplexModel d) : coordinateForm nabla e c z w =
      nabla.form V e (c.symm z) (complexTangentToReal d (c.symm z) (D w)) := by
    apply congrArg (nabla.form V e (c.symm z))
    exact mfderiv_complex_to_real hf ((NormedSpace.fromTangentSpace z).symm w)
  rw [hD, hD, D.map_smul]
  exact hcompatible.1 V e (c.symm z) hz.2 (D v)


/-- The curvatures of smooth compatible pullback connections converge weakly to the distributional
curvature of the invariant connection, and their squared L² integrals on compact test supports
tend to zero. (Zhang, Lemma 2.3, eqs. (6)–(11), pp. 5–7) -/
theorem native_pullback_curvature_sequence
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : Connection U) (hcontinuous : IsContinuous nabla)
    (hcompatible : IsCompatible nabla)
    (hinvariant : IsInvariant nabla f hU) :
    ∀ (V : Opens X) (e : HolomorphicFrame U V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      let Ω : Opens (ComplexModel d) :=
        ⟨c.target ∩ c.symm ⁻¹' (V : Set X), c.isOpen_inter_preimage_symm V.isOpen⟩
      ∃ R : ℕ → ComplexModel d → ComplexModel d → ComplexModel d → ℂ,
        (∀ n v w, ContinuousOn (R n v w) Ω) ∧
        (∀ (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤),
          Filter.Tendsto (fun n ↦ DistributionalSection.regularPairing Ω (R n v w) φ)
            Filter.atTop (nhds (
        (∑ j : Fin d,
          (-DistributionalSection.regularPairing Ω
            (fun z ↦ coordinateForm nabla e c z (Pi.single j 1))
            (TestFunction.lineDerivCLM ℂ v φ) * w j +
          DistributionalSection.regularPairing Ω
            (fun z ↦ coordinateForm nabla e c z (Pi.single j 1))
            (TestFunction.lineDerivCLM ℂ w φ) * v j))))) ∧
        (∀ (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤),
          Filter.Tendsto (fun n ↦ ∫ z in tsupport φ, ‖R n v w z‖ ^ 2 ∂volume)
            Filter.atTop (nhds 0)) := by
  let : TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hnative : ∀ x, Nonempty (NativeAsymptoticLeafDatum (realModel d)
      f.toHomeomorph.symm a.splitting.unstable.toDistribution x) :=
    exists_native_unstable_leaf_data_of_anosov f a hstable
  let native : ∀ x, NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph.symm
      a.splitting.unstable.toDistribution x := fun x => Classical.choice (hnative x)
  obtain ⟨P, hP, hP_real⟩ := rank_one_stable_holomorphic_unstable (by omega) f a hstable
  have hPU : P = U := by
    funext x
    exact submodule_eq_of_realification_eq x (P x) (U x)
      ((hP_real x).trans (hU_real x).symm)
  subst P
  have hbox (x : X) := SingleBundleHolomorphicBox.exists_native_single_bundle_foliation_chart
    (by omega) f.toHomeomorph.symm U hP
    a.splitting.unstable.toDistribution hU_real native x
  have hline := quotient_line_of_holomorphic_codimension_one (by omega : 1 ≤ d) U hP
  obtain ⟨-, -, -, -, -, -, hseed, -, hpull, -⟩ :=
    ConnectionCalculus.zhang_connection_calculus U hP hline
      (unstable_bott_involutive f a U hU_real)
  obtain ⟨D₀, hD₀smooth, hD₀compatible⟩ := hseed
  obtain ⟨Q, hQ, hPull⟩ := hpull f hU
  let smoothConnection := fun (D : Connection U) ↦
    ∀ (V : Opens X) (e : HolomorphicFrame U V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (coordinateForm D e c) (c.target ∩ c.symm ⁻¹' (V : Set X))
  let E := {D : Connection U // smoothConnection D ∧ IsCompatible D}
  have hnext : ∀ D : E, ∃ Dp : E,
      ∀ (V W : Opens X) (e : HolomorphicFrame U V) (e' : HolomorphicFrame U W)
        (x : X), x ∈ V → f x ∈ W →
        Dp.val.form V e x = (imageFrameCoefficient f hU e e' x)⁻¹ •
          realDifferential (imageFrameCoefficient f hU e e') x +
          (D.val.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x) := by
    intro D
    obtain ⟨Dp, hs, hp, hcomp, -⟩ := hPull D.val D.property.1
    exact ⟨⟨Dp, hs, hcomp D.property.2⟩, hp⟩
  choose next hnext using hnext
  let Dstart : E := ⟨D₀, hD₀smooth, hD₀compatible⟩
  let Ds : ℕ → Connection U := fun n ↦ ((next^[n]) Dstart).val
  have hDs (n : ℕ) : smoothConnection (Ds n) ∧ IsCompatible (Ds n) :=
    ((next^[n]) Dstart).property
  have hrec (n : ℕ) (V W : Opens X) (e : HolomorphicFrame U V)
      (e' : HolomorphicFrame U W) (x : X) (hx : x ∈ V) (hfx : f x ∈ W) :
      (Ds (n + 1)).form V e x = (imageFrameCoefficient f hU e e' x)⁻¹ •
        realDifferential (imageFrameCoefficient f hU e e') x +
        ((Ds n).form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x) := by
    dsimp only [Ds]
    rw [Function.iterate_succ_apply']
    exact hnext _ V W e e' x hx hfx
  have hcover := ConnectionCalculus.holomorphic_frame_cover U hP hline
  obtain ⟨D, hDcont, hDcomp, hDinv, hbounded, hlimit⟩ :=
    compatible_pullback_sequence_c0_limit hP f a hU_real hcover hU Ds
      (fun n V e c hc ↦ ((hDs n).1 V e c hc).continuousOn)
      (fun n ↦ (hDs n).2) hrec
  have hagree : Agrees nabla D := compatible_invariant_connections_agree f a hP
    hU_real hcover hU D nabla hDcont hcontinuous hDcomp hcompatible hDinv hinvariant
  intro V e c hc
  dsimp only
  let Ω : Opens (ComplexModel d) :=
    ⟨c.target ∩ c.symm ⁻¹' (V : Set X), c.isOpen_inter_preimage_symm V.isOpen⟩
  let A : ℕ → ComplexModel d → ComplexModel d →L[ℝ] ℂ :=
    fun n z ↦ coordinateForm (Ds n) e c z
  let R : ℕ → ComplexModel d → ComplexModel d → ComplexModel d → ℂ :=
    fun n v w z ↦ fderiv ℝ (A n) z v w - fderiv ℝ (A n) z w v
  have hR (n : ℕ) (v w : ComplexModel d) : ContinuousOn (R n v w) Ω := by
    have hDA : ContinuousOn (fderiv ℝ (A n)) Ω :=
      ((hDs n).1 V e c hc).continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)
    exact (hDA.clm_apply continuousOn_const |>.clm_apply continuousOn_const).sub
      (hDA.clm_apply continuousOn_const |>.clm_apply continuousOn_const)
  have hpair (n : ℕ) (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤) :
      DistributionalSection.regularPairing Ω (R n v w) φ =
        -(∫ z, A n z w * fderiv ℝ (φ : ComplexModel d → ℂ) z v) +
          (∫ z, A n z v * fderiv ℝ (φ : ComplexModel d → ℂ) z w) :=
    smooth_curvature_pairing Ω (A n) ((hDs n).1 V e c hc) v w φ
  have hweak (w : ComplexModel d) (ψ : TestFunction Ω ℂ ⊤) :
      Tendsto (fun n ↦ ∫ z, A n z w * ψ z)
        atTop (𝓝 (∫ z, coordinateForm nabla e c z w * ψ z)) := by
    let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    let w' (z : ComplexModel d) : TangentSpace (realModel d) (c.symm z) :=
      mfderiv (realModel d) (realModel d) c.symm z w
    have hs : ContMDiffOn (realModel d) (realModel d) ∞ c.symm c.target :=
      OneFormBundle.real_contMDiffOn_map (contMDiffOn_symm_of_mem_maximalAtlas hc)
    have htm := hs.continuousOn_tangentMapWithin (by simp)
      c.open_target.uniqueMDiffOn
    have hinput : Continuous (fun z : c.target ↦
        (tangentBundleModelSpaceHomeomorph (realModel d)).symm (z.val, w)) :=
      (tangentBundleModelSpaceHomeomorph (realModel d)).symm.continuous.comp
        (continuous_subtype_val.prodMk continuous_const)
    have hv : Continuous (fun z : c.target ↦
        (⟨c.symm z.val, w' z.val⟩ : TangentBundle (realModel d) X)) := by
      apply (htm.comp_continuous hinput (fun z ↦ z.property)).congr
      intro z
      change (⟨c.symm z.val,
        mfderivWithin (realModel d) (realModel d) c.symm c.target z.val w⟩ :
          TangentBundle (realModel d) X) = _
      rw [mfderivWithin_eq_mfderiv
        (c.open_target.uniqueMDiffOn _ z.property)
        (((hs _ z.property).contMDiffAt (c.open_target.mem_nhds z.property)).mdifferentiableAt
          (by simp))]
    have hnorm : ContinuousOn (fun z ↦ ‖w' z‖) Ω :=
      (continuousOn_iff_continuous_domRestrict.mpr
        (FixedBlockEstimates.Native.continuous_original_norm a.metric (fun z : c.target ↦ c.symm z.val) (fun z : c.target ↦ w' z.val) hv)).mono
          inter_subset_left
    have hi (n : ℕ) : Integrable (fun z ↦ A n z w * ψ z) := by
      simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
        ψ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
          ((((hDs n).1 V e c hc).continuousOn.clm_apply continuousOn_const).locallyIntegrableOn
            Ω.isOpen.measurableSet)
    have hiD : Integrable (fun z ↦ coordinateForm D e c z w * ψ z) := by
      simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
        ψ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
          (((hDcont V e c hc).clm_apply continuousOn_const).locallyIntegrableOn Ω.isOpen.measurableSet)
    have hib : Integrable (fun z ↦ ‖w' z‖ * ‖ψ z‖) := by
      have hb := ψ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℂ ℂ)
        ((Complex.continuous_ofReal.comp_continuousOn hnorm).locallyIntegrableOn
          Ω.isOpen.measurableSet)
      convert hb.norm using 1
      simp [Complex.norm_real, mul_comm]
    have hlimD : Tendsto (fun n ↦ ∫ z, A n z w * ψ z)
        atTop (𝓝 (∫ z, coordinateForm D e c z w * ψ z)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero (fun n ↦ norm_nonneg _)
        (fun n ↦ ?_) (by simpa using hlimit.mul_const (∫ z, ‖w' z‖ * ‖ψ z‖))
      rw [← integral_sub (hi n) hiD]
      calc
        ‖∫ z, A n z w * ψ z - coordinateForm D e c z w * ψ z‖ ≤
            ∫ z, ‖A n z w * ψ z - coordinateForm D e c z w * ψ z‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ z, c0Distance a.metric (Ds n) D * (‖w' z‖ * ‖ψ z‖) := by
          apply integral_mono ((hi n).sub hiD).norm (hib.const_mul _)
          intro z
          by_cases hz : z ∈ Ω
          · change ‖(A n z) w * ψ z - (coordinateForm D e c) z w * ψ z‖ ≤
              c0Distance a.metric (Ds n) D * (‖w' z‖ * ‖ψ z‖)
            calc
              ‖(A n z) w * ψ z - (coordinateForm D e c z) w * ψ z‖ =
                  ‖((A n z) w - (coordinateForm D e c z) w) * ψ z‖ := by rw [sub_mul]
              _ = ‖(A n z) w - (coordinateForm D e c z) w‖ * ‖ψ z‖ := norm_mul _ _
              _ ≤ c0Distance a.metric (Ds n) D * ‖w' z‖ * ‖ψ z‖ := by
                have hcoordA : A n z w = (Ds n).form V e (c.symm z) (w' z) := by
                  rfl
                have hcoordD : coordinateForm D e c z w = D.form V e (c.symm z) (w' z) := by
                  rfl
                rw [hcoordA, hcoordD]
                have hh := difference_eval_le_c0 a.metric (Ds n) D (hbounded n)
                  V e (c.symm z) hz.2 (w' z)
                have heq : Real.sqrt (a.metric.inner (c.symm z) (w' z) (w' z)) = ‖w' z‖ := by
                  symm
                  exact norm_eq_sqrt_real_inner _
                calc
                  _ ≤ c0Distance a.metric (Ds n) D *
                      Real.sqrt (a.metric.inner (c.symm z) (w' z) (w' z)) * ‖ψ z‖ :=
                    mul_le_mul_of_nonneg_right hh (norm_nonneg _)
                  _ = c0Distance a.metric (Ds n) D * ‖w' z‖ * ‖ψ z‖ := by rw [heq]
              _ = c0Distance a.metric (Ds n) D * (‖w' z‖ * ‖ψ z‖) := mul_assoc _ _ _
          · simp [Pi.sub_apply, ψ.zero_on_compl hz]
        _ = c0Distance a.metric (Ds n) D * ∫ z, ‖w' z‖ * ‖ψ z‖ := integral_const_mul _ _
    have heq : (∫ z, coordinateForm D e c z w * ψ z) =
        ∫ z, coordinateForm nabla e c z w * ψ z := by
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ Ω
      · simp only [coordinateForm, ContinuousLinearMap.comp_apply, hagree V e (c.symm z) hz.2]
      · simp [ψ.zero_on_compl hz]
    rwa [heq] at hlimD
  refine ⟨R, hR, ?_, ?_⟩
  · classical
    intro v w φ
    have hfinite (u : ComplexModel d) (ψ : TestFunction Ω ℂ ⊤) :
        (∫ z, coordinateForm nabla e c z u * ψ z) =
          ∑ k : Fin d, DistributionalSection.regularPairing Ω
            (fun z ↦ coordinateForm nabla e c z (Pi.single k 1)) ψ * u k := by
      have hint (k : Fin d) : Integrable
          (fun z ↦ ψ z * coordinateForm nabla e c z (Pi.single k 1)) :=
        ψ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
          (((hcontinuous V e c hc).clm_apply continuousOn_const).locallyIntegrableOn
            Ω.isOpen.measurableSet)
      calc
        _ = ∫ z, ∑ k : Fin d,
            (ψ z * coordinateForm nabla e c z (Pi.single k 1)) * u k := by
          apply integral_congr_ae
          filter_upwards [] with z
          by_cases hz : z ∈ Ω
          · rw [real_linear_type_one_coordinate_sum (coordinateForm nabla e c z)
                (native_coordinate_form_type_one U nabla hcompatible V e c hc z hz) u,
              Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            simp only [smul_eq_mul]
            ring
          · simp [ψ.zero_on_compl hz]
        _ = ∑ k : Fin d, (∫ z, ψ z * coordinateForm nabla e c z (Pi.single k 1)) * u k := by
          rw [integral_finsetSum _ (fun k hk ↦ (hint k).mul_const (u k))]
          simp only [integral_mul_const]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [DistributionalSection.regularPairing,
            setIntegral_eq_integral_of_forall_compl_eq_zero
              (fun z hz ↦ by simp [ψ.zero_on_compl hz])]
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z ↦ mul_comm _ _
    have hder (u : ComplexModel d) (z : ComplexModel d) :
        (TestFunction.lineDerivCLM ℂ u φ : TestFunction Ω ℂ ⊤) z =
          fderiv ℝ (φ : ComplexModel d → ℂ) z u := by
      rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
      exact (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
    have hlim := (hweak w (TestFunction.lineDerivCLM ℂ v φ)).neg.add
      (hweak v (TestFunction.lineDerivCLM ℂ w φ))
    rw [hfinite, hfinite, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib] at hlim
    simpa only [hder, ← hpair, neg_mul] using hlim
  · exact native_smooth_pullback_curvature_l2_decay hd f a hstable U hU_real hU Ds
      (fun n ↦ (hDs n).1) (fun n ↦ (hDs n).2) hrec V e c hc

end HolomorphicAnosov.ConnectionFlatEstimates
