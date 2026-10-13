import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.HyperplaneCurvatureJacobianBoundG6
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.NativeBilinearHermitianBoundG6
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NormalizedPullbackPreparation
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExistsNoConnected
import HolomorphicAnosov.Geometry.HermitianMetricVolumeJacobian
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NativeTopFormChartIntegral
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
open scoped Manifold ContDiff Topology _root_.Topology BigOperators
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov.ConnectionFlatEstimates
open HolomorphicAnosov QuotientLineConnection

/-- A nonnegative curvature integral bounded by the geometric decay factor tends to zero in complex
dimension at least three. (Zhang, eq. (11)) -/
theorem native_l2_decay_from_geometric_bound {d : ℕ}
    (Ω : Opens (ComplexModel d))
    (R : ℕ → (ComplexModel d) → (ComplexModel d) → (ComplexModel d) → ℂ)
    (C rate vol : ℝ) (hd : 3 ≤ d) (hrate : 1 < rate)
    (hbound : ∀ n (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤),
      0 ≤ ∫ z in tsupport φ, ‖R n v w z‖ ^ 2 ∂volume ∧
      ∫ z in tsupport φ, ‖R n v w z‖ ^ 2 ∂volume ≤
        C * ((rate ^ (2 * (d - 2)))⁻¹) ^ n * vol) :
    ∀ v w (φ : TestFunction Ω ℂ ⊤),
      Tendsto (fun n ↦ ∫ z in tsupport φ, ‖R n v w z‖ ^ 2 ∂volume)
        atTop (nhds 0) := by
  intro v w φ
  have hfac : Tendsto (fun n : ℕ ↦ C * ((rate ^ (2 * (d - 2)))⁻¹) ^ n * vol)
      atTop (nhds 0) := curvature_decay_factor_tendsto hd hrate C vol
  exact squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ (hbound n v w φ).1))
    (Filter.Eventually.of_forall (fun n ↦ (hbound n v w φ).2)) (by simpa using hfac)

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The squared L² integrals of coordinate curvature evaluations of a smooth compatible pullback
sequence tend to zero on every compact test support. (Zhang, eqs. (8)–(11), pp. 6–7) -/
theorem native_smooth_pullback_curvature_l2_decay
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
    (Ds : ℕ → Connection U)
    (hsmooth : ∀ n (V : Opens X) (e : HolomorphicFrame U V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (coordinateForm (Ds n) e c)
        (c.target ∩ c.symm ⁻¹' (V : Set X)))
    (hcomp : ∀ n, IsCompatible (Ds n))
    (hrec : ∀ n (V W : Opens X) (e : HolomorphicFrame U V)
      (e' : HolomorphicFrame U W) (x : X), x ∈ V → f x ∈ W →
      (Ds (n + 1)).form V e x = (imageFrameCoefficient f hU e e' x)⁻¹ •
        realDifferential (imageFrameCoefficient f hU e e') x +
        ((Ds n).form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x)) :
    ∀ (V : Opens X) (e : HolomorphicFrame U V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      let Ω : Opens (ComplexModel d) :=
        ⟨c.target ∩ c.symm ⁻¹' (V : Set X), c.isOpen_inter_preimage_symm V.isOpen⟩
      ∀ (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤),
        Tendsto (fun n ↦ ∫ z in tsupport φ,
          ‖fderiv ℝ (coordinateForm (Ds n) e c) z v w -
            fderiv ℝ (coordinateForm (Ds n) e c) z w v‖ ^ 2 ∂volume)
          atTop (nhds 0) := by
  classical
  let : TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨P, hP, hP_real⟩ := rank_one_stable_holomorphic_unstable (by omega) f a hstable
  have hPU : P = U := by
    funext x
    exact submodule_eq_of_realification_eq x (P x) (U x)
      ((hP_real x).trans (hU_real x).symm)
  subst P
  have hline := quotient_line_of_holomorphic_codimension_one (by omega : 1 ≤ d) U hP
  obtain ⟨hcover, -, -, -, -, -, -, hlocal, -, -, -, hcurvature, hnaturality⟩ :=
    ConnectionCalculus.zhang_connection_calculus U hP hline
      (unstable_bott_involutive f a U hU_real)
  have hcovrestrict (D : Connection U) (V W : Opens X) (e : HolomorphicFrame U V)
      (hWV : W ≤ V) (s : (x : X) → Fibre U x) (x : X) (hx : x ∈ W)
      (v : TangentSpace (realModel d) x) :
      covariantDerivative D (ConnectionCalculus.holomorphicFrameRestrict e hWV) s x hx v =
        covariantDerivative D e s x (hWV hx) v := by
    let er := ConnectionCalculus.holomorphicFrameRestrict e hWV
    have heq : er.coefficient s =ᶠ[nhds x] e.coefficient s := by
      filter_upwards [W.isOpen.mem_nhds hx] with y hy
      simp only [HolomorphicFrame.coefficient]
      rw [dite_eq_left (show y ∈ W from hy), dite_eq_left (hWV hy)]
      rfl
    have hg : e.coefficient er.sectionValue =ᶠ[nhds x] (fun _ ↦ (1 : ℂ)) := by
      filter_upwards [V.isOpen.mem_nhds (hWV hx)] with y hy
      simp only [HolomorphicFrame.coefficient]
      rw [dite_eq_left (show y ∈ V from hy)]
      exact e.normalized y hy
    have hd : realDifferential (d := d) (er.coefficient s) x =
        realDifferential (e.coefficient s) x := by
      unfold realDifferential
      rw [heq.eq_of_nhds, heq.mfderiv_eq]
      rfl
    have hdg : realDifferential (d := d) (e.coefficient er.sectionValue) x = 0 := by
      unfold realDifferential
      rw [hg.mfderiv_eq]
      simp
    have hform : D.form W er x = D.form V e x := by
      rw [D.gauge V W e er x (hWV hx) hx, hdg]
      ext v
      simp
    change covariantDerivative D er s x hx v = _
    simp only [covariantDerivative, hd, heq.eq_of_nhds, hform]
    rfl
  have hlocalform (n : ℕ) (c : OpenPartialHomeomorph X (ComplexModel d))
      (j : Fin d) (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
      (hker : ∀ x ∈ c.source, U x = LinearMap.ker
        (((ContinuousLinearMap.proj j).comp
          ((tangentSpaceCastModel (complexModel d) (c x)).toContinuousLinearMap.comp
            (mfderiv (complexModel d) (complexModel d) c x))).toLinearMap)) :
      ∃ e : HolomorphicFrame U ⟨c.source, c.open_source⟩,
        ∃ b : ComplexModel d → ℂ, ContDiffOn ℝ ∞ b c.target ∧
          ∀ z ∈ c.target, coordinateForm (Ds n) e c z =
            b z • (ContinuousLinearMap.proj j : ComplexModel d →L[ℂ] ℂ).restrictScalars ℝ := by
    obtain ⟨e, he, hcriterion⟩ := hlocal c j hc hker
    refine ⟨e, (hcriterion (Ds n) (hsmooth n)).mp ?_⟩
    refine ⟨fun V e x hx _ v ↦ (hcomp n).1 V e x hx v, ?_⟩
    intro V e Y Z hY hZ hYP x hx hxc
    let W : Opens X := V ⊓ ⟨c.source, c.open_source⟩
    have hxW : x ∈ W := ⟨hx, hxc⟩
    have hh := (hcomp n).2 W (ConnectionCalculus.holomorphicFrameRestrict e inf_le_left)
      Y Z hY hZ hYP x hxW
    simpa only [hcovrestrict] using hh
  choose R hR hRunique using fun n ↦ hcurvature (Ds n) (hsmooth n)
  have hRfoliation (n : ℕ) (c : OpenPartialHomeomorph X (ComplexModel d))
      (j : Fin d) (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
      (hker : ∀ x ∈ c.source, U x = LinearMap.ker
        (((ContinuousLinearMap.proj j).comp
          ((tangentSpaceCastModel (complexModel d) (c x)).toContinuousLinearMap.comp
            (mfderiv (complexModel d) (complexModel d) c x))).toLinearMap)) :
      ∃ b : ComplexModel d → ℂ, ContDiffOn ℝ ∞ b c.target ∧
        ∀ z ∈ c.target, ∀ v w : ComplexModel d,
          R n (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z
              ((NormedSpace.fromTangentSpace z).symm v))
            (mfderiv (realModel d) (realModel d) c.symm z
              ((NormedSpace.fromTangentSpace z).symm w)) =
            fderiv ℝ b z v * w j - fderiv ℝ b z w * v j := by
    obtain ⟨e, b, hb, hform⟩ := hlocalform n c j hc hker
    refine ⟨b, hb, ?_⟩
    intro z hz v w
    rw [(hR n).1 ⟨c.source, c.open_source⟩ e c hc z ⟨hz, c.map_target hz⟩]
    have heq : coordinateForm (Ds n) e c =ᶠ[nhds z]
        (fun t ↦ b t • (ContinuousLinearMap.proj j : ComplexModel d →L[ℂ] ℂ).restrictScalars ℝ) :=
      by
        filter_upwards [c.open_target.mem_nhds hz] with t ht
        exact hform t ht
    rw [heq.fderiv_eq]
    rw [fderiv_smul_const ((hb.differentiableOn (by simp) z hz).differentiableAt
      (c.open_target.mem_nhds hz))
      ((ContinuousLinearMap.proj j : ComplexModel d →L[ℂ] ℂ).restrictScalars ℝ)]
    rfl
  have hnative : ∀ x, Nonempty (NativeAsymptoticLeafDatum (realModel d)
      f.toHomeomorph.symm a.splitting.unstable.toDistribution x) :=
    exists_native_unstable_leaf_data_of_anosov f a hstable
  let native : ∀ x, NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph.symm
      a.splitting.unstable.toDistribution x := fun x ↦ Classical.choice (hnative x)
  have hRkernel (n : ℕ) (x : X) (v w : TangentSpace (complexModel d) x)
      (hv : v ∈ U x) (hw : w ∈ U x) :
      R n x (complexTangentToReal d x v) (complexTangentToReal d x w) = 0 := by
    obtain ⟨box, c, hxbox, hsource, hc, hker⟩ :=
      SingleBundleHolomorphicBox.exists_native_single_bundle_foliation_chart
        (by omega) f.toHomeomorph.symm U hP
        a.splitting.unstable.toDistribution hU_real native x
    have hx : x ∈ c.source := hsource.symm ▸ hxbox
    let j : Fin d := ⟨0, by omega⟩
    obtain ⟨b, hb, hbf⟩ := hRfoliation n c j hc hker
    have hcD : c.MDifferentiable (complexModel d) (complexModel d) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
    let vc := tangentSpaceCastModel (complexModel d) (c x)
      (mfderiv (complexModel d) (complexModel d) c x v)
    let wc := tangentSpaceCastModel (complexModel d) (c x)
      (mfderiv (complexModel d) (complexModel d) c x w)
    have hvj : vc j = 0 := by
      rw [hker x hx] at hv
      exact hv
    have hwj : wc j = 0 := by
      rw [hker x hx] at hw
      exact hw
    have hback (t : TangentSpace (complexModel d) x) :
        mfderiv (realModel d) (realModel d) c.symm (c x)
          ((NormedSpace.fromTangentSpace (c x)).symm
            (tangentSpaceCastModel (complexModel d) (c x)
              (mfderiv (complexModel d) (complexModel d) c x t))) =
          complexTangentToReal d x t := by
      have hr := mfderiv_complex_to_real (hcD.mdifferentiableAt_symm (c.map_source hx))
        (mfderiv (complexModel d) (complexModel d) c x t)
      change mfderiv (realModel d) (realModel d) c.symm (c x)
        (complexTangentToReal d (c x)
          (mfderiv (complexModel d) (complexModel d) c x t)) = _
      rw [hr]
      have hi := congrArg (fun L ↦ L t) (hcD.symm_comp_deriv hx)
      change mfderiv (complexModel d) (complexModel d) c.symm (c x)
        (mfderiv (complexModel d) (complexModel d) c x t) = t at hi
      rw [hi]
      rfl
    have hh := hbf (c x) (c.map_source hx) vc wc
    rw [hvj, hwj, mul_zero, mul_zero, sub_self] at hh
    simp only [vc, wc, hback] at hh
    have he := congrArg (fun y : X ↦ R n y
      ((tangentSpaceCastModel (realModel d) y).symm
        (tangentSpaceCastModel (realModel d) x (complexTangentToReal d x v)))
      ((tangentSpaceCastModel (realModel d) y).symm
        (tangentSpaceCastModel (realModel d) x (complexTangentToReal d x w))))
      (c.left_inv hx)
    exact he.symm.trans hh
  have hRstep (n : ℕ) (x : X) (v w : TangentSpace (realModel d) x) :
      R (n + 1) x v w = R n (f x)
        (mfderiv (realModel d) (realModel d) f x v)
        (mfderiv (realModel d) (realModel d) f x w) :=
    hnaturality f hU (Ds n) (Ds (n + 1)) (hsmooth n) (hsmooth (n + 1))
      (hrec n) (R n) (R (n + 1)) (hR n).1 (hR (n + 1)).1 x v w
  have hfreal : ContMDiff (realModel d) (realModel d) ∞ (f : X → X) :=
    f.toReal.contMDiff
  have hRiterate (n : ℕ) (x : X) (v w : TangentSpace (realModel d) x) :
      R n x v w = R 0 ((f : X → X)^[n] x)
        (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x v)
        (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x w) := by
    induction n generalizing x with
    | zero => simp only [Function.iterate_zero, id_eq, mfderiv_id]; rfl
    | succ n ih =>
      rw [hRstep, ih, Function.iterate_succ]
      simp only [mfderiv_comp_apply x
        ((hfreal.iterate n).mdifferentiable (by simp) (f x))
        (hfreal.mdifferentiable (by simp) x)]
      rfl
  have hRcoeff (x : X) :
      let t := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
      ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ⊆ t.baseSet ∧
        ∃ A : X → ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℂ,
          ContinuousOn A O ∧ ∀ y ∈ O, ∀ v w,
            R 0 y (t.symm y v) (t.symm y w) = A y v w := by
    intro t
    let c := chartAt (ComplexModel d) x
    have hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
      IsManifold.chart_mem_maximalAtlas x
    obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
    let O := c.source ∩ (V : Set X)
    let Ω := c.target ∩ c.symm ⁻¹' (V : Set X)
    have hΩ : IsOpen Ω := c.isOpen_inter_preimage_symm V.isOpen
    let A : ComplexModel d → ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℂ := fun z ↦
      fderiv ℝ (coordinateForm (Ds 0) e c) z -
        (fderiv ℝ (coordinateForm (Ds 0) e c) z).flip
    have hA : ContinuousOn A Ω := by
      have hder := (hsmooth 0 V e c hc).continuousOn_fderiv_of_isOpen hΩ (by simp)
      exact hder.sub ((ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel d)
        (ComplexModel d) ℂ).continuous.comp_continuousOn hder)
    have hcO : MapsTo c O Ω := by
      intro y hy
      exact ⟨c.map_source hy.1, by change c.symm (c y) ∈ V; rw [c.left_inv hy.1]; exact hy.2⟩
    refine ⟨O, c.open_source.inter V.isOpen, ⟨mem_chart_source _ _, hxV⟩,
      (fun _ hy ↦ hy.1), (fun y ↦ A (c y)),
      hA.comp (c.continuousOn.mono inter_subset_left) hcO, ?_⟩
    intro y hy v w
    have hcurve := (hR 0).1 V e c hc (c y) (hcO hy) v w
    have hinv := TangentBundle.symmL_trivializationAt (I := realModel d)
      (x₀ := x) (x := y) hy.1
    simp only [realModel, modelWithCornersSelf_coe, Set.range_id,
      mfderivWithin_univ] at hinv
    change t.symmL ℝ y = mfderiv (realModel d) (realModel d) c.symm (c y) at hinv
    have hback (a : ComplexModel d) :
        mfderiv (realModel d) (realModel d) c.symm (c y)
          ((NormedSpace.fromTangentSpace (c y)).symm a) = t.symm y a := by
      change mfderiv (realModel d) (realModel d) c.symm (c y) a = _
      rw [← hinv]
      exact Bundle.Trivialization.symmL_apply (R := ℝ) t hy.1 a
    have htransport := congrArg (fun z : X ↦ R 0 z
      ((tangentSpaceCastModel (realModel d) z).symm
        (tangentSpaceCastModel (realModel d) y (t.symm y v)))
      ((tangentSpaceCastModel (realModel d) z).symm
        (tangentSpaceCastModel (realModel d) y (t.symm y w)))) (c.left_inv hy.1)
    have heval := congrArg₂ (fun v w ↦ R 0 (c.symm (c y)) v w) (hback v) (hback w)
    exact htransport.symm.trans (heval.symm.trans hcurve)
  obtain ⟨metric, hmetric⟩ :=
    OneFormBundle.original_smooth_tangent_metric_exists_no_connected (d := d) (M := X)
  obtain ⟨curvatureC, hcurvatureC, hcurvaturebound⟩ :=
    uniform_native_bilinear_hermitian_bound (R 0) hRcoeff metric hmetric
  choose S hSrank hSreal using hstable
  have hsplit (x : X) : IsCompl (S x) (U x) := by
    apply isCompl_of_realifications (complexTangentToReal d x).toLinearEquiv
    rw [hSreal x, hU_real x]
    exact a.splitting.isCompl x
  have hSmap (x : X) : (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x) :=
    complex_map_of_original_map f x (S x) (S (f x)) _ _ (hSreal x) (hSreal (f x))
      (a.splitting.stable_map x)
  have hUmap (x : X) : (U x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = U (f x) :=
    complex_map_of_original_map f x (U x) (U (f x)) _ _ (hU_real x) (hU_real (f x))
      (a.splitting.unstable_map x)
  have hUrank (x : X) : Module.finrank ℂ (U x) = d - 1 := by
    have hh := Submodule.finrank_add_eq_of_isCompl (hsplit x)
    rw [hSrank] at hh
    have htdim : Module.finrank ℂ (TangentSpace (complexModel d) x) = d := by
      change Module.finrank ℂ (ComplexModel d) = d
      simp [ComplexModel]
    rw [htdim] at hh
    omega
  obtain ⟨g, hgpos, hgcont, hgcontract⟩ :=
    anosov_original_complex_block_bounds f a S U hSreal hU_real
  obtain ⟨A, B, rate, hA, hB, hrate, hoperators⟩ :=
    compact_anosov_hermitian_operator_bounds f S U a.splitting.stable a.splitting.unstable
      hSreal hU_real hsplit hSmap hUmap (fun x ↦ by rw [hUrank]; omega)
      g hgpos hgcont a.k a.one_le_k hgcontract metric hmetric
  let η := hermitianMetricPreferredTopForm metric
  have hη : IsSmoothPositiveRealTangentTopForm η :=
    (hermitian_metric_volume_jacobian metric hmetric).1
  have hscalar := (hermitian_metric_volume_jacobian metric hmetric).2.2.2
  choose J hJsmooth hJpos hJpull hJunique hJdet using hscalar
  let Rc (y : X) : TangentSpace (complexModel d) y →ₗ[ℝ]
      TangentSpace (complexModel d) y →ₗ[ℝ] ℂ :=
    { toFun := fun v ↦
        { toFun := fun w ↦ R 0 y (complexTangentToReal d y v) (complexTangentToReal d y w)
          map_add' := by intro v w; simp
          map_smul' := by intro r w; simp }
      map_add' := by intro v w; ext z; simp
      map_smul' := by intro r v; ext z; simp }
  have hpoint (n : ℕ) (x : X) (v w : TangentSpace (complexModel d) x) :
      ‖R n x (complexTangentToReal d x v) (complexTangentToReal d x w)‖ ^ 2 ≤
        (2 * curvatureC * B) ^ 2 * J (hermitianBoundsIterate f n) x *
          hermitianBoundsNorm metric x v ^ 2 * hermitianBoundsNorm metric x w ^ 2 /
            (A⁻¹ * rate ^ n) ^ (2 * (d - 2)) := by
    let y := hermitianBoundsIterate f n x
    let F := hermitianBoundsDerivative f n x
    have hmap : (U x).map F.toLinearMap = U y :=
      CompactHermitianBoundsScratch.actual_iterate_subspace_invariant f U hUmap n x
    have hμ : 0 < A⁻¹ * rate ^ n :=
      mul_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hA))
        (pow_pos (lt_trans zero_lt_one hrate) n)
    have hdim (z : X) : Module.finrank ℂ (TangentSpace (complexModel d) z) = d := by
      change Module.finrank ℂ (ComplexModel d) = d
      simp [ComplexModel]
    obtain ⟨bs, bt, hbs, hbt, hbound⟩ := core_bilinear_pullback_conorm_bound
      (metric x) (metric y) (U x) (U y) F.toLinearEquiv hmap d (by omega)
      (hdim x) (hdim y) (hUrank x) (hUrank y) (Rc y)
      curvatureC B (A⁻¹ * rate ^ n) (zero_le_one.trans hcurvatureC) hB.le hμ
      (hcurvaturebound y) (fun v hv w hw ↦ hRkernel 0 y v w hv hw) (hoperators n x).2.2.2
      (hoperators n x).2.2.1
    have hdet : J (hermitianBoundsIterate f n) x =
        ‖(LinearMap.toMatrix bs bt F.toLinearMap).det‖ ^ 2 :=
      hJdet (hermitianBoundsIterate f n) x bs bt hbs hbt
    have hidentity : R n x (complexTangentToReal d x v) (complexTangentToReal d x w) =
        Rc y (F v) (F w) := by
      rw [hRiterate]
      have hf : MDifferentiableAt (complexModel d) (complexModel d) ((f : X → X)^[n]) x :=
        ((f.contMDiff.iterate n).mdifferentiable (by simp)) x
      rw [mfderiv_complex_to_real hf v, mfderiv_complex_to_real hf w]
      rfl
    rw [hidentity]
    apply (le_div_iff₀ (pow_pos hμ _)).mpr
    have hb := pow_le_pow_left₀
      (mul_nonneg (norm_nonneg (Rc y (F v) (F w))) (pow_nonneg hμ.le (d - 2)))
      (hbound v w) 2
    rw [hdet]
    dsimp only [hermitianBoundsNorm, HermitianFibreAlgebra.coreLength] at hb ⊢
    convert hb using 1 <;> ring
  intro V e c hc
  dsimp only
  intro v w φ
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
  have hKc : tsupport φ ⊆ c.target := fun z hz ↦ (φ.tsupport_subset hz).1
  obtain ⟨mass, hmass, hmassbound⟩ :=
    native_positive_jacobian_compact_chart_bound η hη c hc (tsupport φ) hK hKc
  have hJmass (F : Biholomorph d d X X) :
      (∫ z in tsupport φ, J F (c.symm z) ∂volume) ≤ mass :=
    hmassbound F (J F) (hJsmooth F).continuous (hJpos F) (hJpull F)
  let input (z : ComplexModel d) (v : ComplexModel d) :=
    mfderiv (complexModel d) (complexModel d) c.symm z
      ((NormedSpace.fromTangentSpace z).symm v)
  have hinputsum (z : ComplexModel d) (v : ComplexModel d) :
      (∑ i, v i • hermitianTangentChartFrame c z i) = input z v := by
    simp only [hermitianTangentChartFrame]
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1
    change (∑ i, v i • Pi.single i 1) = v
    exact (pi_eq_sum_univ' v).symm
  have hinputcont (v : ComplexModel d) : ContinuousOn
      (fun z ↦ hermitianBoundsNorm metric (c.symm z) (input z v)) c.target := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hh := (Preparation.continuous_hermitian_chart_frame_norm metric hmetric c hc).comp
      (continuous_id.prodMk (continuous_const (y := v)))
    change Continuous (fun z : c.target ↦
      Real.sqrt (((metric (c.symm z.val)).inner (input z.val v) (input z.val v)).re))
    simpa only [hinputsum, Function.comp_def, id_eq] using hh
  obtain ⟨Dv, hDv⟩ := hK.bddAbove_image ((hinputcont v).mono hKc)
  obtain ⟨Dw, hDw⟩ := hK.bddAbove_image ((hinputcont w).mono hKc)
  let D := max 0 (max Dv Dw)
  have hD : 0 ≤ D := le_max_left _ _
  have hinputv z (hz : z ∈ tsupport φ) :
      hermitianBoundsNorm metric (c.symm z) (input z v) ≤ D :=
    (hDv (Set.mem_image_of_mem _ hz)).trans
      ((le_max_left Dv Dw).trans (le_max_right 0 (max Dv Dw)))
  have hinputw z (hz : z ∈ tsupport φ) :
      hermitianBoundsNorm metric (c.symm z) (input z w) ≤ D :=
    (hDw (Set.mem_image_of_mem _ hz)).trans
      ((le_max_right Dv Dw).trans (le_max_right 0 (max Dv Dw)))
  let C := (2 * curvatureC * B) ^ 2 * D ^ 4 * A ^ (2 * (d - 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let decay (n : ℕ) := ((rate ^ (2 * (d - 2)))⁻¹) ^ n
  have hdecay (n : ℕ) : 0 ≤ decay n := by dsimp [decay]; positivity
  have hfac (n : ℕ) :
      ((A⁻¹ * rate ^ n) ^ (2 * (d - 2)))⁻¹ = A ^ (2 * (d - 2)) * decay n := by
    dsimp [decay]
    simp only [mul_pow, mul_inv_rev, inv_pow, inv_inv]
    rw [← pow_mul, Nat.mul_comm n (2 * (d - 2)), pow_mul]
    ring
  let b (n : ℕ) (z : ComplexModel d) :=
    fderiv ℝ (coordinateForm (Ds n) e c) z v w -
      fderiv ℝ (coordinateForm (Ds n) e c) z w v
  have hbcont (n : ℕ) : ContinuousOn (b n) (tsupport φ) := by
    have hh := (hsmooth n V e c hc).continuousOn_fderiv_of_isOpen
      (c.isOpen_inter_preimage_symm V.isOpen) (by simp)
    exact (((hh.clm_apply continuousOn_const).clm_apply continuousOn_const).sub
      ((hh.clm_apply continuousOn_const).clm_apply continuousOn_const)).mono φ.tsupport_subset
  have hlocal (n : ℕ) (z : ComplexModel d) (hz : z ∈ tsupport φ) :
      ‖b n z‖ ^ 2 ≤ (C * decay n) * J (hermitianBoundsIterate f n) (c.symm z) := by
    have hzΩ := φ.tsupport_subset hz
    have hid (a : ComplexModel d) :
        mfderiv (realModel d) (realModel d) c.symm z
          ((NormedSpace.fromTangentSpace z).symm a) =
            complexTangentToReal d (c.symm z) (input z a) :=
      mfderiv_complex_to_real
        ((contMDiffAt_symm_of_mem_maximalAtlas hc hzΩ.1).mdifferentiableAt (by simp))
        ((NormedSpace.fromTangentSpace z).symm a)
    have hr := (hR n).1 V e c hc z hzΩ v w
    have heval := congrArg₂ (fun v w ↦ R n (c.symm z) v w) (hid v) (hid w)
    have hcurv : b n z = R n (c.symm z)
        (complexTangentToReal d (c.symm z) (input z v))
        (complexTangentToReal d (c.symm z) (input z w)) := hr.symm.trans heval
    rw [hcurv]
    calc
      _ ≤ (2 * curvatureC * B) ^ 2 * J (hermitianBoundsIterate f n) (c.symm z) *
          hermitianBoundsNorm metric (c.symm z) (input z v) ^ 2 *
          hermitianBoundsNorm metric (c.symm z) (input z w) ^ 2 /
          (A⁻¹ * rate ^ n) ^ (2 * (d - 2)) := hpoint n (c.symm z) (input z v) (input z w)
      _ ≤ (2 * curvatureC * B) ^ 2 * J (hermitianBoundsIterate f n) (c.symm z) *
          D ^ 2 * D ^ 2 / (A⁻¹ * rate ^ n) ^ (2 * (d - 2)) := by
        have hJ := (hJpos (hermitianBoundsIterate f n) (c.symm z)).le
        have hv0 : 0 ≤ hermitianBoundsNorm metric (c.symm z) (input z v) := Real.sqrt_nonneg _
        have hw0 : 0 ≤ hermitianBoundsNorm metric (c.symm z) (input z w) := Real.sqrt_nonneg _
        gcongr
        · exact hinputv z hz
        · exact hinputw z hz
      _ = _ := by rw [div_eq_mul_inv, hfac]; dsimp [C]; ring
  have hint (n : ℕ) : IntegrableOn
      (fun z ↦ J (hermitianBoundsIterate f n) (c.symm z)) (tsupport φ) volume :=
    ((hJsmooth (hermitianBoundsIterate f n)).continuous.comp_continuousOn
      (c.symm.continuousOn.mono hKc)).integrableOn_compact hK
  have hbound (n : ℕ) : (∫ z in tsupport φ, ‖b n z‖ ^ 2 ∂volume) ≤ C * decay n * mass := by
    calc
      _ ≤ ∫ z in tsupport φ, (C * decay n) * J (hermitianBoundsIterate f n) (c.symm z) :=
        setIntegral_mono_on (((hbcont n).norm.pow 2).integrableOn_compact hK)
          ((hint n).const_mul _) hK.measurableSet (hlocal n)
      _ = (C * decay n) * ∫ z in tsupport φ, J (hermitianBoundsIterate f n) (c.symm z) :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hJmass _) (mul_nonneg hC (hdecay n))
  exact squeeze_zero' (Filter.Eventually.of_forall fun n ↦
    integral_nonneg fun z ↦ sq_nonneg ‖b n z‖)
    (Filter.Eventually.of_forall hbound) (curvature_decay_factor_tendsto hd hrate C mass)

end HolomorphicAnosov.ConnectionFlatEstimates

