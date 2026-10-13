import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The differential of the Riemannian exponential at a zero tangent vector sends horizontal and
vertical tangent vectors to their sum. -/
theorem riemannianExponential_mfderiv_zero_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) (u w : E) :
    mfderiv (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) (riemannianExponential g)
      (⟨p,0⟩ : TangentBundle 𝓘(ℝ,E) M) (u,w) = u+w := by
  obtain ⟨hD,he⟩ := riemannianExponential_open_smooth g
  have he' := ((he.contMDiffAt (hD.mem_nhds (riemannianExponential_zero g p).1)).mdifferentiableAt
    (by simp))
  have hp : MDifferentiableAt (𝓘(ℝ,E)).tangent 𝓘(ℝ,E)
      (Bundle.TotalSpace.proj : TangentBundle 𝓘(ℝ,E) M → M) ⟨p,0⟩ :=
    (Bundle.mdifferentiable_proj (TangentSpace 𝓘(ℝ,E))).mdifferentiableAt
  have hprod := mfderiv_prodMk hp he'
  have hh := congrArg Prod.snd (riemannianExponentialAddition_horizontal_derivative g p u)
  have hj (v : E) : mfderiv 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent
      (fun z : E ↦ (⟨p,(tangentSpaceCastModel 𝓘(ℝ,E) p).symm z⟩ : TangentBundle 𝓘(ℝ,E) M))
      0 ((tangentSpaceCastModel 𝓘(ℝ,E) (0 : E)).symm v) = (0,v) := by
    rw [W07FibreInsertionDerivative.mfderiv_fibreInsertion]
    rfl
  have hv := congrArg Prod.snd (riemannianExponentialAddition_vertical_derivative g p w (hj w))
  change (mfderiv (𝓘(ℝ,E)).tangent ((𝓘(ℝ,E)).prod 𝓘(ℝ,E))
    (fun z : TangentBundle 𝓘(ℝ,E) M ↦ (z.proj,riemannianExponential g z)) ⟨p,0⟩ (u,0)).2 = u at hh
  change (mfderiv (𝓘(ℝ,E)).tangent ((𝓘(ℝ,E)).prod 𝓘(ℝ,E))
    (fun z : TangentBundle 𝓘(ℝ,E) M ↦ (z.proj,riemannianExponential g z)) ⟨p,0⟩ (0,w)).2 = w at hv
  rw [hprod] at hh hv
  change mfderiv (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) (riemannianExponential g) ⟨p,0⟩ (u,0) = u at hh
  change mfderiv (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) (riemannianExponential g) ⟨p,0⟩ (0,w) = w at hv
  have hlin := (mfderiv (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) (riemannianExponential g)
    (⟨p,0⟩ : TangentBundle 𝓘(ℝ,E) M)).map_add (u,0) (0,w)
  change mfderiv (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) (riemannianExponential g) ⟨p,0⟩
    (u+0,0+w) = _ at hlin
  simpa only [add_zero,zero_add,hh,hv] using hlin

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- In the preferred tangent-bundle chart, a zero tangent vector has the ambient base coordinate and
zero fibre coordinate. -/
theorem extChartAt_tangent_zero_g18 (p : M) :
    extChartAt (𝓘(ℝ,E)).tangent (⟨p,0⟩ : TangentBundle 𝓘(ℝ,E) M) ⟨p,0⟩ =
      (extChartAt 𝓘(ℝ,E) p p,0) := by
  rw [FiberBundle.extChartAt]
  change ((extChartAt 𝓘(ℝ,E) p).prod (PartialEquiv.refl E))
    ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p) ⟨p,0⟩) = _
  have hz : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p) ⟨p,0⟩ = (p,0) := by
    simpa only [Bundle.zeroSection] using
      (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).zeroSection ℝ
        (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ,E)) p)
  rw [hz]
  rfl

/-- In the preferred ambient and tangent-bundle charts, the derivative of the exponential at a zero
vector is `(u, w) ↦ u + w`. -/
theorem riemannianExponential_coordinate_derivative_zero_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) :
    HasFDerivAt
      (writtenInExtChartAt (𝓘(ℝ,E)).tangent 𝓘(ℝ,E)
        (⟨p,0⟩ : TangentBundle 𝓘(ℝ,E) M) (riemannianExponential g))
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
      (extChartAt 𝓘(ℝ,E) p p,0) := by
  obtain ⟨hD,he⟩ := riemannianExponential_open_smooth g
  have hd := ((he.contMDiffAt (hD.mem_nhds (riemannianExponential_zero g p).1)).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have hcoord := hd.2
  have heq : (tangentSpaceCastModel 𝓘(ℝ,E) (riemannianExponential g ⟨p,0⟩)).toContinuousLinearMap.comp
      ((mfderiv (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) (riemannianExponential g) ⟨p,0⟩).comp
        (tangentSpaceCastModel (𝓘(ℝ,E)).tangent
          (⟨p,0⟩ : TangentBundle 𝓘(ℝ,E) M)).symm.toContinuousLinearMap) =
      ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    apply ContinuousLinearMap.ext
    intro z
    exact riemannianExponential_mfderiv_zero_g18 g p z.1 z.2
  rw [heq,extChartAt_tangent_zero_g18] at hcoord
  simpa only [ModelWithCorners.Boundaryless.range_eq_univ,hasFDerivWithinAt_univ] using hcoord

/-- The exponential coordinate map is smooth on an open neighborhood of the zero vector where the
tangent-chart inverse lies in the geodesic domain and the endpoint lies in the ambient chart. -/
theorem riemannianExponential_coordinate_domain_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) :
    let z₀ : TangentBundle 𝓘(ℝ,E) M := ⟨p,0⟩
    let a := writtenInExtChartAt (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) z₀ (riemannianExponential g)
    ∃ U : Set (E × E), IsOpen U ∧ (extChartAt 𝓘(ℝ,E) p p,0) ∈ U ∧
      ContDiffOn ℝ ∞ a U ∧ ∀ z ∈ U,
        z ∈ (extChartAt (𝓘(ℝ,E)).tangent z₀).target ∧
        (extChartAt (𝓘(ℝ,E)).tangent z₀).symm z ∈ riemannianExponentialDomain g ∧
        riemannianExponential g ((extChartAt (𝓘(ℝ,E)).tangent z₀).symm z) ∈
          (extChartAt 𝓘(ℝ,E) p).source := by
  dsimp only
  let z₀ : TangentBundle 𝓘(ℝ,E) M := ⟨p,0⟩
  let ct := extChartAt (𝓘(ℝ,E)).tangent z₀
  let cp := extChartAt 𝓘(ℝ,E) p
  obtain ⟨hD,he⟩ := riemannianExponential_open_smooth g
  have hct : ContMDiffOn 𝓘(ℝ,E × E) (𝓘(ℝ,E)).tangent ∞ ct.symm ct.target :=
    contMDiffOn_extChartAt_symm z₀
  let V := ct.target ∩ ct.symm ⁻¹' riemannianExponentialDomain g
  have hV : IsOpen V := hct.continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target z₀) hD
  have hev : ContMDiffOn 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞ (riemannianExponential g ∘ ct.symm) V :=
    he.comp (hct.mono inter_subset_left) (fun _ hz ↦ hz.2)
  let U := V ∩ (riemannianExponential g ∘ ct.symm) ⁻¹' cp.source
  have hU : IsOpen U := hev.continuousOn.isOpen_inter_preimage hV (isOpen_extChartAt_source p)
  have hzsrc : z₀ ∈ ct.source := mem_extChartAt_source z₀
  have hcoord : ct z₀ = (extChartAt 𝓘(ℝ,E) p p,0) := extChartAt_tangent_zero_g18 p
  have hpU : (extChartAt 𝓘(ℝ,E) p p,0) ∈ U := by
    rw [← hcoord]
    refine ⟨⟨ct.map_source hzsrc,?_⟩,?_⟩
    · change ct.symm (ct z₀) ∈ riemannianExponentialDomain g
      rw [ct.left_inv hzsrc]
      exact (riemannianExponential_zero g p).1
    · change riemannianExponential g (ct.symm (ct z₀)) ∈ cp.source
      rw [ct.left_inv hzsrc,(riemannianExponential_zero g p).2]
      exact mem_extChartAt_source p
  refine ⟨U,hU,hpU,?_,fun z hz ↦ ⟨hz.1.1,hz.1.2,hz.2⟩⟩
  have hcp : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ cp cp.source := by
    simpa only [cp,extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := p) (n := ∞))
  have hcomp := hcp.comp (hev.mono inter_subset_left) (fun _ hz ↦ hz.2)
  have heq : writtenInExtChartAt (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) z₀ (riemannianExponential g) =
      cp ∘ riemannianExponential g ∘ ct.symm := by
    simp only [writtenInExtChartAt,z₀,(riemannianExponential_zero g p).2]
    rfl
  rw [heq]
  exact hcomp.contDiffOn


omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Zero tangent vectors based in a fixed chart have zero fibre coordinate. -/
theorem extChartAt_tangent_zero_at_g18 (a p : M)
    (hp : p ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    extChartAt (𝓘(ℝ,E)).tangent (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) ⟨p,0⟩ =
      (extChartAt 𝓘(ℝ,E) a p,0) := by
  rw [FiberBundle.extChartAt]
  change ((extChartAt 𝓘(ℝ,E) a).prod (PartialEquiv.refl E))
    ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) a) ⟨p,0⟩) = _
  have hp' : p ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using hp
  have hz : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a) ⟨p,0⟩ = (p,0) := by
    simpa only [Bundle.zeroSection] using
      (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).zeroSection ℝ hp'
  rw [hz]
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The inverse of a fixed tangent-bundle chart recovers the tangent vector given by the inverse
frame. -/
theorem extChartAt_tangent_symm_fibre_g18 (a p : M)
    (hp : p ∈ (extChartAt 𝓘(ℝ,E) a).source) (w : E) :
    let hp' : p ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using hp
    (extChartAt (𝓘(ℝ,E)).tangent (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)).symm
      (extChartAt 𝓘(ℝ,E) a p,w) =
      ⟨p,((trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).continuousLinearEquivAt ℝ p hp').symm w⟩ := by
  dsimp only
  rw [FiberBundle.extChartAt]
  change (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).toOpenPartialHomeomorph.symm
    ((extChartAt 𝓘(ℝ,E) a).symm (extChartAt 𝓘(ℝ,E) a p),w) = _
  rw [(extChartAt 𝓘(ℝ,E) a).left_inv hp]
  exact (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).symm_apply_eq_mk_continuousLinearEquivAt_symm p _ w

/-- The exponential expressed in a fixed chart is smooth on an open coordinate neighborhood of each
zero vector based in that chart. -/
theorem riemannianExponential_fixed_coordinate_domain_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (a p : M) (hp : p ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    let ct := extChartAt (𝓘(ℝ,E)).tangent (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)
    let ca := extChartAt 𝓘(ℝ,E) a
    let A := ca ∘ riemannianExponential g ∘ ct.symm
    ∃ U : Set (E × E), IsOpen U ∧ (ca p,0) ∈ U ∧ ContDiffOn ℝ ∞ A U ∧
      ∀ z ∈ U, z ∈ ct.target ∧ ct.symm z ∈ riemannianExponentialDomain g ∧
        riemannianExponential g (ct.symm z) ∈ ca.source := by
  dsimp only
  let ct := extChartAt (𝓘(ℝ,E)).tangent (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)
  let ca := extChartAt 𝓘(ℝ,E) a
  obtain ⟨hD,he⟩ := riemannianExponential_open_smooth g
  have hct : ContMDiffOn 𝓘(ℝ,E × E) (𝓘(ℝ,E)).tangent ∞ ct.symm ct.target :=
    contMDiffOn_extChartAt_symm (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)
  let V := ct.target ∩ ct.symm ⁻¹' riemannianExponentialDomain g
  have hV : IsOpen V := hct.continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target _) hD
  have hev : ContMDiffOn 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞ (riemannianExponential g ∘ ct.symm) V :=
    he.comp (hct.mono inter_subset_left) (fun _ hz ↦ hz.2)
  let U := V ∩ (riemannianExponential g ∘ ct.symm) ⁻¹' ca.source
  have hU : IsOpen U := hev.continuousOn.isOpen_inter_preimage hV (isOpen_extChartAt_source a)
  have hzsrc : (⟨p,0⟩ : TangentBundle 𝓘(ℝ,E) M) ∈ ct.source := by
    simpa only [ct,extChartAt_source,TangentBundle.mem_chart_source_iff] using hp
  have hc : ct ⟨p,0⟩ = (ca p,0) := extChartAt_tangent_zero_at_g18 a p hp
  have hpU : (ca p,0) ∈ U := by
    rw [← hc]
    refine ⟨⟨ct.map_source hzsrc,?_⟩,?_⟩
    · change ct.symm (ct ⟨p,0⟩) ∈ riemannianExponentialDomain g
      rw [ct.left_inv hzsrc]
      exact (riemannianExponential_zero g p).1
    · change riemannianExponential g (ct.symm (ct ⟨p,0⟩)) ∈ ca.source
      rw [ct.left_inv hzsrc,(riemannianExponential_zero g p).2]
      exact hp
  refine ⟨U,hU,hpU,?_,fun z hz ↦ ⟨hz.1.1,hz.1.2,hz.2⟩⟩
  have hca : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ ca ca.source := by
    simpa only [ca,extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := a) (n := ∞))
  exact (hca.comp (hev.mono inter_subset_left) (fun _ hz ↦ hz.2)).contDiffOn


/-- The vertical derivative of the exponential in fixed coordinates is the identity at each zero
vector. -/
theorem riemannianExponential_fixed_coordinate_vertical_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (a p : M) (hp : p ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    HasFDerivAt (fun w : E ↦ extChartAt 𝓘(ℝ,E) a (riemannianExponential g
      ((extChartAt (𝓘(ℝ,E)).tangent (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)).symm
        (extChartAt 𝓘(ℝ,E) a p,w)))) (ContinuousLinearMap.id ℝ E) 0 := by
  let ca := extChartAt 𝓘(ℝ,E) a
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) a
  have hp' : p ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hp
  let J := tr.continuousLinearEquivAt ℝ p hp'
  let ep : E → M := fun v ↦ riemannianExponential g
    ⟨p,(tangentSpaceCastModel 𝓘(ℝ,E) p).symm v⟩
  have hep : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) ep 0 :=
    (riemannianExponential_fibre_contMDiffAt_zero g p).mdifferentiableAt (by simp)
  have hepd : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ep 0 = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro w
    exact riemannianExponential_vertical_derivative g p hep w
  have hep' : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) ep 0 (ContinuousLinearMap.id ℝ E) := by
    rw [← hepd]
    exact hep.hasMFDerivAt
  have hJ : J.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca p := by
    rw [show J.toContinuousLinearMap = tr.continuousLinearMapAt ℝ p from
      tr.coe_continuousLinearEquivAt_eq' hp']
    exact TangentBundle.continuousLinearMapAt_trivializationAt (by simpa only [extChartAt_source] using hp)
  have hca : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) ca (ep 0) J.toContinuousLinearMap := by
    have heq : ep 0 = p := by simpa only [ep,map_zero] using (riemannianExponential_zero g p).2
    rw [heq,hJ]
    exact (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hp)).hasMFDerivAt
  let J₀ : E ≃L[ℝ] E := (tangentSpaceCastModel 𝓘(ℝ,E) p).symm.trans J
  have hcomp := hca.comp 0 hep'
  have hcompF : HasFDerivAt (ca ∘ ep) J₀.toContinuousLinearMap 0 := by
    change HasFDerivAt (ca ∘ ep) (J.toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ E)) 0
    exact hcomp.hasFDerivAt
  have hcomp' := (by simpa only [map_zero] using hcompF :
      HasFDerivAt (ca ∘ ep) J₀.toContinuousLinearMap (J₀.symm 0)).comp 0
        J₀.symm.toContinuousLinearMap.hasFDerivAt
  convert hcomp' using 1
  · funext w
    rw [extChartAt_tangent_symm_fibre_g18 a p hp w]
    change ca (riemannianExponential g ⟨p,J.symm w⟩) =
      ca (riemannianExponential g ⟨p,(tangentSpaceCastModel 𝓘(ℝ,E) p).symm
        (tangentSpaceCastModel 𝓘(ℝ,E) p (J.symm w))⟩)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · apply ContinuousLinearMap.ext
    intro w
    exact (J₀.apply_symm_apply w).symm

/-- The derivative of the exponential in a fixed receiving chart at each zero vector is `(u, w) ↦ u
+ w`. -/
theorem riemannianExponential_fixed_coordinate_derivative_zero_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (a p : M) (hp : p ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    let ct := extChartAt (𝓘(ℝ,E)).tangent (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)
    let ca := extChartAt 𝓘(ℝ,E) a
    HasFDerivAt (ca ∘ riemannianExponential g ∘ ct.symm)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (ca p,0) := by
  let ct := extChartAt (𝓘(ℝ,E)).tangent (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)
  let ca := extChartAt 𝓘(ℝ,E) a
  let A := ca ∘ riemannianExponential g ∘ ct.symm
  obtain ⟨U,hU,hpU,hAU,_⟩ := riemannianExponential_fixed_coordinate_domain_g18 g a p hp
  have hA : HasFDerivAt A (fderiv ℝ A (ca p,0)) (ca p,0) :=
    (hAU.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp) |>.hasFDerivAt
  have heq : (fun y : E ↦ A (y,0)) =ᶠ[nhds (ca p)] id := by
    filter_upwards [(isOpen_extChartAt_target a).mem_nhds (ca.map_source hp)] with y hy
    have h := extChartAt_tangent_symm_fibre_g18 a (ca.symm y) (ca.map_target hy) (0 : E)
    change ca (riemannianExponential g (ct.symm (y,0))) = y
    have hzero : ct.symm (y,0) = (⟨ca.symm y,0⟩ : TangentBundle 𝓘(ℝ,E) M) := by
      simp only [map_zero] at h
      change ct.symm (ca (ca.symm y),0) = (⟨ca.symm y,0⟩ : TangentBundle 𝓘(ℝ,E) M) at h
      rwa [ca.right_inv hy] at h
    rw [hzero,(riemannianExponential_zero g (ca.symm y)).2,ca.right_inv hy]
  have hh : (fderiv ℝ A (ca p,0)).comp (ContinuousLinearMap.inl ℝ E E) =
      ContinuousLinearMap.id ℝ E := by
    have h := (hA.comp (ca p) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (ca p) (0 : E))).fderiv
    change fderiv ℝ (fun y ↦ A (y,0)) (ca p) = _ at h
    rw [heq.fderiv_eq,fderiv_id] at h
    exact h.symm
  have hv : (fderiv ℝ A (ca p,0)).comp (ContinuousLinearMap.inr ℝ E E) =
      ContinuousLinearMap.id ℝ E := by
    have h := hA.comp 0 (hasFDerivAt_prodMk_right (𝕜 := ℝ) (ca p) (0 : E))
    exact h.unique (riemannianExponential_fixed_coordinate_vertical_g18 g a p hp)
  have hfull : fderiv ℝ A (ca p,0) =
      ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    apply ContinuousLinearMap.ext
    rintro ⟨u,w⟩
    change fderiv ℝ A (ca p,0) (u,w) = u+w
    have hu := congrArg (fun T : E →L[ℝ] E ↦ T u) hh
    have hw := congrArg (fun T : E →L[ℝ] E ↦ T w) hv
    have hsum := (fderiv ℝ A (ca p,0)).map_add (u,0) (0,w)
    simpa only [Prod.mk_add_mk,add_zero,zero_add,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,ContinuousLinearMap.id_apply] using
      hsum.trans (congrArg₂ (· + ·) hu hw)
  rw [← hfull]
  exact hA

end HolomorphicAnosov




