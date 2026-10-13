import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.EndpointCertificate
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ManifoldInverse
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.FibreCoordinateMFDeriv
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.TangentHausdorff
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.CurveTangentLiftSmooth
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.GeodesicInitial
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.FixedFibreSmooth
import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.SmoothLeviCivitaConnection
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.SmoothLocalFlow
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Topology.Connected.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The genuine Riemannian exponential and its local addition


-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology


namespace HolomorphicAnosov

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The metric's Levi-Civita connection, chosen from its named existence and uniqueness theorem. Source: Andrews, Lecture 10 Proposition 10.3.1, pp.96–98. -/
def riemannianConnection
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    SmoothAffineConnection E M :=
  Classical.choose (andrews_smooth_levi_civita_connection E M g)

/-- A time-one endpoint is witnessed by a genuine connection geodesic on an open interval containing the whole time segment, with exactly the prescribed initial tangent vector. Source: Andrews, Lecture 8 Definition 8.11.1 and the exponential definition, pp.83–84. -/
def IsGeodesicTimeOneEndpoint (nabla : SmoothAffineConnection E M)
    (z : TangentBundle 𝓘(ℝ, E) M) (q : M) : Prop :=
  ∃ (J : Set ℝ) (γ : ℝ → M), IsOpen J ∧ OrdConnected J ∧ Icc (0 : ℝ) 1 ⊆ J ∧
    IsConnectionGeodesicOn nabla γ J ∧ curveTangentLift γ 0 = z ∧ γ 1 = q

/-- The genuine time-one domain of the metric exponential. Source: Andrews, Lecture 8, pp.83–84. -/
def riemannianExponentialDomain
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    Set (TangentBundle 𝓘(ℝ, E) M) :=
  {z | ∃ q, IsGeodesicTimeOneEndpoint (riemannianConnection g) z q}

/-- The exponential is the endpoint of an actual solution. Source: Andrews, Lecture 8 p.84. -/
def riemannianExponential
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (z : TangentBundle 𝓘(ℝ, E) M) : M := by
  classical
  exact if h : z ∈ riemannianExponentialDomain g then Classical.choose h else z.proj

/-- The moving-base exponential addition uses the original tangent projection. Source: Andrews, Lecture 8 Proposition 8.11.5, pp.85–86. -/
def riemannianExponentialAddition
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (z : TangentBundle 𝓘(ℝ, E) M) : M × M :=
  (z.proj, riemannianExponential g z)

/-- The geodesic endpoint is unique, so the time-one exponential definition is independent of all choices of solution and interval. Source: Andrews, Lecture 8 Proposition 8.11.2, pp.83–84, and Lecture 6 Proposition 6.1.1. -/
theorem geodesicTimeOneEndpoint_unique (nabla : SmoothAffineConnection E M)
    (z : TangentBundle 𝓘(ℝ, E) M) {q q' : M}
    (hq : IsGeodesicTimeOneEndpoint nabla z q)
    (hq' : IsGeodesicTimeOneEndpoint nabla z q') : q = q' := by
  obtain ⟨J, γ, hJ, hJc, hI, hγ, hγ0, hγ1⟩ := hq
  obtain ⟨J', γ', hJ', hJc', hI', hγ', hγ0', hγ1'⟩ := hq'
  obtain ⟨G, hG, hGc, hGu, hG0, hGcurve⟩ := exists_connectionGeodesicSpray nabla
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := tangentBundle_t2Space
  obtain ⟨U, δ, Ψ, hU, hzU, hδ, hΨ, hΨ0, hΨcurve, huniq, hgroup, hdiff⟩ :=
    exists_smoothLocalFlow (𝓘(ℝ, E)).tangent G hG z
  have hInt : IsOpen (J ∩ J') := hJ.inter hJ'
  have hIntc : OrdConnected (J ∩ J') := hJc.inter hJc'
  have hγInt : IsConnectionGeodesicOn nabla γ (J ∩ J') :=
    ⟨hγ.1.mono inter_subset_left, fun t ht ↦ hγ.2 t ht.1⟩
  have hγInt' : IsConnectionGeodesicOn nabla γ' (J ∩ J') :=
    ⟨hγ'.1.mono inter_subset_right, fun t ht ↦ hγ'.2 t ht.2⟩
  have hcurve : IsMIntegralCurveOn (I := (𝓘(ℝ, E)).tangent)
      (curveTangentLift (E := E) γ) G (J ∩ J') := by
    apply (hGcurve (J ∩ J') hInt hIntc (curveTangentLift (E := E) γ)
      (curveTangentLift_contMDiffOn hInt hγInt.1)).mpr
    exact ⟨hγInt, fun _ _ ↦ rfl⟩
  have hcurve' : IsMIntegralCurveOn (I := (𝓘(ℝ, E)).tangent)
      (curveTangentLift (E := E) γ') G (J ∩ J') := by
    apply (hGcurve (J ∩ J') hInt hIntc (curveTangentLift (E := E) γ')
      (curveTangentLift_contMDiffOn hInt hγInt'.1)).mpr
    exact ⟨hγInt', fun _ _ ↦ rfl⟩
  have h0 : (0 : ℝ) ∈ J ∩ J' := ⟨hI (by simp), hI' (by simp)⟩
  have h1 : (1 : ℝ) ∈ J ∩ J' := ⟨hI (by simp), hI' (by simp)⟩
  have heq := huniq (J ∩ J') hIntc 0 h0 _ _ hcurve hcurve' (hγ0.trans hγ0'.symm)
  have heq1 := congrArg TotalSpace.proj (heq h1)
  change γ 1 = γ' 1 at heq1
  exact hγ1.symm.trans (heq1.trans hγ1')

/-- A zero initial vector has the stationary base geodesic as its time-one solution. -/
lemma geodesicTimeOneEndpoint_zero (nabla : SmoothAffineConnection E M) (p : M) :
    IsGeodesicTimeOneEndpoint nabla ⟨p, 0⟩ p := by
  obtain ⟨G, hG, hGc, hGu, hG0, hGcurve⟩ := exists_connectionGeodesicSpray nabla
  let z : TangentBundle 𝓘(ℝ, E) M := ⟨p, 0⟩
  have hc : IsMIntegralCurveOn (I := (𝓘(ℝ, E)).tangent) (fun _ : ℝ ↦ z) G univ := by
    intro t ht
    change HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent (fun _ : ℝ ↦ z) univ t _
    have hzero : G z = 0 := hG0 p
    rw [hzero, ContinuousLinearMap.smulRight_zero]
    exact hasMFDerivWithinAt_const z univ t
  have hg := (hGcurve univ isOpen_univ ordConnected_univ (fun _ : ℝ ↦ z)
    contMDiffOn_const).mp hc
  refine ⟨univ, (fun _ : ℝ ↦ p), isOpen_univ, ordConnected_univ, subset_univ _, ?_, ?_, rfl⟩
  · exact hg.1
  · exact (hg.2 (mem_univ (0 : ℝ))).symm

/-- The literal choice defining the exponential satisfies every specified actual endpoint. -/
lemma riemannianExponential_eq_endpoint
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (z : TangentBundle 𝓘(ℝ, E) M) {q : M}
    (hq : IsGeodesicTimeOneEndpoint (riemannianConnection g) z q) :
    riemannianExponential g z = q := by
  classical
  have hz : z ∈ riemannianExponentialDomain g := ⟨q, hq⟩
  change (if h : z ∈ riemannianExponentialDomain g then Classical.choose h else z.proj) = q
  rw [dite_eq_left hz]
  exact geodesicTimeOneEndpoint_unique (riemannianConnection g) z
    (Classical.choose_spec hz) hq

/-- Every zero vector belongs to the genuine full time-one domain, and exponentiates to its base. -/
lemma riemannianExponential_zero
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) :
    (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g ∧
      riemannianExponential g ⟨p, 0⟩ = p := by
  have h := geodesicTimeOneEndpoint_zero (riemannianConnection g) p
  exact ⟨⟨p, h⟩, riemannianExponential_eq_endpoint g ⟨p, 0⟩ h⟩

/-- An actual partial inverse of the moving-base addition has the asserted first component and uniqueness in its own source. This is purely the native partial-equivalence inverse law. -/
lemma riemannianExponentialAddition_inverse_properties
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (e : PartialDiffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (TangentBundle 𝓘(ℝ, E) M) (M × M) ∞)
    (he : EqOn e (riemannianExponentialAddition g) e.source)
    (q y : M) (hqy : (q, y) ∈ e.target) :
    (e.symm (q, y)).proj = q ∧ riemannianExponential g (e.symm (q, y)) = y ∧
      (∀ z ∈ e.source, z.proj = q → riemannianExponential g z = y →
        z = e.symm (q, y)) := by
  have hx : e.symm (q, y) ∈ e.source := e.toPartialEquiv.map_target hqy
  have hi : e (e.symm (q, y)) = (q, y) := e.toPartialEquiv.right_inv hqy
  have ha : riemannianExponentialAddition g (e.symm (q, y)) = (q, y) :=
    (he hx).symm.trans hi
  refine ⟨congrArg Prod.fst ha, congrArg Prod.snd ha, ?_⟩
  intro z hz hzq hzy
  apply e.toPartialEquiv.injOn hz hx
  rw [he hz, hi]
  exact Prod.ext hzq hzy

omit [T2Space M] in
/-- Affine rescaling realizes each point of an actual geodesic through zero as a genuine time-one endpoint, including negative and zero rescaling. -/
lemma geodesicTimeOneEndpoint_rescale (nabla : SmoothAffineConnection E M)
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : OrdConnected J)
    (hγ : IsConnectionGeodesicOn nabla γ J) (h0 : (0 : ℝ) ∈ J)
    {t : ℝ} (ht : t ∈ J) :
    IsGeodesicTimeOneEndpoint nabla
      ⟨γ 0, t • curveVelocity (E := E) γ 0⟩ (γ t) := by
  have hpre : IsOpen {s : ℝ | t * s ∈ J} :=
    hJ.preimage (continuous_const.mul continuous_id)
  have hc : OrdConnected {s : ℝ | t * s ∈ J} := by
    by_cases ht0 : 0 ≤ t
    · exact hJc.preimage_mono (fun a b hab ↦ mul_le_mul_of_nonneg_left hab ht0)
    · exact hJc.preimage_anti
        (fun a b hab ↦ mul_le_mul_of_nonpos_left hab (le_of_lt (lt_of_not_ge ht0)))
  have hI : Icc (0 : ℝ) 1 ⊆ {s : ℝ | t * s ∈ J} := by
    intro s hs
    by_cases ht0 : 0 ≤ t
    · apply hJc.out h0 ht
      constructor <;> nlinarith [hs.1, hs.2]
    · apply hJc.out ht h0
      constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨hrescale, hinit⟩ := connectionGeodesic_rescale nabla γ J hJ hJc hγ t
  refine ⟨{s : ℝ | t * s ∈ J}, (fun s ↦ γ (t * s)), hpre, hc, hI,
    hrescale, ?_, by simp⟩
  apply TotalSpace.ext
  · simp [curveTangentLift]
  · exact heq_of_eq (hinit h0).2

/-- Along an existing geodesic, the exponential follows the corresponding rescaled trajectory. -/
lemma riemannianExponential_along_geodesic
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : OrdConnected J)
    (hγ : IsConnectionGeodesicOn (riemannianConnection g) γ J)
    (h0 : (0 : ℝ) ∈ J) {t : ℝ} (ht : t ∈ J) :
    riemannianExponential g ⟨γ 0, t • curveVelocity (E := E) γ 0⟩ = γ t :=
  riemannianExponential_eq_endpoint g _
    (geodesicTimeOneEndpoint_rescale (riemannianConnection g) hJ hJc hγ h0 ht)

set_option backward.isDefEq.respectTransparency false in
/-- Differentiability of the actual fibre exponential, together with genuine geodesic rescaling, forces its differential at zero to be the identity. -/
lemma riemannianExponential_vertical_derivative
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M)
    (hep : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun v : E ↦ riemannianExponential g
        ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩) 0)
    (w : E) :
    tangentSpaceCastModel 𝓘(ℝ, E) (riemannianExponential g ⟨p, 0⟩)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (fun v : E ↦ riemannianExponential g
          ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩) 0
        ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w)) = w := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
    (fun v : E ↦ riemannianExponential g
      ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩) 0 w = w
  obtain ⟨J, γ, hJ, hJc, h0, hγ, hinit⟩ :=
    exists_connectionGeodesic_initial (riemannianConnection g)
      ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm w⟩
  have hp : γ 0 = p := congrArg TotalSpace.proj hinit
  have hv : curveVelocity (E := E) γ 0 = (tangentSpaceCastModel 𝓘(ℝ, E) p).symm w := by
    exact eq_of_heq (TotalSpace.ext_iff.mp hinit).2
  let ep : E → M := fun v ↦ riemannianExponential g
    ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩
  have heq : (fun t : ℝ ↦ ep (t • w)) =ᶠ[𝓝 0] γ := by
    filter_upwards [hJ.mem_nhds h0] with t ht
    have h := riemannianExponential_along_geodesic g hJ hJc hγ h0 ht
    have hinitt : (⟨γ 0, t • curveVelocity (E := E) γ 0⟩ : TangentBundle 𝓘(ℝ, E) M) =
        ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm (t • w)⟩ := by
      apply TotalSpace.ext hp
      exact heq_of_eq (by simpa only [map_smul] using congrArg (t • ·) hv)
    rw [hinitt] at h
    exact h
  have hline : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ ↦ t • w) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    exact ((1 : ℝ →L[ℝ] ℝ).smulRight w).hasFDerivAt.hasMFDerivAt
  have hc := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    (x := (0 : ℝ)) (f := fun t : ℝ ↦ t • w) (g := ep)
    (by simpa using hep) hline.mdifferentiableAt
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (0 : ℝ)).symm 1)
  have hcγ := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
  have hv' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (0 : ℝ)).symm 1) =
      (tangentSpaceCastModel 𝓘(ℝ, E) p).symm w := hv
  simp only [Function.comp_def] at hc
  rw [hcγ] at hc
  simp only [ContinuousLinearMap.comp_apply, tangentSpaceCast,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at hc
  rw [hv'] at hc
  simp only [hline.mfderiv, ContinuousLinearMap.smulRight_apply] at hc
  dsimp [tangentSpaceCastModel, ContinuousLinearEquiv.symm] at hc
  simp only [TangentSpace, one_apply_eq_self, one_smul] at hc
  rw [show (0 : ℝ) • w = (0 : E) from zero_smul ℝ w] at hc
  change w = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 w at hc
  dsimp [tangentSpaceCastModel, ContinuousLinearEquiv.symm]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 w = w
  exact hc.symm

/-- Nearby initial vectors have time-one endpoints obtained by continuation of the geodesic. -/
lemma riemannianExponential_local_certificate
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (z : TangentBundle 𝓘(ℝ, E) M) (hz : z ∈ riemannianExponentialDomain g) :
    ∃ W, IsOpen W ∧ z ∈ W ∧ ∃ F : TangentBundle 𝓘(ℝ, E) M → M,
      ContMDiffOn (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞ F W ∧
      ∀ w ∈ W, IsGeodesicTimeOneEndpoint (riemannianConnection g) w (F w) := by
  obtain ⟨q, J, γ, hJ, hJc, hseg, hγ, hγ0, hγ1⟩ := hz
  obtain ⟨G, hG, hGc, hGu, hG0, hGcurve⟩ :=
    exists_connectionGeodesicSpray (riemannianConnection g)
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := tangentBundle_t2Space
  have h0 : (0 : ℝ) ∈ J := hseg (by simp)
  have h1 : (1 : ℝ) ∈ J := hseg (by simp)
  have hcl := curveTangentLift_contMDiffOn hJ hγ.1
  have hcurve := (hGcurve J hJ hJc (curveTangentLift (E := E) γ) hcl).mpr
    ⟨hγ, fun _ _ ↦ rfl⟩
  obtain ⟨W, hW, hzW, F, hF, hFz, hFW⟩ :=
    W07FlowContinuation.endpoint_certificate hG hJ hJc h0 hcl hcurve h1
  refine ⟨W, hW, hγ0 ▸ hzW, fun w ↦ (F w).proj,
    (Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, E))).comp_contMDiffOn hF, ?_⟩
  intro w hw
  obtain ⟨a, b, c, hc0, hc1, hc, hcc, he0, he1⟩ := hFW w hw
  have hgeoc := (hGcurve (Ioo a b) isOpen_Ioo ordConnected_Ioo c hc).mp hcc
  refine ⟨Ioo a b, fun t ↦ (c t).proj, isOpen_Ioo, ordConnected_Ioo, ?_,
    hgeoc.1, ?_, ?_⟩
  · intro t ht
    exact ⟨lt_of_lt_of_le hc0.1 ht.1, lt_of_le_of_lt ht.2 hc1.2⟩
  · exact (hgeoc.2 hc0).symm.trans he0
  · exact congrArg TotalSpace.proj he1

/-- The actual full exponential domain is open, and the originally selected endpoint function is smooth on all of it by unique local continuation. -/
lemma riemannianExponential_open_smooth
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    IsOpen (riemannianExponentialDomain g) ∧
    ContMDiffOn (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞ (riemannianExponential g)
      (riemannianExponentialDomain g) := by
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨W, hW, hzW, F, hF, hend⟩ := riemannianExponential_local_certificate g z hz
    exact Filter.mem_of_superset (hW.mem_nhds hzW) (fun w hw ↦ ⟨F w, hend w hw⟩)
  · intro z hz
    obtain ⟨W, hW, hzW, F, hF, hend⟩ := riemannianExponential_local_certificate g z hz
    apply ContMDiffAt.contMDiffWithinAt
    apply (hF.contMDiffAt (hW.mem_nhds hzW)).congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hzW] with w hw
    exact riemannianExponential_eq_endpoint g w (hend w hw)

/-- The original fixed-fibre exponential is smooth at zero on its genuine domain. -/
lemma riemannianExponential_fibre_contMDiffAt_zero
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun v : E ↦ riemannianExponential g
        ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩) 0 := by
  obtain ⟨hD, he⟩ := riemannianExponential_open_smooth g
  have hp0 := (riemannianExponential_zero g p).1
  have hi := (tangentBundle_fixed_fibre_contMDiff p).contMDiffAt (x := (0 : E))
  have hz : (⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm (0 : E)⟩ :
      TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g := by
    simpa only [map_zero] using hp0
  exact (he.contMDiffAt (hD.mem_nhds hz)).comp 0 hi

/-- Along the actual zero section, the addition is the diagonal map, so its horizontal differential is the diagonal linear map in the native tangent model. -/
lemma riemannianExponentialAddition_horizontal_derivative
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (u : TangentSpace 𝓘(ℝ, E) p) :
    mfderiv (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (riemannianExponentialAddition g) (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M)
      (u, (0 : E)) = (u, u) := by
  obtain ⟨hD, he⟩ := riemannianExponential_open_smooth g
  have ha : MDifferentiableAt (𝓘(ℝ, E)).tangent
      ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (riemannianExponentialAddition g) ⟨p, 0⟩ :=
    (Bundle.mdifferentiable_proj (TangentSpace 𝓘(ℝ, E))).mdifferentiableAt.prodMk
      ((he.contMDiffAt (hD.mem_nhds (riemannianExponential_zero g p).1)).mdifferentiableAt
        (by simp))
  let Z := Bundle.zeroSection E (TangentSpace 𝓘(ℝ, E) : M → Type _)
  have hZ := Bundle.mdifferentiable_zeroSection ℝ (F := E) (IB := 𝓘(ℝ, E))
    (TangentSpace 𝓘(ℝ, E) : M → Type _)
  have hcomp : riemannianExponentialAddition g ∘ Z = fun q : M ↦ (q, q) := by
    funext q
    exact Prod.ext rfl (riemannianExponential_zero g q).2
  have hzero : mfderiv 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent Z p u = (u, (0 : E)) := by
    exact congrArg TotalSpace.snd (TangentBundle.tangentMap_tangentBundle_pure
      (I := 𝓘(ℝ, E)) (⟨p, u⟩ : TangentBundle 𝓘(ℝ, E) M))
  have hc := mfderiv_comp_apply (I := 𝓘(ℝ, E)) (I' := (𝓘(ℝ, E)).tangent)
    (I'' := ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))) (f := Z)
    (g := riemannianExponentialAddition g) p ha (hZ p) u
  rw [hcomp, hzero] at hc
  have hd : mfderiv 𝓘(ℝ, E) ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (fun q : M ↦ (q, q)) p =
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) p)).prod
        (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) p)) := by
    exact (mfderiv_prodMk (f := id) (g := id) mdifferentiableAt_id
      mdifferentiableAt_id).trans (by rw [mfderiv_id])
  rw [hd] at hc
  exact hc.symm

/-- Combining the genuine vertical exponential derivative with the actual fibre inclusion gives the vertical differential of the moving-base addition. -/
lemma riemannianExponentialAddition_vertical_derivative
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (w : E)
    (hj : mfderiv 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent
      (fun v : E ↦ (⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩ :
        TangentBundle 𝓘(ℝ, E) M)) 0
      ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w) = ((0 : E), w)) :
    mfderiv (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (riemannianExponentialAddition g) (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M)
      ((0 : E), w) = ((0 : E), w) := by
  obtain ⟨hD, he⟩ := riemannianExponential_open_smooth g
  have ha : MDifferentiableAt (𝓘(ℝ, E)).tangent
      ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (riemannianExponentialAddition g) ⟨p, 0⟩ :=
    (Bundle.mdifferentiable_proj (TangentSpace 𝓘(ℝ, E))).mdifferentiableAt.prodMk
      ((he.contMDiffAt (hD.mem_nhds (riemannianExponential_zero g p).1)).mdifferentiableAt
        (by simp))
  let j : E → TangentBundle 𝓘(ℝ, E) M := fun v ↦
    ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩
  have hj0 : j 0 = ⟨p, 0⟩ := by simp only [j, map_zero]
  let ep : E → M := riemannianExponential g ∘ j
  have hep : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 :=
    (riemannianExponential_fibre_contMDiffAt_zero g p).mdifferentiableAt (by simp)
  have hcomp : riemannianExponentialAddition g ∘ j = fun v : E ↦ (p, ep v) := rfl
  have hc := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, E)) (I' := (𝓘(ℝ, E)).tangent)
    (I'' := ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))) (f := j)
    (g := riemannianExponentialAddition g) (0 : E) ha
    ((tangentBundle_fixed_fibre_contMDiff p).mdifferentiableAt (by simp)) hj0
    ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w)
  rw [hcomp, hj, mfderiv_prodMk mdifferentiableAt_const hep] at hc
  have hv := riemannianExponential_vertical_derivative g p hep w
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0
    ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w) = w at hv
  rw [mfderiv_const] at hc
  change ((0 : E), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0
    ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w)) = _ at hc
  rw [hv] at hc
  exact hc.symm

/-- The horizontal and vertical derivatives determine the invertible shear differential of the actual moving-base exponential addition. -/
lemma riemannianExponentialAddition_invertible_derivative
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M)
    (hj : ∀ w : E, mfderiv 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent
      (fun v : E ↦ (⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩ :
        TangentBundle 𝓘(ℝ, E) M)) 0
      ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w) = ((0 : E), w)) :
    ∃ a : TangentSpace (𝓘(ℝ, E)).tangent
        (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ≃L[ℝ]
        TangentSpace ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
          (riemannianExponentialAddition g ⟨p, 0⟩),
      mfderiv (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
        (riemannianExponentialAddition g) (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) =
        a.toContinuousLinearMap := by
  let S : (E × E) ≃L[ℝ] E × E :=
    (ContinuousLinearEquiv.refl ℝ E).skewProd (ContinuousLinearEquiv.refl ℝ E)
      (ContinuousLinearMap.id ℝ E)
  let a := (tangentSpaceCastModel (𝓘(ℝ, E)).tangent
      (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).trans
    (S.trans (tangentSpaceCastModel ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (riemannianExponentialAddition g ⟨p, 0⟩)).symm)
  refine ⟨a, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨u, w⟩ := v
  have hh := riemannianExponentialAddition_horizontal_derivative g p
    ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm u)
  have hv := riemannianExponentialAddition_vertical_derivative g p w (hj w)
  let L : (E × E) →L[ℝ] E × E :=
    (tangentSpaceCastModel ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (riemannianExponentialAddition g ⟨p, 0⟩)).toContinuousLinearMap.comp
    ((mfderiv (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E))
      (riemannianExponentialAddition g) (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).comp
      (tangentSpaceCastModel (𝓘(ℝ, E)).tangent
        (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm.toContinuousLinearMap)
  have hh' : L (u, 0) = (u, u) := hh
  have hv' : L (0, w) = (0, w) := hv
  change L (u, w) = (u, w + u)
  have hsplit : (u, w) = (u, (0 : E)) + ((0 : E), w) := by simp
  rw [hsplit, map_add, hh', hv']
  simp only [Prod.mk_add_mk, add_zero, add_comm]

/-- The genuine geodesic exponential is a smooth local addition near the entire zero section. Source: Andrews, Lecture 8 Propositions 8.11.2, 8.11.4–5, pp.83–86; Lecture 10 Proposition 10.3.1, pp.96–98. -/
theorem riemannian_exponential_local_addition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    IsOpen (riemannianExponentialDomain g) ∧
    (∀ p : M, (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) ∧
    ContMDiffOn (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞ (riemannianExponential g)
      (riemannianExponentialDomain g) ∧
    (∀ p : M, riemannianExponential g ⟨p, 0⟩ = p) ∧
    (∀ (p : M) (w : E),
      tangentSpaceCastModel 𝓘(ℝ, E) (riemannianExponential g ⟨p, 0⟩)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
          (fun v : E ↦ riemannianExponential g
            ⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩) 0
          ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w)) = w) ∧
    (∀ p : M, ∃ e : PartialDiffeomorph (𝓘(ℝ, E)).tangent
        ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (TangentBundle 𝓘(ℝ, E) M) (M × M) ∞,
      (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ e.source ∧
      e.source ⊆ riemannianExponentialDomain g ∧ (p, p) ∈ e.target ∧
      EqOn e (riemannianExponentialAddition g) e.source ∧
      (∀ q y : M, (q, y) ∈ e.target →
        (e.symm (q, y)).proj = q ∧ riemannianExponential g (e.symm (q, y)) = y ∧
        (∀ z ∈ e.source, z.proj = q → riemannianExponential g z = y →
          z = e.symm (q, y)))) := by
  obtain ⟨hD, he⟩ := riemannianExponential_open_smooth g
  refine ⟨hD, fun p ↦ (riemannianExponential_zero g p).1, he,
    fun p ↦ (riemannianExponential_zero g p).2, ?_, ?_⟩
  · intro p w
    exact riemannianExponential_vertical_derivative g p
      ((riemannianExponential_fibre_contMDiffAt_zero g p).mdifferentiableAt (by simp)) w
  · intro p
    have hj (w : E) : mfderiv 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent
        (fun v : E ↦ (⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm v⟩ :
          TangentBundle 𝓘(ℝ, E) M)) 0
        ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm w) = ((0 : E), w) := by
      have hh := congrArg (fun L : E →L[ℝ] E × E ↦ L w)
        (W07FibreInsertionDerivative.coordinate_mfderiv_fibreInsertion (I := 𝓘(ℝ, E)) p)
      exact hh
    obtain ⟨a, ha⟩ := riemannianExponentialAddition_invertible_derivative g p hj
    have hAdd : ContMDiffOn (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) ∞
        (riemannianExponentialAddition g) (riemannianExponentialDomain g) :=
      (Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, E))).contMDiffOn.prodMk he
    obtain ⟨e, hp, heD, hef⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph hD
      (riemannianExponential_zero g p).1 hAdd a ha
    have heA : EqOn e (riemannianExponentialAddition g) e.source :=
      fun z hz ↦ (hef hz).symm
    refine ⟨e, hp, heD, ?_, heA, ?_⟩
    · have hv : e ⟨p, 0⟩ = (p, p) :=
        (heA hp).trans (Prod.ext rfl (riemannianExponential_zero g p).2)
      rw [← hv]
      exact e.toPartialEquiv.map_source hp
    · exact riemannianExponentialAddition_inverse_properties g e heA


end
end HolomorphicAnosov
