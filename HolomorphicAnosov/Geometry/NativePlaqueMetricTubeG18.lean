import HolomorphicAnosov.Geometry.ExponentialDerivativeZeroG18
import HolomorphicAnosov.Geometry.NativePlaqueSecondDerivativeG18
import HolomorphicAnosov.Geometry.MetricChartTensorG18
import HolomorphicAnosov.Geometry.ParametricMetricNormalFrameG18

noncomputable section
open Set Bundle
open scoped Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov.HPS
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Dist : RealTangentDistribution 𝓘(ℝ,E) M}
  {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
  {F : LeafPartition Dist ι L r} {x : M} {d : ℕ}
  {Φ : FiniteC1NativePlaqueFamily F x d} {n : ℕ}

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Fin d → ℝ)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

/-- A finite-order native plaque family admits metric-normal tube coordinates in the fixed receiving
chart for the pulled-back ambient metric. -/
theorem FiniteOrderNativePlaqueCoherence.original_metric_normal_tube_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n) (hn : 2 ≤ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ : Φ.family.centerDomain)
    (a : E × E → E) (U : Set (E × E)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hu₀ : (H.coordinate p₀ 0,0) ∈ U)
    (ha₀ : HasFDerivAt a (ContinuousLinearMap.fst ℝ E E +
      ContinuousLinearMap.snd ℝ E E) (H.coordinate p₀ 0,0)) :
    let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
    let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∃ Q : TopologicalSpace.Opens Φ.family.centerDomain, ∃ hpQ : p₀ ∈ Q,
      ∃ W : Set E, IsOpen W ∧ a (H.coordinate p₀ 0,0) ∈ W ∧
      ∃ e : Q → OpenPartialHomeomorph ((Fin d → ℝ) × K) E,
        (∀ p : Q, (e p : ((Fin d → ℝ) × K) → E) =
            (fun z ↦ a (H.coordinate p.1 z.1,N (p.1,z.1) z.2)) ∧
          (e p).target = W ∧ ContDiffOn ℝ 1 (e p) (e p).source ∧
          ContDiffOn ℝ 1 (e p).symm (e p).target ∧
          ∀ z ∈ (e p).source, (p.1,z.1) ∈ Ω ∧ (H.coordinate p.1 z.1,N (p.1,z.1) z.2) ∈ U) ∧
        ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2) (univ ×ˢ W) ∧
        ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W) ∧
        0 ∈ (e ⟨p₀,hpQ⟩).source ∧
        IsOpen {z : Q × ((Fin d → ℝ) × K) | z.2 ∈ (e z.1).source} := by
  let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
  let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
  let q := H.coordinate
  let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (q z.1) z.2
  let DD := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (fderiv ℝ (q z.1)) z.2
  let β := originalMetricChartTensor_g18 g Φ.family.receivingAnchor
  let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ β (q z.1 z.2)
  let Db := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ (fderiv ℝ β (q z.1 z.2)).comp (D z)
  let T := (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).target
  have hΩ : IsOpen Ω := isOpen_univ.prod Metric.isOpen_ball
  have hpΩ : (p₀,0) ∈ Ω := ⟨mem_univ _,Metric.mem_ball_self Φ.family.radius_pos⟩
  have hq : ContinuousOn (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := (continuousOn_extChartAt (I := 𝓘(ℝ,E)) Φ.family.receivingAnchor).comp_continuous
      Φ.family.jointly_continuous (fun z ↦ Φ.family.receiving_domain z.1 z.2 z.2.property)
    have hc' := hc.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    exact hc'.congr (fun z ↦ (H.coordinate_eq z.1.1 z.property.2).symm)
  have hmaps : MapsTo (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω T := by
    intro z hz
    change q z.1 z.2 ∈ T
    rw [show q z.1 z.2 = extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param z.2) from H.coordinate_eq z.1 hz.2]
    exact (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).map_source
      (Φ.family.receiving_domain z.1 z.2 hz.2)
  have hD : ContinuousOn D Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := Φ.family.jointly_continuous_derivative.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    apply hc.congr
    intro z
    have heq : q z.1.1 =ᶠ[nhds z.1.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds z.property.2] with v hv
      exact H.coordinate_eq z.1.1 hv
    exact heq.fderiv_eq.symm
  have hDD : ContinuousOn DD Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (H.continuous_second_derivative_g18 hn).comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
  have hqd : ∀ z ∈ Ω, HasFDerivAt (q z.1) (D z) z.2 := by
    intro z hz
    exact ((H.coordinate_smooth z.1).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz.2)).differentiableAt (by simp) |>.hasFDerivAt
  have hDd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ D (z.1,v)) (DD z) z.2 := by
    intro z hz
    exact (((H.coordinate_smooth z.1).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz.2)).fderiv_right (m := 1) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have hDin : ∀ z ∈ Ω, Function.Injective (D z) := by
    intro z hz
    have hv : z.2 ∈ (Φ.family.plaque z.1).domain := by
      rw [Φ.family.domain_eq]; exact hz.2
    have hφ := ((Φ.family.plaque z.1).smooth z.2 hv).contMDiffAt
      ((Φ.family.plaque z.1).domain_open.mem_nhds hv)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E))
      (by simpa only [extChartAt_source] using Φ.family.receiving_domain z.1 z.2 hz.2)
    have hchain := mfderiv_comp z.2 hc (hφ.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hchain
    change fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param v)) z.2 = _ at hchain
    have heq : q z.1 =ᶠ[nhds z.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with v hv
      exact H.coordinate_eq z.1 hv
    change Function.Injective (fderiv ℝ (q z.1) z.2)
    rw [heq.fderiv_eq, hchain]
    apply Function.Injective.comp _ ((Φ.family.plaque z.1).immersed z.2 hv)
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
      (Φ.family.receiving_domain z.1 z.2 hz.2)
    rw [← hA]
    exact A.injective
  have hβ := originalMetricChartTensor_contDiffOn_g18 g Φ.family.receivingAnchor
  have hT : IsOpen T := isOpen_extChartAt_target Φ.family.receivingAnchor
  have hb : ContinuousOn b Ω := hβ.continuousOn.comp hq hmaps
  have hβD : ContinuousOn (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      fderiv ℝ β (q z.1 z.2)) Ω :=
    (hβ.continuousOn_fderiv_of_isOpen hT (by simp)).comp hq hmaps
  have hDb : ContinuousOn Db Ω := ContinuousOn.clm_comp
    (𝕜 := ℝ) (E := Fin d → ℝ) (F := E) (G := E →L[ℝ] E →L[ℝ] ℝ) hβD hD
  have hbpos : ∀ z ∈ Ω, ∀ v, v ≠ 0 → 0 < b z v v := by
    intro z hz v hv
    exact originalMetricChartTensor_pos_g18 g Φ.family.receivingAnchor _ (hmaps hz) v hv
  have hbd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ b (z.1,v)) (Db z) z.2 := by
    intro z hz
    exact ((hβ.contDiffAt (hT.mem_nhds (hmaps hz))).differentiableAt (by simp)).hasFDerivAt.comp
      z.2 (hqd z hz)
  exact parametric_metric_normal_tube_g18 q b D Db DD Ω hΩ p₀ hpΩ hq hb hD hDb hDD
    hbpos hDin hqd hbd hDd a U hU ha hu₀ ha₀


/-- A finite-order native plaque family admits metric-normal tube coordinates defined by the
Riemannian exponential in the fixed receiving chart. -/
theorem FiniteOrderNativePlaqueCoherence.original_exponential_normal_tube_g18 [T2Space M]
    (H : FiniteOrderNativePlaqueCoherence Φ n) (hn : 2 ≤ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ : Φ.family.centerDomain) :
    let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
    let ct := extChartAt (𝓘(ℝ,E)).tangent
      (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
    let a := ca ∘ riemannianExponential g ∘ ct.symm
    ∃ U : Set (E × E), IsOpen U ∧ (H.coordinate p₀ 0,0) ∈ U ∧
      (∀ z ∈ U, z ∈ ct.target ∧ ct.symm z ∈ riemannianExponentialDomain g ∧
        riemannianExponential g (ct.symm z) ∈ ca.source) ∧
    let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
    let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∃ Q : TopologicalSpace.Opens Φ.family.centerDomain, ∃ hpQ : p₀ ∈ Q,
      ∃ W : Set E, IsOpen W ∧ a (H.coordinate p₀ 0,0) ∈ W ∧
      ∃ e : Q → OpenPartialHomeomorph ((Fin d → ℝ) × K) E,
        (∀ p : Q, (e p : ((Fin d → ℝ) × K) → E) =
            (fun z ↦ a (H.coordinate p.1 z.1,N (p.1,z.1) z.2)) ∧
          (e p).target = W ∧ ContDiffOn ℝ 1 (e p) (e p).source ∧
          ContDiffOn ℝ 1 (e p).symm (e p).target ∧
          ∀ z ∈ (e p).source, (p.1,z.1) ∈ Ω ∧ (H.coordinate p.1 z.1,N (p.1,z.1) z.2) ∈ U) ∧
        ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2) (univ ×ˢ W) ∧
        ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W) ∧
        0 ∈ (e ⟨p₀,hpQ⟩).source ∧
        IsOpen {z : Q × ((Fin d → ℝ) × K) | z.2 ∈ (e z.1).source} := by
  let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
  let ct := extChartAt (𝓘(ℝ,E)).tangent
    (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
  let a := ca ∘ riemannianExponential g ∘ ct.symm
  have h0 : (0 : Fin d → ℝ) ∈ Metric.ball 0 Φ.family.radius :=
    Metric.mem_ball_self Φ.family.radius_pos
  have hq0 : H.coordinate p₀ 0 = ca p₀.val := by
    exact (H.coordinate_eq p₀ h0).trans (congrArg ca (Φ.family.plaque p₀).centered)
  have hp : p₀.val ∈ ca.source := by
    simpa only [(Φ.family.plaque p₀).centered] using Φ.family.receiving_domain p₀ 0 h0
  obtain ⟨U,hU,hpU,hA,hguard⟩ :=
    riemannianExponential_fixed_coordinate_domain_g18 g Φ.family.receivingAnchor p₀.val hp
  have hder := riemannianExponential_fixed_coordinate_derivative_zero_g18
    g Φ.family.receivingAnchor p₀.val hp
  have hqU : (H.coordinate p₀ 0,0) ∈ U := by rwa [hq0]
  refine ⟨U,hU,hqU,hguard,?_⟩
  exact H.original_metric_normal_tube_g18 hn g p₀ a U hU (hA.of_le (by simp)) hqU
    (by simpa only [hq0] using hder)

/-- A native plaque family admits a uniform injective metric-normal radius on a small compact plaque
core. -/
theorem FiniteOrderNativePlaqueCoherence.original_metric_normal_uniform_tube_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n) (hn : 2 ≤ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ : Φ.family.centerDomain)
    (a : E × E → E) (U : Set (E × E)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hu₀ : (H.coordinate p₀ 0,0) ∈ U)
    (hzero : ∀ v ∈ Metric.ball (0 : Fin d → ℝ) Φ.family.radius,
      (H.coordinate p₀ v,0) ∈ U → a (H.coordinate p₀ v,0) = H.coordinate p₀ v)
    (ha₀ : ∀ v ∈ Metric.ball (0 : Fin d → ℝ) Φ.family.radius,
      (H.coordinate p₀ v,0) ∈ U → HasFDerivAt a
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
        (H.coordinate p₀ v,0)) :
    let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
    let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ Q ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Q,
      InjOn (fun z : (Fin d → ℝ) × K ↦ a (H.coordinate p z.1,N (p,z.1) z.2))
        (Metric.closedBall 0 ρ ×ˢ Metric.ball (0 : K) ε) ∧
      ∀ z ∈ Metric.closedBall 0 ρ ×ˢ Metric.ball (0 : K) ε,
        ((p,z.1) ∈ Ω ∧ (H.coordinate p z.1,N (p,z.1) z.2) ∈ U) ∧
        (fderiv ℝ (fun w : (Fin d → ℝ) × K ↦
          a (H.coordinate p w.1,N (p,w.1) w.2)) z).IsInvertible := by
  let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
  let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
  let q := H.coordinate
  let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (q z.1) z.2
  let DD := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (fderiv ℝ (q z.1)) z.2
  let β := originalMetricChartTensor_g18 g Φ.family.receivingAnchor
  let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ β (q z.1 z.2)
  let Db := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ (fderiv ℝ β (q z.1 z.2)).comp (D z)
  let T := (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).target
  have hΩ : IsOpen Ω := isOpen_univ.prod Metric.isOpen_ball
  have hpΩ : (p₀,0) ∈ Ω := ⟨mem_univ _,Metric.mem_ball_self Φ.family.radius_pos⟩
  have hq : ContinuousOn (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := (continuousOn_extChartAt (I := 𝓘(ℝ,E)) Φ.family.receivingAnchor).comp_continuous
      Φ.family.jointly_continuous (fun z ↦ Φ.family.receiving_domain z.1 z.2 z.2.property)
    have hc' := hc.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    exact hc'.congr (fun z ↦ (H.coordinate_eq z.1.1 z.property.2).symm)
  have hmaps : MapsTo (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω T := by
    intro z hz
    change q z.1 z.2 ∈ T
    rw [show q z.1 z.2 = extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param z.2) from H.coordinate_eq z.1 hz.2]
    exact (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).map_source
      (Φ.family.receiving_domain z.1 z.2 hz.2)
  have hD : ContinuousOn D Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := Φ.family.jointly_continuous_derivative.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    apply hc.congr
    intro z
    have heq : q z.1.1 =ᶠ[nhds z.1.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds z.property.2] with v hv
      exact H.coordinate_eq z.1.1 hv
    exact heq.fderiv_eq.symm
  have hDD : ContinuousOn DD Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (H.continuous_second_derivative_g18 hn).comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
  have hqd : ∀ z ∈ Ω, HasFDerivAt (q z.1) (D z) z.2 := by
    intro z hz
    exact ((H.coordinate_smooth z.1).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz.2)).differentiableAt (by simp) |>.hasFDerivAt
  have hDd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ D (z.1,v)) (DD z) z.2 := by
    intro z hz
    exact (((H.coordinate_smooth z.1).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz.2)).fderiv_right (m := 1) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have hDin : ∀ z ∈ Ω, Function.Injective (D z) := by
    intro z hz
    have hv : z.2 ∈ (Φ.family.plaque z.1).domain := by
      rw [Φ.family.domain_eq]; exact hz.2
    have hφ := ((Φ.family.plaque z.1).smooth z.2 hv).contMDiffAt
      ((Φ.family.plaque z.1).domain_open.mem_nhds hv)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E))
      (by simpa only [extChartAt_source] using Φ.family.receiving_domain z.1 z.2 hz.2)
    have hchain := mfderiv_comp z.2 hc (hφ.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hchain
    change fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param v)) z.2 = _ at hchain
    have heq : q z.1 =ᶠ[nhds z.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with v hv
      exact H.coordinate_eq z.1 hv
    change Function.Injective (fderiv ℝ (q z.1) z.2)
    rw [heq.fderiv_eq, hchain]
    apply Function.Injective.comp _ ((Φ.family.plaque z.1).immersed z.2 hv)
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
      (Φ.family.receiving_domain z.1 z.2 hz.2)
    rw [← hA]
    exact A.injective
  have hβ := originalMetricChartTensor_contDiffOn_g18 g Φ.family.receivingAnchor
  have hT : IsOpen T := isOpen_extChartAt_target Φ.family.receivingAnchor
  have hb : ContinuousOn b Ω := hβ.continuousOn.comp hq hmaps
  have hβD : ContinuousOn (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      fderiv ℝ β (q z.1 z.2)) Ω :=
    (hβ.continuousOn_fderiv_of_isOpen hT (by simp)).comp hq hmaps
  have hDb : ContinuousOn Db Ω := ContinuousOn.clm_comp
    (𝕜 := ℝ) (E := Fin d → ℝ) (F := E) (G := E →L[ℝ] E →L[ℝ] ℝ) hβD hD
  have hbpos : ∀ z ∈ Ω, ∀ v, v ≠ 0 → 0 < b z v v := by
    intro z hz v hv
    exact originalMetricChartTensor_pos_g18 g Φ.family.receivingAnchor _ (hmaps hz) v hv
  have hbd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ b (z.1,v)) (Db z) z.2 := by
    intro z hz
    exact ((hβ.contDiffAt (hT.mem_nhds (hmaps hz))).differentiableAt (by simp)).hasFDerivAt.comp
      z.2 (hqd z hz)
  have hinj : InjOn (q p₀) {v | (p₀,v) ∈ Ω} := by
    intro v hv w hw heq
    have hv' : v ∈ (Φ.family.plaque p₀).domain := by
      rw [Φ.family.domain_eq]; exact hv.2
    have hw' : w ∈ (Φ.family.plaque p₀).domain := by
      rw [Φ.family.domain_eq]; exact hw.2
    have heq' : (Φ.family.plaque p₀).param v = (Φ.family.plaque p₀).param w :=
      (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).injOn
        (Φ.family.receiving_domain p₀ v hv.2) (Φ.family.receiving_domain p₀ w hw.2)
        (by simpa only [q,H.coordinate_eq p₀ hv.2,H.coordinate_eq p₀ hw.2] using heq)
    exact congrArg Subtype.val ((Φ.family.plaque p₀).embedded.injective
      (show (Φ.family.plaque p₀).param (⟨v,hv'⟩ : (Φ.family.plaque p₀).domain) =
        (Φ.family.plaque p₀).param (⟨w,hw'⟩ : (Φ.family.plaque p₀).domain) from heq'))
  exact parametric_metric_normal_uniform_tube_g18 q b D Db DD Ω hΩ p₀ hpΩ hq hb hD hDb hDD
    hbpos hDin hqd hbd hDd a U hU ha hu₀
    (fun v hv ↦ hzero v hv.2) (fun v hv ↦ ha₀ v hv.2) hinj

/-- The Riemannian exponential normal tube of a native plaque family is injective for a uniform
radius on a small compact plaque core. -/
theorem FiniteOrderNativePlaqueCoherence.original_exponential_normal_uniform_tube_g18 [T2Space M]
    (H : FiniteOrderNativePlaqueCoherence Φ n) (hn : 2 ≤ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ : Φ.family.centerDomain) :
    let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
    let ct := extChartAt (𝓘(ℝ,E)).tangent
      (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
    let a := ca ∘ riemannianExponential g ∘ ct.symm
    ∃ U : Set (E × E), IsOpen U ∧ (H.coordinate p₀ 0,0) ∈ U ∧
      (∀ z ∈ U, z ∈ ct.target ∧ ct.symm z ∈ riemannianExponentialDomain g ∧
        riemannianExponential g (ct.symm z) ∈ ca.source) ∧
    let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
    let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ Q ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Q,
      InjOn (fun z : (Fin d → ℝ) × K ↦ a (H.coordinate p z.1,N (p,z.1) z.2))
        (Metric.closedBall 0 ρ ×ˢ Metric.ball (0 : K) ε) ∧
      ∀ z ∈ Metric.closedBall 0 ρ ×ˢ Metric.ball (0 : K) ε,
        ((p,z.1) ∈ Ω ∧ (H.coordinate p z.1,N (p,z.1) z.2) ∈ U) ∧
        (fderiv ℝ (fun w : (Fin d → ℝ) × K ↦
          a (H.coordinate p w.1,N (p,w.1) w.2)) z).IsInvertible := by
  let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
  let ct := extChartAt (𝓘(ℝ,E)).tangent
    (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
  let a := ca ∘ riemannianExponential g ∘ ct.symm
  have h0 : (0 : Fin d → ℝ) ∈ Metric.ball 0 Φ.family.radius :=
    Metric.mem_ball_self Φ.family.radius_pos
  have hq0 : H.coordinate p₀ 0 = ca p₀.val := by
    exact (H.coordinate_eq p₀ h0).trans (congrArg ca (Φ.family.plaque p₀).centered)
  have hp : p₀.val ∈ ca.source := by
    simpa only [(Φ.family.plaque p₀).centered] using Φ.family.receiving_domain p₀ 0 h0
  obtain ⟨U,hU,hpU,hA,hguard⟩ :=
    riemannianExponential_fixed_coordinate_domain_g18 g Φ.family.receivingAnchor p₀.val hp
  have hder := riemannianExponential_fixed_coordinate_derivative_zero_g18
    g Φ.family.receivingAnchor p₀.val hp
  have hqU : (H.coordinate p₀ 0,0) ∈ U := by rwa [hq0]
  refine ⟨U,hU,hqU,hguard,?_⟩
  apply H.original_metric_normal_uniform_tube_g18 hn g p₀ a U hU (hA.of_le (by simp)) hqU
  · intro v hv hu
    have hpv : (Φ.family.plaque p₀).param v ∈ ca.source := Φ.family.receiving_domain p₀ v hv
    have hvq : H.coordinate p₀ v = ca ((Φ.family.plaque p₀).param v) := H.coordinate_eq p₀ hv
    rw [hvq]
    change ca (riemannianExponential g (ct.symm (ca ((Φ.family.plaque p₀).param v),0))) = _
    rw [extChartAt_tangent_symm_fibre_g18 Φ.family.receivingAnchor _ hpv 0]
    simp only [map_zero,(riemannianExponential_zero g ((Φ.family.plaque p₀).param v)).2]
  · intro v hv hu
    have hpv : (Φ.family.plaque p₀).param v ∈ ca.source := Φ.family.receiving_domain p₀ v hv
    have hvq : H.coordinate p₀ v = ca ((Φ.family.plaque p₀).param v) := H.coordinate_eq p₀ hv
    rw [hvq]
    exact riemannianExponential_fixed_coordinate_derivative_zero_g18
      g Φ.family.receivingAnchor _ hpv

end HolomorphicAnosov.HPS


