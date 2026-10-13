import HolomorphicAnosov.Geometry.PlaqueMetricNormalProjectionG18
import HolomorphicAnosov.Geometry.ParametricPlaqueTubeInverseG18
import Mathlib.Analysis.Normed.Operator.Prod

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable section
open Set
namespace HolomorphicAnosov
variable {P K E : Type*} {r : ℕ} [TopologicalSpace P]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (K →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] K →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Fin r → ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ]
    (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Fin r → ℝ) (F := (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E))
    (σ₁₂ := RingHom.id ℝ)
local instance : NormedAddCommGroup (((E →L[ℝ] E →L[ℝ] ℝ) ×
    ((Fin r → ℝ) →L[ℝ] E)) →L[ℝ] K →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E)) (F := K →L[ℝ] E)
    (σ₁₂ := RingHom.id ℝ)

/-- The metric-normal frame has jointly continuous spatial derivatives. -/
theorem parametric_metric_normal_frame_g18
    (b : P × (Fin r → ℝ) → E →L[ℝ] E →L[ℝ] ℝ)
    (D : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] E)
    (Db : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DD : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] E)
    (N₀ : K →L[ℝ] E) (Ω : Set (P × (Fin r → ℝ)))
    (hb : ContinuousOn b Ω) (hD : ContinuousOn D Ω)
    (hDb : ContinuousOn Db Ω) (hDD : ContinuousOn DD Ω)
    (hbpos : ∀ z ∈ Ω, ∀ v, v ≠ 0 → 0 < b z v v)
    (hDin : ∀ z ∈ Ω, Function.Injective (D z))
    (hbd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ b (z.1,v)) (Db z) z.2)
    (hDd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ D (z.1,v)) (DD z) z.2) :
    let N := fun z ↦ (ContinuousLinearMap.id ℝ E - plaqueMetricProjection (b z) (D z)).comp N₀
    ContinuousOn N Ω ∧ ∃ DN : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] K →L[ℝ] E,
      ContinuousOn DN Ω ∧ ∀ z ∈ Ω,
        HasFDerivAt (fun v ↦ N (z.1,v)) (DN z) z.2 := by
  let Φ := fun s : (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E) ↦
    (ContinuousLinearMap.id ℝ E - plaqueMetricProjection s.1 s.2).comp N₀
  let J := fun z ↦ (b z, D z)
  let DJ := fun z ↦ (Db z).prod (DD z)
  have hΦ (z) (hz : z ∈ Ω) : ContDiffAt ℝ 1 Φ (J z) :=
    (contDiffAt_const.sub (contDiffAt_plaqueMetricProjection
      (b z) (hbpos z hz) (D z) (hDin z hz) 1)).clm_comp contDiffAt_const
  have hJ : ContinuousOn J Ω := hb.prodMk hD
  have hDJ : ContinuousOn DJ Ω :=
    (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := Fin r → ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (G := (Fin r → ℝ) →L[ℝ] E) ℝ).continuous.comp_continuousOn
      (hDb.prodMk hDD)
  have hΦD : ContinuousOn (fun z ↦ fderiv ℝ Φ (J z)) Ω := by
    intro z hz
    exact ((hΦ z hz).continuousAt_fderiv (by norm_num)).comp_continuousWithinAt (hJ z hz)
  let DN : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] K →L[ℝ] E :=
    fun z ↦ (fderiv ℝ Φ (J z)).comp (DJ z)
  have hDN : ContinuousOn DN Ω := ContinuousOn.clm_comp
    (𝕜 := ℝ) (E := Fin r → ℝ)
    (F := (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E))
    (G := K →L[ℝ] E) hΦD hDJ
  dsimp only
  constructor
  · intro z hz
    exact (hΦ z hz).continuousAt.comp_continuousWithinAt (hJ z hz)
  refine ⟨DN, hDN, ?_⟩
  intro z hz
  have hJd : HasFDerivAt (fun v ↦ J (z.1, v)) (DJ z) z.2 :=
    HasFDerivAt.prodMk (𝕜 := ℝ) (E := Fin r → ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (G := (Fin r → ℝ) →L[ℝ] E)
      (hbd z hz) (hDd z hz)
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (J z)) (J z) :=
    ((hΦ z hz).differentiableAt (by norm_num)).hasFDerivAt
  exact HasFDerivAt.comp (𝕜 := ℝ) (E := Fin r → ℝ)
    (F := (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E))
    (G := K →L[ℝ] E) z.2 hΦd hJd


/-- The metric tensor and first two spatial plaque jets determine C¹ metric-normal tube charts with
a common receiving neighborhood. The normal coordinate space is the metric-normal kernel at the
reference center. -/
theorem parametric_metric_normal_tube_g18 [FiniteDimensional ℝ E]
    (q : P → (Fin r → ℝ) → E)
    (b : P × (Fin r → ℝ) → E →L[ℝ] E →L[ℝ] ℝ)
    (D : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] E)
    (Db : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DD : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] E)
    (Ω : Set (P × (Fin r → ℝ))) (hΩ : IsOpen Ω) (p₀ : P) (hp₀ : (p₀,0) ∈ Ω)
    (hq : ContinuousOn (fun z : P × (Fin r → ℝ) ↦ q z.1 z.2) Ω)
    (hb : ContinuousOn b Ω) (hD : ContinuousOn D Ω)
    (hDb : ContinuousOn Db Ω) (hDD : ContinuousOn DD Ω)
    (hbpos : ∀ z ∈ Ω, ∀ v, v ≠ 0 → 0 < b z v v)
    (hDin : ∀ z ∈ Ω, Function.Injective (D z))
    (hqd : ∀ z ∈ Ω, HasFDerivAt (q z.1) (D z) z.2)
    (hbd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ b (z.1,v)) (Db z) z.2)
    (hDd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ D (z.1,v)) (DD z) z.2)
    (a : E × E → E) (U : Set (E × E)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hu₀ : (q p₀ 0,0) ∈ U)
    (ha₀ : HasFDerivAt a (ContinuousLinearMap.fst ℝ E E +
      ContinuousLinearMap.snd ℝ E E) (q p₀ 0,0)) :
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∃ Q : TopologicalSpace.Opens P, ∃ hpQ : p₀ ∈ Q,
      ∃ W : Set E, IsOpen W ∧ a (q p₀ 0,0) ∈ W ∧
      ∃ e : Q → OpenPartialHomeomorph ((Fin r → ℝ) × K) E,
        (∀ p : Q, (e p : ((Fin r → ℝ) × K) → E) =
            (fun z ↦ a (q p.1 z.1,N (p.1,z.1) z.2)) ∧
          (e p).target = W ∧ ContDiffOn ℝ 1 (e p) (e p).source ∧
          ContDiffOn ℝ 1 (e p).symm (e p).target ∧
          ∀ z ∈ (e p).source, (p.1,z.1) ∈ Ω ∧ (q p.1 z.1,N (p.1,z.1) z.2) ∈ U) ∧
        ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2) (univ ×ˢ W) ∧
        ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W) ∧ 0 ∈ (e ⟨p₀,hpQ⟩).source ∧
        IsOpen {z : Q × ((Fin r → ℝ) × K) | z.2 ∈ (e z.1).source} := by
  let K₀ := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
  let N := fun z ↦ plaqueNormalFrame (b z) (D z) K₀.subtypeL
  obtain ⟨hN, DN, hDN, hNd⟩ := parametric_metric_normal_frame_g18
    b D Db DD K₀.subtypeL Ω hb hD hDb hDD hbpos hDin hbd hDd
  let A := plaqueTangentNormalEquiv (b (p₀,0)) (hbpos _ hp₀)
    (D (p₀,0)) (hDin _ hp₀)
  have hA : (D (p₀,0)).coprod (N (p₀,0)) = A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    have hz : plaqueMetricCoordinates (b (p₀,0)) (D (p₀,0)) z.2.val = 0 := z.2.property
    simp [A, N, plaqueTangentNormalEquiv, plaqueNormalFrame, plaqueMetricProjection, hz]
  exact parametric_plaque_tube_inverse_g18 q D N DN Ω hΩ p₀ hp₀ hq hD hN hDN
    hqd hNd a U hU ha hu₀ ha₀ A hA

/-- At the central zero vector, the base differential of a metric-normal tube inverse is the metric
Gram projection. -/
theorem metric_normal_tube_inverse_base_derivative_g18
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D)
    (q : (Fin r → ℝ) → E) (hq : HasFDerivAt q D 0)
    (N : (Fin r → ℝ) → plaqueNormalSpace b D →L[ℝ] E)
    (DN : (Fin r → ℝ) →L[ℝ] plaqueNormalSpace b D →L[ℝ] E)
    (hN : HasFDerivAt N DN 0) (hN0 : N 0 = (plaqueNormalSpace b D).subtypeL)
    (a : E × E → E)
    (ha : HasFDerivAt a (ContinuousLinearMap.fst ℝ E E +
      ContinuousLinearMap.snd ℝ E E) (q 0,0))
    (e : OpenPartialHomeomorph ((Fin r → ℝ) × plaqueNormalSpace b D) E)
    (he : (e : ((Fin r → ℝ) × plaqueNormalSpace b D) → E) =
      fun z ↦ a (q z.1,N z.1 z.2)) (h0 : 0 ∈ e.source) :
    HasFDerivAt (fun w ↦ q (e.symm w).1) (plaqueMetricProjection b D) (e 0) := by
  let A := plaqueTangentNormalEquiv b hb D hD
  have hA : D.coprod (N 0) = A.toContinuousLinearMap := by
    rw [hN0]
    rfl
  have hT : HasFDerivAt e A.toContinuousLinearMap 0 := by
    rw [he, ← hA]
    exact hasFDerivAt_plaque_normal_tube_zero_g18 q D 0 hq N DN hN a ha
  have hi : HasFDerivAt e.symm A.symm.toContinuousLinearMap (e 0) :=
    HasFDerivAt.of_local_left_inverse (e.continuousAt_symm (e.map_source h0))
      (by simpa only [e.left_inv h0] using hT) (e.eventually_right_inverse' h0)
  have hf := (hasFDerivAt_fst (𝕜 := ℝ) (p := e.symm (e 0))).comp (e 0) hi
  have hq' : HasFDerivAt q D (e.symm (e 0)).1 := by
    simpa only [e.left_inv h0, Prod.fst_zero] using hq
  convert hq'.comp (e 0) hf using 1 <;> rfl


open scoped _root_.Topology
/-- A small compact plaque core has an injective metric-normal tube with uniform radii for all
nearby parameters. -/
theorem parametric_metric_normal_uniform_tube_g18 [FiniteDimensional ℝ E]
    (q : P → (Fin r → ℝ) → E)
    (b : P × (Fin r → ℝ) → E →L[ℝ] E →L[ℝ] ℝ)
    (D : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] E)
    (Db : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DD : P × (Fin r → ℝ) → (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] E)
    (Ω : Set (P × (Fin r → ℝ))) (hΩ : IsOpen Ω) (p₀ : P) (hp₀ : (p₀,0) ∈ Ω)
    (hq : ContinuousOn (fun z : P × (Fin r → ℝ) ↦ q z.1 z.2) Ω)
    (hb : ContinuousOn b Ω) (hD : ContinuousOn D Ω)
    (hDb : ContinuousOn Db Ω) (hDD : ContinuousOn DD Ω)
    (hbpos : ∀ z ∈ Ω, ∀ v, v ≠ 0 → 0 < b z v v)
    (hDin : ∀ z ∈ Ω, Function.Injective (D z))
    (hqd : ∀ z ∈ Ω, HasFDerivAt (q z.1) (D z) z.2)
    (hbd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ b (z.1,v)) (Db z) z.2)
    (hDd : ∀ z ∈ Ω, HasFDerivAt (fun v ↦ D (z.1,v)) (DD z) z.2)
    (a : E × E → E) (U : Set (E × E)) (hU : IsOpen U)
    (ha : ContDiffOn ℝ 1 a U) (hu₀ : (q p₀ 0,0) ∈ U)
    (hzero : ∀ v, (p₀,v) ∈ Ω → (q p₀ v,0) ∈ U → a (q p₀ v,0) = q p₀ v)
    (ha₀ : ∀ v, (p₀,v) ∈ Ω → (q p₀ v,0) ∈ U →
      HasFDerivAt a (ContinuousLinearMap.fst ℝ E E +
        ContinuousLinearMap.snd ℝ E E) (q p₀ v,0))
    (hinj : InjOn (q p₀) {v | (p₀,v) ∈ Ω}) :
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ Q ∈ 𝓝 p₀, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Q,
      InjOn (fun z : (Fin r → ℝ) × K ↦ a (q p z.1,N (p,z.1) z.2))
        (Metric.closedBall 0 ρ ×ˢ Metric.ball (0 : K) ε) ∧
      ∀ z ∈ Metric.closedBall 0 ρ ×ˢ Metric.ball (0 : K) ε,
        ((p,z.1) ∈ Ω ∧ (q p z.1,N (p,z.1) z.2) ∈ U) ∧
        (fderiv ℝ (fun w : (Fin r → ℝ) × K ↦ a (q p w.1,N (p,w.1) w.2)) z).IsInvertible := by
  let K₀ := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
  let N := fun z ↦ plaqueNormalFrame (b z) (D z) K₀.subtypeL
  obtain ⟨hN, DN, hDN, hNd⟩ := parametric_metric_normal_frame_g18
    b D Db DD K₀.subtypeL Ω hb hD hDb hDD hbpos hDin hbd hDd
  have hJ := (hb.prodMk hD).continuousAt (hΩ.mem_nhds hp₀)
  have hi : ∀ᶠ z in 𝓝 (p₀,(0 : Fin r → ℝ)),
      ((D z).coprod (N z)).IsInvertible :=
    hJ.eventually (eventually_invertible_plaque_normal_frame_g18
      (b (p₀,0)) (hbpos _ hp₀) (D (p₀,0)) (hDin _ hp₀))
  have hc : ContinuousAt (fun v : Fin r → ℝ ↦ (p₀,v)) 0 :=
    continuousAt_const.prodMk continuousAt_id
  have hq₀ := (hq.continuousAt (hΩ.mem_nhds hp₀)).comp hc
  have hqu : ∀ᶠ v in 𝓝 (0 : Fin r → ℝ), (q p₀ v,0) ∈ U :=
    (hq₀.prodMk continuousAt_const).eventually (hU.mem_nhds hu₀)
  have hall : ∀ᶠ v in 𝓝 (0 : Fin r → ℝ),
      (p₀,v) ∈ Ω ∧ (q p₀ v,0) ∈ U ∧ ((D (p₀,v)).coprod (N (p₀,v))).IsInvertible := by
    filter_upwards [hc.eventually (hΩ.mem_nhds hp₀),hqu,hc.eventually hi] with v hv hu hi
    exact ⟨hv,hu,hi⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hall
  have hsmall : Metric.closedBall (0 : Fin r → ℝ) (R / 2) ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball (by linarith)
  have hcore v (hv : v ∈ Metric.closedBall (0 : Fin r → ℝ) (R / 2)) := hball (hsmall hv)
  refine ⟨R / 2,by positivity,?_⟩
  apply parametric_plaque_tube_uniform_injective_g18 q D N DN Ω hΩ hq hD hN hDN hqd hNd
    a U hU ha p₀ (Metric.closedBall 0 (R / 2)) (isCompact_closedBall _ _)
  · exact fun v hv ↦ (hcore v hv).1
  · exact fun v hv ↦ (hcore v hv).2.1
  · exact fun v hv ↦ hzero v (hcore v hv).1 (hcore v hv).2.1
  · exact fun v hv ↦ ha₀ v (hcore v hv).1 (hcore v hv).2.1
  · exact hinj.mono (fun v hv ↦ (hcore v hv).1)
  · exact fun v hv ↦ (hcore v hv).2.2

end HolomorphicAnosov



