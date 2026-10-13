import HolomorphicAnosov.Geometry.ContinuousOriginalFrameNorms
import HolomorphicAnosov.Analysis.MovingAlmostIsometryG18
import HolomorphicAnosov.Geometry.NativePlaqueIntrinsicPathBoundsLowerG18
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import HolomorphicAnosov.Geometry.NativePlaqueMetricTubeG18
import HolomorphicAnosov.Geometry.PlaqueMetricNormalProjectionG18
import HolomorphicAnosov.Geometry.ParametricPlaqueTubeInverseG18
import Mathlib.Analysis.Normed.Operator.Prod

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable section
open Set
namespace HolomorphicAnosov
open Filter
open scoped _root_.Topology

/-- An eventual relation for an open family of marked points holds on a common ambient neighborhood
of the marked label and second argument. -/
theorem open_label_relation_localization_g18
    {Q M : Type*} [TopologicalSpace Q] [TopologicalSpace M]
    (j : Q → M) (hj : _root_.Topology.IsOpenEmbedding j) (q₀ : Q)
    (R : Q → M → Prop) (hR : ∀ᶠ z : Q × M in 𝓝 (q₀,j q₀), R z.1 z.2)
    (G : Set M) (hG : IsOpen G) (hqG : j q₀ ∈ G) :
    ∃ A : Set M, IsOpen A ∧ j q₀ ∈ A ∧ A ⊆ G ∧
      ∀ q, j q ∈ A → ∀ x ∈ A, R q x := by
  obtain ⟨U,V,hU,hqU,hV,hjV,hUV⟩ := mem_nhds_prod_iff'.mp hR
  refine ⟨(j '' U ∩ V) ∩ G, ((hj.isOpenMap _ hU).inter hV).inter hG,
    ⟨⟨⟨q₀,hqU,rfl⟩,hjV⟩,hqG⟩,fun _ h ↦ h.2,?_⟩
  intro q hq x hx
  obtain ⟨q',hq',heq⟩ := hq.1.1
  have hqU' : q ∈ U := hj.injective heq ▸ hq'
  exact hUV (show (q,x) ∈ U ×ˢ V from ⟨hqU',hx.1.2⟩)


variable {P K E : Type*} {r : ℕ} [TopologicalSpace P]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance nativeTubeDerivativeNormInst0 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst2 : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst3 : NormedAddCommGroup (K →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst4 : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] K →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst5 : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Fin r → ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance nativeTubeDerivativeNormInst6 : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst7 : NormedAddCommGroup ((Fin r → ℝ) →L[ℝ]
    (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E)) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Fin r → ℝ) (F := (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E))
    (σ₁₂ := RingHom.id ℝ)
local instance nativeTubeDerivativeNormInst8 : NormedAddCommGroup (((E →L[ℝ] E →L[ℝ] ℝ) ×
    ((Fin r → ℝ) →L[ℝ] E)) →L[ℝ] K →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := (E →L[ℝ] E →L[ℝ] ℝ) × ((Fin r → ℝ) →L[ℝ] E)) (F := K →L[ℝ] E)
    (σ₁₂ := RingHom.id ℝ)

/-- The derivative of the base projection of an invertible normal tube frame is the metric
orthogonal projection at a zero-normal point. -/
theorem metric_normal_tube_inverse_fixed_frame_g18
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D)
    (q : (Fin r → ℝ) → E) (u₀ : Fin r → ℝ) (hq : HasFDerivAt q D u₀)
    (N : (Fin r → ℝ) → K →L[ℝ] E)
    (DN : (Fin r → ℝ) →L[ℝ] K →L[ℝ] E)
    (hN : HasFDerivAt N DN u₀) (N₀ : K →L[ℝ] E)
    (hN0 : N u₀ = plaqueNormalFrame b D N₀)
    (hAinv : (D.coprod (N u₀)).IsInvertible)
    (a : E × E → E)
    (ha : HasFDerivAt a (ContinuousLinearMap.fst ℝ E E +
      ContinuousLinearMap.snd ℝ E E) (q u₀,0))
    (e : OpenPartialHomeomorph ((Fin r → ℝ) × K) E)
    (he : (e : ((Fin r → ℝ) × K) → E) =
      fun z ↦ a (q z.1,N z.1 z.2)) (h0 : (u₀,0) ∈ e.source) :
    HasFDerivAt (fun w ↦ q (e.symm w).1) (plaqueMetricProjection b D) (e (u₀,0)) := by
  obtain ⟨A,hA⟩ := hAinv
  have hA' : D.coprod (N u₀) = A.toContinuousLinearMap := hA.symm
  have hcN (k : K) : plaqueMetricCoordinates b D (N u₀ k) = 0 := by
    rw [hN0]
    change plaqueMetricCoordinates b D (N₀ k - D (plaqueMetricCoordinates b D (N₀ k))) = 0
    rw [map_sub, plaqueMetricCoordinates_derivative b hb D hD, sub_self]
  have hcA (w : E) : (A.symm w).1 = plaqueMetricCoordinates b D w := by
    have hs : D (A.symm w).1 + N u₀ (A.symm w).2 = w := by
      change (D.coprod (N u₀)) (A.symm w) = w
      rw [hA']
      exact A.apply_symm_apply w
    have hh := congrArg (plaqueMetricCoordinates b D) hs
    simpa only [map_add,plaqueMetricCoordinates_derivative b hb D hD,hcN,add_zero] using hh
  have hT : HasFDerivAt e A.toContinuousLinearMap (u₀,0) := by
    rw [he, ← hA']
    exact hasFDerivAt_plaque_normal_tube_zero_g18 q D u₀ hq N DN hN a ha
  have hi : HasFDerivAt e.symm A.symm.toContinuousLinearMap (e (u₀,0)) :=
    HasFDerivAt.of_local_left_inverse (e.continuousAt_symm (e.map_source h0))
      (by simpa only [e.left_inv h0] using hT) (e.eventually_right_inverse' h0)
  have hf := (hasFDerivAt_fst (𝕜 := ℝ) (p := e.symm (e (u₀,0)))).comp (e (u₀,0)) hi
  have hq' : HasFDerivAt q D (e.symm (e (u₀,0))).1 := by
    simpa only [e.left_inv h0] using hq
  convert hq'.comp (e (u₀,0)) hf using 1
  · rfl
  · ext w
    exact congrArg D (hcA w).symm
end HolomorphicAnosov

end
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff _root_.Topology
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

local instance nativeTubeDerivativeNormInst9 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst10 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst11 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance nativeTubeDerivativeNormInst12 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst13 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance nativeTubeDerivativeNormInst14 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Fin d → ℝ)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

/-- The base projection of a native exponential tube has derivative equal to the original-metric
orthogonal projection at each zero-normal point. -/
theorem native_inverse_projection_derivative_g18 [T2Space M]
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ p : Φ.family.centerDomain) (u : Fin d → ℝ)
    (hu : u ∈ Metric.ball 0 Φ.family.radius) :
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
    let ct := extChartAt 𝓘(ℝ,E).tangent
      (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
    ∀ e : OpenPartialHomeomorph ((Fin d → ℝ) × K) E,
      (e : ((Fin d → ℝ) × K) → E) =
        (fun z ↦ ca (riemannianExponential g (ct.symm (H.coordinate p z.1,N (p,z.1) z.2)))) →
      (u,0) ∈ e.source → ((D (p,u)).coprod (N (p,u))).IsInvertible →
      HasFDerivAt (fun w ↦ H.coordinate p (e.symm w).1)
        (plaqueMetricProjection (b (p,u)) (D (p,u))) (H.coordinate p u) := by
  dsimp only
  intro e he hsource hinv
  let q := H.coordinate p
  let D := fun v ↦ fderiv ℝ q v
  let β := originalMetricChartTensor_g18 g Φ.family.receivingAnchor
  let b := fun v ↦ β (q v)
  let K := plaqueNormalSpace
    (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate p₀ 0))
    (fderiv ℝ (H.coordinate p₀) 0)
  let N := fun v ↦ plaqueNormalFrame (b v) (D v) K.subtypeL
  let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
  let ct := extChartAt 𝓘(ℝ,E).tangent
    (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
  have hx := Φ.family.receiving_domain p u hu
  have hq : HasFDerivAt q (D u) u :=
    ((H.coordinate_smooth p).contDiffAt (Metric.isOpen_ball.mem_nhds hu)).differentiableAt
      (by simp) |>.hasFDerivAt
  have hDd : DifferentiableAt ℝ D u :=
    (((H.coordinate_smooth p).contDiffAt (Metric.isOpen_ball.mem_nhds hu)).fderiv_right
      (m := 1) (by simp)).differentiableAt (by simp)
  have htarget : q u ∈ ca.target := by
    rw [show q u = ca ((Φ.family.plaque p).param u) from H.coordinate_eq p hu]
    exact ca.map_source hx
  have hbpos : ∀ w, w ≠ 0 → 0 < b u w w :=
    originalMetricChartTensor_pos_g18 g Φ.family.receivingAnchor (q u) htarget
  have hDin : Function.Injective (D u) := by
    have hv : u ∈ (Φ.family.plaque p).domain := by rw [Φ.family.domain_eq]; exact hu
    have hφ := ((Φ.family.plaque p).smooth u hv).contMDiffAt
      ((Φ.family.plaque p).domain_open.mem_nhds hv)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E))
      (by simpa only [extChartAt_source] using hx)
    have hchain := mfderiv_comp u hc (hφ.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hchain
    change fderiv ℝ (fun v ↦ ca ((Φ.family.plaque p).param v)) u = _ at hchain
    have heq : q =ᶠ[𝓝 u] (fun v ↦ ca ((Φ.family.plaque p).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hu] with v hv
      exact H.coordinate_eq p hv
    change Function.Injective (fderiv ℝ q u)
    rw [heq.fderiv_eq,hchain]
    apply Function.Injective.comp _ ((Φ.family.plaque p).immersed u hv)
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hx
    rw [← hA]
    exact A.injective
  have hbd : DifferentiableAt ℝ b u :=
    (((originalMetricChartTensor_contDiffOn_g18 g Φ.family.receivingAnchor).contDiffAt
      ((isOpen_extChartAt_target Φ.family.receivingAnchor).mem_nhds htarget)).differentiableAt
        (by simp)).comp u hq.differentiableAt
  have hProj : DifferentiableAt ℝ (fun v ↦ plaqueMetricProjection (b v) (D v)) u :=
    ((contDiffAt_plaqueMetricProjection (b u) hbpos (D u) hDin 1).differentiableAt
      (by norm_num)).comp u (f := fun v : Fin d → ℝ ↦ (b v,D v)) (hbd.prodMk hDd)
  have hNd : DifferentiableAt ℝ N u :=
    ((differentiableAt_const (ContinuousLinearMap.id ℝ E)).sub hProj).clm_comp
      (differentiableAt_const K.subtypeL)
  have ha := riemannianExponential_fixed_coordinate_derivative_zero_g18
    g Φ.family.receivingAnchor ((Φ.family.plaque p).param u) hx
  have hqu : q u = ca ((Φ.family.plaque p).param u) := H.coordinate_eq p hu
  have ha' : HasFDerivAt (ca ∘ riemannianExponential g ∘ ct.symm)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (q u,0) := by
    rw [hqu]
    exact ha
  have hcenter : e (u,0) = q u := by
    rw [he]
    change ca (riemannianExponential g (ct.symm (q u,N u 0))) = q u
    rw [map_zero,hqu,extChartAt_tangent_symm_fibre_g18 Φ.family.receivingAnchor _ hx 0]
    simp only [map_zero,(riemannianExponential_zero g ((Φ.family.plaque p).param u)).2]
  have hd := metric_normal_tube_inverse_fixed_frame_g18 (b u) hbpos (D u) hDin
    q u hq N (fderiv ℝ N u) hNd.hasFDerivAt K.subtypeL rfl hinv
    (ca ∘ riemannianExponential g ∘ ct.symm) ha' e he hsource
  rw [hcenter] at hd
  exact hd
end HolomorphicAnosov.HPS

end
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov
variable {E V K F HZ M Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace HZ] (J : ModelWithCorners ℝ F HZ)
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace Z] [ChartedSpace HZ Z]

/-- The local base projection defined through a receiving chart and a smooth native lift is smooth
on its guarded open domain. -/
theorem native_local_smooth_projection_g18 (anchor : M)
    (B : Opens V) (l : B → Z) (hl : ContMDiff 𝓘(ℝ,V) J 1 l)
    (e : OpenPartialHomeomorph (V × K) E)
    (he : ContDiffOn ℝ 1 e.symm e.target)
    (hguard : ∀ z ∈ e.source, z.1 ∈ B) :
    let ca := extChartAt 𝓘(ℝ,E) anchor
    ∃ hO : IsOpen (ca.source ∩ ca ⁻¹' e.target),
    let O : Opens M := ⟨ca.source ∩ ca ⁻¹' e.target,hO⟩
    ∃ ψ : O → Z, ContMDiff 𝓘(ℝ,E) J 1 ψ ∧
      ∀ z : O, ψ z = l ⟨(e.symm (ca z.val)).1,hguard _ (e.map_target z.property.2)⟩ := by
  let ca := extChartAt 𝓘(ℝ,E) anchor
  have hO : IsOpen (ca.source ∩ ca ⁻¹' e.target) :=
    (continuousOn_extChartAt (I := 𝓘(ℝ,E)) anchor).isOpen_inter_preimage
      (isOpen_extChartAt_source anchor) e.open_target
  let O : Opens M := ⟨ca.source ∩ ca ⁻¹' e.target,hO⟩
  let π : O → B := fun z ↦ ⟨(e.symm (ca z.val)).1,hguard _ (e.map_target z.property.2)⟩
  have hc : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) 1 ca ca.source := by
    simpa only [ca,extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := anchor) (n := 1))
  have hπval : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) 1 (Subtype.val ∘ π) := by
    intro z
    have hca := (hc.contMDiffAt ((isOpen_extChartAt_source anchor).mem_nhds z.property.1)).comp
      z (contMDiff_subtype_val (I := 𝓘(ℝ,E)) (U := O) (n := 1)).contMDiffAt
    have hi := ((he.contDiffAt (e.open_target.mem_nhds z.property.2)).contMDiffAt).comp z hca
    have hf : ContMDiff 𝓘(ℝ,V × K) 𝓘(ℝ,V) 1 (Prod.fst : V × K → V) :=
      contDiff_fst.contMDiff
    exact hf.contMDiffAt.comp z hi
  have hπ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) 1 π := by
    intro z
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff π univ z).mp (hπval z)
  exact ⟨hO,l ∘ π,hl.comp hπ,fun _ ↦ rfl⟩
end HolomorphicAnosov

end

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

local instance nativeNormalSizeNormInst0 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeNormalSizeNormInst1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeNormalSizeNormInst2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance nativeNormalSizeNormInst3 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance nativeNormalSizeNormInst4 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance nativeNormalSizeNormInst5 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Fin d → ℝ)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

/-- The length of the physical normal vector in the original metric is continuous at each guarded
native tube coordinate. -/
theorem native_normal_size_at_point_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ p : Φ.family.centerDomain) (u : Fin d → ℝ)
    (hu : u ∈ Metric.ball 0 Φ.family.radius) :
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∀ k : K, ContinuousAt
      (fun z : (Fin d → ℝ) × K ↦ Real.sqrt (b (p,z.1) (N (p,z.1) z.2) (N (p,z.1) z.2)))
      (u,k) := by
  dsimp only
  intro k
  let q := H.coordinate p
  let D := fun v ↦ fderiv ℝ q v
  let β := originalMetricChartTensor_g18 g Φ.family.receivingAnchor
  let b := fun v ↦ β (q v)
  let K := plaqueNormalSpace
    (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate p₀ 0))
    (fderiv ℝ (H.coordinate p₀) 0)
  let N := fun v ↦ plaqueNormalFrame (b v) (D v) K.subtypeL
  let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
  have hx := Φ.family.receiving_domain p u hu
  have hq : HasFDerivAt q (D u) u :=
    ((H.coordinate_smooth p).contDiffAt (Metric.isOpen_ball.mem_nhds hu)).differentiableAt
      (by simp) |>.hasFDerivAt
  have hDd : DifferentiableAt ℝ D u :=
    (((H.coordinate_smooth p).contDiffAt (Metric.isOpen_ball.mem_nhds hu)).fderiv_right
      (m := 1) (by simp)).differentiableAt (by simp)
  have htarget : q u ∈ ca.target := by
    rw [show q u = ca ((Φ.family.plaque p).param u) from H.coordinate_eq p hu]
    exact ca.map_source hx
  have hbpos : ∀ w, w ≠ 0 → 0 < b u w w :=
    originalMetricChartTensor_pos_g18 g Φ.family.receivingAnchor (q u) htarget
  have hDin : Function.Injective (D u) := by
    have hv : u ∈ (Φ.family.plaque p).domain := by rw [Φ.family.domain_eq]; exact hu
    have hφ := ((Φ.family.plaque p).smooth u hv).contMDiffAt
      ((Φ.family.plaque p).domain_open.mem_nhds hv)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E))
      (by simpa only [extChartAt_source] using hx)
    have hchain := mfderiv_comp u hc (hφ.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hchain
    change fderiv ℝ (fun v ↦ ca ((Φ.family.plaque p).param v)) u = _ at hchain
    have heq : q =ᶠ[𝓝 u] (fun v ↦ ca ((Φ.family.plaque p).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hu] with v hv
      exact H.coordinate_eq p hv
    change Function.Injective (fderiv ℝ q u)
    rw [heq.fderiv_eq,hchain]
    apply Function.Injective.comp _ ((Φ.family.plaque p).immersed u hv)
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hx
    rw [← hA]
    exact A.injective
  have hbd : DifferentiableAt ℝ b u :=
    (((originalMetricChartTensor_contDiffOn_g18 g Φ.family.receivingAnchor).contDiffAt
      ((isOpen_extChartAt_target Φ.family.receivingAnchor).mem_nhds htarget)).differentiableAt
        (by simp)).comp u hq.differentiableAt
  have hProj : DifferentiableAt ℝ (fun v ↦ plaqueMetricProjection (b v) (D v)) u :=
    ((contDiffAt_plaqueMetricProjection (b u) hbpos (D u) hDin 1).differentiableAt
      (by norm_num)).comp u (f := fun v : Fin d → ℝ ↦ (b v,D v)) (hbd.prodMk hDd)
  have hNd : DifferentiableAt ℝ N u :=
    ((differentiableAt_const (ContinuousLinearMap.id ℝ E)).sub hProj).clm_comp
      (differentiableAt_const K.subtypeL)
  have hNv : ContinuousAt (fun z : (Fin d → ℝ) × K ↦ N z.1 z.2) (u,k) :=
    (hNd.continuousAt.comp (x := (u,k)) (f := fun z : (Fin d → ℝ) × K ↦ z.1)
      continuousAt_fst).clm_apply continuousAt_snd
  exact Real.continuous_sqrt.continuousAt.comp
    (((hbd.continuousAt.comp (x := (u,k)) (f := fun z : (Fin d → ℝ) × K ↦ z.1)
      continuousAt_fst).clm_apply hNv).clm_apply hNv)
end HolomorphicAnosov.HPS

end

noncomputable section
open Set Filter
open scoped Manifold ContDiff _root_.Topology
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
  {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

omit [FiniteDimensional ℝ E] in
/-- The projected inverse tube derivative is jointly continuous in the receiving label and ambient
coordinate. -/
theorem native_inverse_projection_derivative_continuous_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (Q : TopologicalSpace.Opens Φ.family.centerDomain) (W : Set E)
    (e : Q → OpenPartialHomeomorph ((Fin d → ℝ) × K) E)
    (ht : ∀ p, (e p).target = W)
    (he : ∀ p, ContDiffOn ℝ 1 (e p).symm (e p).target)
    (hbase : ∀ p, ∀ z ∈ (e p).source, z.1 ∈ Metric.ball 0 Φ.family.radius)
    (hc : ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2) (univ ×ˢ W))
    (hd : ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W)) :
    ContinuousOn (fun z : Q × E ↦
      fderiv ℝ (fun w ↦ H.coordinate z.1.val ((e z.1).symm w).1) z.2) (univ ×ˢ W) := by
  let Ω : Set (Φ.family.centerDomain × (Fin d → ℝ)) :=
    univ ×ˢ Metric.ball 0 Φ.family.radius
  let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
  have hD : ContinuousOn D Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc' := Φ.family.jointly_continuous_derivative.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    apply hc'.congr
    intro z
    have hq : H.coordinate z.1.1 =ᶠ[𝓝 z.1.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds z.property.2] with v hv
      exact H.coordinate_eq z.1.1 hv
    exact hq.fderiv_eq.symm
  let v : Q × E → Φ.family.centerDomain × (Fin d → ℝ) :=
    fun z ↦ (z.1.val,((e z.1).symm z.2).1)
  have hv : ContinuousOn v (univ ×ˢ W) :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.prodMk hc.fst
  have hmaps : MapsTo v (univ ×ˢ W) Ω := by
    intro z hz
    refine ⟨mem_univ _,hbase z.1 _ ((e z.1).map_target ?_)⟩
    rw [ht]
    exact hz.2
  have hformula (z : Q × E) (hz : z ∈ univ ×ˢ W) :
      fderiv ℝ (fun w ↦ H.coordinate z.1.val ((e z.1).symm w).1) z.2 =
      (D (v z)).comp ((ContinuousLinearMap.fst ℝ (Fin d → ℝ) K).comp
        (fderiv ℝ (e z.1).symm z.2)) := by
    have htarget : z.2 ∈ (e z.1).target := by rw [ht]; exact hz.2
    have hi := ((he z.1).contDiffAt ((e z.1).open_target.mem_nhds htarget)).differentiableAt
      (by simp : (1 : WithTop ℕ∞) ≠ 0)
    have hq := ((H.coordinate_smooth z.1.val).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hmaps hz).2)).differentiableAt (by simp)
    exact (hq.hasFDerivAt.comp z.2 hi.hasFDerivAt.fst).fderiv
  have hf : ContinuousOn (fun _z : Q × E ↦ ContinuousLinearMap.fst ℝ (Fin d → ℝ) K)
      (univ ×ˢ W) := continuousOn_const
  exact ((hD.comp hv hmaps).clm_comp (hf.clm_comp hd)).congr hformula
end HolomorphicAnosov.HPS
end

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped ContDiff Manifold _root_.Topology ENNReal
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
/-- The intrinsic Hermitian leaf distance is jointly continuous in the intrinsic leaf topology.
(Lee, Ch. 11) -/
theorem intrinsicHermitianLeafEDist_continuous_g18
    {r d : ℕ} {L M : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
 :
    Continuous (fun xy : L × L ↦ intrinsicHermitianLeafEDist (r := r) inc h xy.1 xy.2) := by
  obtain ⟨m,hm,he⟩ := hermitian_pullback_emetric h hh inc hinc hi
  let : EMetricSpace L := m.replaceTopology hm.symm
  exact continuous_edist.congr (fun xy ↦ he xy.1 xy.2)
end HolomorphicAnosov

end

noncomputable section
open Set Bundle
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- A continuous coordinate operator transports continuous tangent vectors continuously through a
fixed ambient tangent trivialization. -/
theorem tangent_chart_operator_continuous_g18
    {B : Type*} [TopologicalSpace B] (anchor : M) (σ τ : B → M)
    (hτ : Continuous τ)
    (hσchart : ∀ t, σ t ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).baseSet)
    (hτchart : ∀ t, τ t ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).baseSet)
    (V : B → E →L[ℝ] E) (hV : Continuous V)
    (v : ∀ t, TangentSpace 𝓘(ℝ,E) (σ t))
    (hv : Continuous (fun t ↦ (⟨σ t,v t⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    Continuous (fun t ↦ (⟨τ t,
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).continuousLinearEquivAt
        ℝ (τ t) (hτchart t)).symm
      (V t ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).continuousLinearEquivAt
        ℝ (σ t) (hσchart t) (v t)))⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
  have hc : Continuous (fun t ↦ tr.continuousLinearEquivAt ℝ (σ t) (hσchart t) (v t)) :=
    (tr.continuousOn.comp_continuous hv (fun t ↦ tr.mem_source.mpr (hσchart t))).snd
  have hcoord := hτ.prodMk (hV.clm_apply hc)
  exact tr.continuousOn_symm.comp_continuous hcoord
    (fun t ↦ ⟨hτchart t,mem_univ _⟩)

/-- The physical projection of a continuous real tangent subbundle frame is continuous in the
tangent total space. -/
theorem physical_projection_frame_continuous_g18 {r : ℕ}
    (P : RealTangentDistribution 𝓘(ℝ,E) M) :
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) inferInstance
    ∀ e : Trivialization (Fin r → ℝ)
      (TotalSpace.proj (F := Fin r → ℝ) (E := fun x : M ↦ ↥(P x))),
    ∀ he : e.IsLinear ℝ,
    letI := he
    ∀ {B : Type*} [TopologicalSpace B] (anchor : M) (σ : B → e.baseSet), Continuous σ →
    ∀ (τ : B → M), Continuous τ →
    ∀ (hσchart : ∀ t, (σ t).val ∈
        (trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).baseSet)
      (hτchart : ∀ t, τ t ∈
        (trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).baseSet)
      (V : B → E →L[ℝ] E), Continuous V →
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let A : ∀ t : B, P (σ t).val →L[ℝ] TangentSpace 𝓘(ℝ,E) (τ t) := fun t ↦
      (tr.continuousLinearEquivAt ℝ (τ t) (hτchart t)).symm.toContinuousLinearMap.comp
        ((V t).comp ((tr.continuousLinearEquivAt ℝ (σ t).val (hσchart t)).toContinuousLinearMap.comp
          (P (σ t).val).subtypeL))
    Continuous (fun z : B × (Fin r → ℝ) ↦
      (⟨τ z.1,A z.1 ((e.linearEquivAt ℝ (σ z.1).val (σ z.1).prop).symm z.2)⟩ :
        TangentBundle 𝓘(ℝ,E) M)) := by
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) inferInstance
  intro e he
  let := he
  intro B _ anchor σ hσ τ hτ hσchart hτchart V hV
  dsimp only
  have hv := (continuous_induced_dom :
    Continuous (fun z : TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x)) ↦
      (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M))).comp
      (FixedBlockEstimates.Native.continuous_frame_totalSpace P e)
  have hv' := hv.comp ((hσ.comp continuous_fst).prodMk continuous_snd)
  exact tangent_chart_operator_continuous_g18 anchor
    (fun z : B × (Fin r → ℝ) ↦ (σ z.1).val) (fun z ↦ τ z.1)
    (hτ.comp continuous_fst) (fun z ↦ hσchart z.1) (fun z ↦ hτchart z.1)
    (fun z ↦ V z.1) (hV.comp continuous_fst)
    (fun z ↦ ((e.linearEquivAt ℝ (σ z.1).val (σ z.1).prop).symm z.2).val) hv'

/-- At a zero-normal diagonal, the metric projection transported through tangent charts is the
identity on the plaque tangent image. -/
theorem plaque_physical_projection_identity_g18 [FiniteDimensional ℝ E]
    {r : ℕ}
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (anchor : M) (P : (Fin r → ℝ) → M) (u : Fin r → ℝ)
    (hP : MDifferentiableAt 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u)
    (hPi : Function.Injective (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u))
    (hx : P u ∈ (extChartAt 𝓘(ℝ,E) anchor).source)
    (v : TangentSpace 𝓘(ℝ,E) (P u))
    (hv : v ∈ (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u).range) :
    let ca := extChartAt 𝓘(ℝ,E) anchor
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let hx' : P u ∈ tr.baseSet := by
      simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
    let J := tr.continuousLinearEquivAt ℝ (P u) hx'
    J.symm (plaqueMetricProjection (originalMetricChartTensor_g18 g anchor (ca (P u)))
      (fderiv ℝ (ca ∘ P) u) (J v)) = v := by
  dsimp only
  let ca := extChartAt 𝓘(ℝ,E) anchor
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
  have hx' : P u ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  let J := tr.continuousLinearEquivAt ℝ (P u) hx'
  let D := fderiv ℝ (ca ∘ P) u
  have hJ : J.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca (P u) := by
    rw [show J.toContinuousLinearMap = tr.continuousLinearMapAt ℝ (P u) from
      tr.coe_continuousLinearEquivAt_eq' hx']
    exact TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hx)
  have hD : D = J.toContinuousLinearMap.comp (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u) := by
    rw [hJ]
    have hh := mfderiv_comp u (mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using hx)) hP
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hDi : Function.Injective D := by
    rw [hD]
    exact J.injective.comp hPi
  change J.symm (plaqueMetricProjection (originalMetricChartTensor_g18 g anchor (ca (P u)))
    D (J v)) = v
  obtain ⟨a,rfl⟩ := hv
  have hDa : J (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u a) = D a := by
    rw [hD]
    rfl
  let β := originalMetricChartTensor_g18 g anchor (ca (P u))
  exact (congrArg J.symm ((congrArg (plaqueMetricProjection β D) hDa).trans
    (plaqueMetricProjection_derivative β
      (originalMetricChartTensor_pos_g18 g anchor (ca (P u)) (ca.map_source hx)) D hDi a))).trans
    ((congrArg J.symm hDa.symm).trans (J.symm_apply_apply _))

end HolomorphicAnosov

end

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov.FixedBlockEstimates.Native
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- A continuous operator on a real tangent subbundle that is isometric at a marked point is
uniformly near-isometric nearby in the original metric. -/
theorem original_frame_nearisometry_g18 {r : ℕ}
    (P : RealTangentDistribution 𝓘(ℝ,E) M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _)) :
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) inferInstance
    ∀ e : Trivialization (Fin r → ℝ)
      (TotalSpace.proj (F := Fin r → ℝ) (E := fun x : M ↦ ↥(P x))),
    ∀ he : e.IsLinear ℝ,
    letI := he
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {B : Type*} [TopologicalSpace B] (σ : B → e.baseSet), Continuous σ →
    ∀ (τ : B → M) (A : ∀ t : B, P (σ t).val →L[ℝ] TangentSpace 𝓘(ℝ,E) (τ t)),
    Continuous (fun z : B × (Fin r → ℝ) ↦
      (⟨τ z.1,A z.1 ((e.linearEquivAt ℝ (σ z.1).val (σ z.1).prop).symm z.2)⟩ :
        TangentBundle 𝓘(ℝ,E) M)) →
    ∀ t₀ : B, (∀ v, ‖A t₀ v‖ = ‖v‖) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 t₀, ∀ v : P (σ t).val,
      (1-ε)*‖v‖ ≤ ‖A t v‖ ∧ ‖A t v‖ ≤ (1+ε)*‖v‖ := by
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) inferInstance
  intro e he
  let := he
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) :=
    ⟨g.toRiemannianMetric⟩
  intro B _ σ hσ τ A hA t₀ hisom ε hε
  have hv := (continuous_induced_dom :
    Continuous (fun z : TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x)) ↦
      (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M))).comp
      (continuous_frame_totalSpace P e)
  have hs := continuous_original_norm g (fun z : e.baseSet × (Fin r → ℝ) ↦ z.1.val)
    (fun z ↦ ((e.linearEquivAt ℝ z.1.val z.1.prop).symm z.2).val) hv
  have hs' : Continuous (fun z : B × (Fin r → ℝ) ↦
      ‖(e.linearEquivAt ℝ (σ z.1).val (σ z.1).prop).symm z.2‖) :=
    hs.comp ((hσ.comp continuous_fst).prodMk continuous_snd)
  have ht := continuous_original_norm g (fun z : B × (Fin r → ℝ) ↦ τ z.1)
    (fun z ↦ A z.1 ((e.linearEquivAt ℝ (σ z.1).val (σ z.1).prop).symm z.2)) hA
  exact moving_isometry_eventually_norm_bounds_g18
    (fun t ↦ (e.linearEquivAt ℝ (σ t).val (σ t).prop).symm) A hs' ht t₀ hisom hε
end HolomorphicAnosov.FixedBlockEstimates.Native
end
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Continuous projection derivatives transported through tangent charts are uniformly
near-isometric near an isometric diagonal in the original metric. -/
theorem physical_frame_nearisometry_g18 {r : ℕ}
    (P : RealTangentDistribution 𝓘(ℝ,E) M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _)) :
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) inferInstance
    ∀ e : Trivialization (Fin r → ℝ)
      (TotalSpace.proj (F := Fin r → ℝ) (E := fun x : M ↦ ↥(P x))),
    ∀ he : e.IsLinear ℝ,
    letI := he
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
    ∀ {B : Type*} [TopologicalSpace B] (anchor : M) (σ : B → e.baseSet), Continuous σ →
    ∀ (τ : B → M), Continuous τ →
    ∀ (hσchart : ∀ t, (σ t).val ∈
        (trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).baseSet)
      (hτchart : ∀ t, τ t ∈
        (trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor).baseSet)
      (V : B → E →L[ℝ] E), Continuous V →
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let A : ∀ t : B, P (σ t).val →L[ℝ] TangentSpace 𝓘(ℝ,E) (τ t) := fun t ↦
      (tr.continuousLinearEquivAt ℝ (τ t) (hτchart t)).symm.toContinuousLinearMap.comp
        ((V t).comp ((tr.continuousLinearEquivAt ℝ (σ t).val (hσchart t)).toContinuousLinearMap.comp
          (P (σ t).val).subtypeL))
    ∀ t₀ : B, (∀ v, ‖A t₀ v‖ = ‖v‖) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 t₀, ∀ v : P (σ t).val,
        (1-ε)*‖v‖ ≤ ‖A t v‖ ∧ ‖A t v‖ ≤ (1+ε)*‖v‖ := by
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) inferInstance
  intro e he
  let := he
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
  intro B _ anchor σ hσ τ hτ hσchart hτchart V hV
  dsimp only
  intro t₀ hdiag ε hε
  exact FixedBlockEstimates.Native.original_frame_nearisometry_g18 P g e he σ hσ τ _
    (physical_projection_frame_continuous_g18 P e he anchor σ hσ τ hτ hσchart hτchart V hV)
    t₀ hdiag ε hε
end HolomorphicAnosov

end

noncomputable section
open Set Bundle
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov
variable {E M EX HX X EY HY Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  (IX : ModelWithCorners ℝ EX HX) [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  (IY : ModelWithCorners ℝ EY HY) [TopologicalSpace Y] [ChartedSpace HY Y]

/-- A local coordinate formula for an intrinsic projection identifies its ambient derivative with
the coordinate derivative transported through tangent charts. -/
theorem intrinsic_coordinate_derivative_g18
    (anchor : M) (incX : X → M) (incY : Y → M) (projMap : X → Y) (x : X)
    (hX : MDifferentiableAt IX 𝓘(ℝ,E) incX x)
    (hY : MDifferentiableAt IY 𝓘(ℝ,E) incY (projMap x))
    (hprojMap : MDifferentiableAt IX IY projMap x)
    (hx : incX x ∈ (extChartAt 𝓘(ℝ,E) anchor).source)
    (hy : incY (projMap x) ∈ (extChartAt 𝓘(ℝ,E) anchor).source)
    (F : E → E) (V : E →L[ℝ] E)
    (hF : HasFDerivAt F V (extChartAt 𝓘(ℝ,E) anchor (incX x)))
    (heq : ((extChartAt 𝓘(ℝ,E) anchor) ∘ incY ∘ projMap) =ᶠ[𝓝 x]
      (F ∘ (extChartAt 𝓘(ℝ,E) anchor) ∘ incX)) :
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let hx' : incX x ∈ tr.baseSet := by
      simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
    let hy' : incY (projMap x) ∈ tr.baseSet := by
      simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hy
    let Jin := tr.continuousLinearEquivAt ℝ (incX x) hx'
    let Jout := tr.continuousLinearEquivAt ℝ (incY (projMap x)) hy'
    (mfderiv IY 𝓘(ℝ,E) incY (projMap x)).comp (mfderiv IX IY projMap x) =
      Jout.symm.toContinuousLinearMap.comp (V.comp
        (Jin.toContinuousLinearMap.comp (mfderiv IX 𝓘(ℝ,E) incX x))) := by
  dsimp only
  let ca := extChartAt 𝓘(ℝ,E) anchor
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
  have hx' : incX x ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  have hy' : incY (projMap x) ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hy
  let Jin := tr.continuousLinearEquivAt ℝ (incX x) hx'
  let Jout := tr.continuousLinearEquivAt ℝ (incY (projMap x)) hy'
  have hJin : Jin.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca (incX x) := by
    rw [show Jin.toContinuousLinearMap = tr.continuousLinearMapAt ℝ (incX x) from
      tr.coe_continuousLinearEquivAt_eq' hx']
    exact TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hx)
  have hJout : Jout.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca (incY (projMap x)) := by
    rw [show Jout.toContinuousLinearMap = tr.continuousLinearMapAt ℝ (incY (projMap x)) from
      tr.coe_continuousLinearEquivAt_eq' hy']
    exact TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hy)
  have hcx : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) ca (incX x) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hcy : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) ca (incY (projMap x)) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hy)
  have hl : mfderiv IX 𝓘(ℝ,E) (ca ∘ incY ∘ projMap) x =
      Jout.toContinuousLinearMap.comp
        ((mfderiv IY 𝓘(ℝ,E) incY (projMap x)).comp (mfderiv IX IY projMap x)) := by
    rw [hJout,mfderiv_comp x hcy (hY.comp x hprojMap),mfderiv_comp x hY hprojMap]
    rfl
  have hr : mfderiv IX 𝓘(ℝ,E) (F ∘ ca ∘ incX) x =
      V.comp (Jin.toContinuousLinearMap.comp (mfderiv IX 𝓘(ℝ,E) incX x)) := by
    have hFm : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) F (ca (incX x)) = V :=
      mfderiv_eq_fderiv.trans hF.fderiv
    rw [hJin,mfderiv_comp x hF.differentiableAt.mdifferentiableAt (hcx.comp x hX),
      mfderiv_comp x hcx hX]
    exact congrArg (fun A : E →L[ℝ] E ↦ A.comp
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca (incX x)).comp (mfderiv IX 𝓘(ℝ,E) incX x))) hFm
  have hder : Jout.toContinuousLinearMap.comp
        ((mfderiv IY 𝓘(ℝ,E) incY (projMap x)).comp (mfderiv IX IY projMap x)) =
      V.comp (Jin.toContinuousLinearMap.comp (mfderiv IX 𝓘(ℝ,E) incX x)) :=
    hl.symm.trans (heq.mfderiv_eq.trans hr)
  change (mfderiv IY 𝓘(ℝ,E) incY (projMap x)).comp (mfderiv IX IY projMap x) =
    Jout.symm.toContinuousLinearMap.comp
      (V.comp (Jin.toContinuousLinearMap.comp (mfderiv IX 𝓘(ℝ,E) incX x)))
  ext v
  exact (Jout.symm_apply_apply _).symm.trans
    (congrArg Jout.symm (congrArg (fun A : TangentSpace IX x →L[ℝ] E ↦ A v) hder))
end HolomorphicAnosov

end

noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff _root_.Topology
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

/-- At a native plaque point, the physical metric projection preserves the original metric norm on
the given tangent distribution. -/
theorem native_physical_projection_norm_diagonal_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (q : Φ.family.centerDomain) (u : Fin d → ℝ)
    (hu : u ∈ Metric.ball 0 Φ.family.radius)
    (a b : M) (ha : a = (Φ.family.plaque q).param u)
    (hb : b = (Φ.family.plaque q).param u) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) Φ.family.receivingAnchor
    ∀ (hga : a ∈ tr.baseSet) (hgb : b ∈ tr.baseSet),
    let V := plaqueMetricProjection
      (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q u))
      (fderiv ℝ (H.coordinate q) u)
    ∀ v : Dist a,
      ‖(tr.continuousLinearEquivAt ℝ b hgb).symm
        (V ((tr.continuousLinearEquivAt ℝ a hga) v.val))‖ = ‖v‖ := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
  subst a
  subst b
  dsimp only
  intro hga hgb v
  have hdom : u ∈ (Φ.family.plaque q).domain := by rw [Φ.family.domain_eq]; exact hu
  have hP := ((Φ.family.plaque q).smooth u hdom).contMDiffAt
    ((Φ.family.plaque q).domain_open.mem_nhds hdom)
  have heq : H.coordinate q =ᶠ[𝓝 u]
      ((extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor) ∘ (Φ.family.plaque q).param) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hu] with w hw
    exact H.coordinate_eq q hw
  have hid := plaque_physical_projection_identity_g18 g Φ.family.receivingAnchor
    (Φ.family.plaque q).param u (hP.mdifferentiableAt (by simp))
    ((Φ.family.plaque q).immersed u hdom) (Φ.family.receiving_domain q u hu) v.val
    (by rw [(Φ.family.plaque q).tangent u hdom]; exact v.property)
  rw [H.coordinate_eq q hu, heq.fderiv_eq]
  exact congrArg norm hid

section NativeNearIsometry
variable (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
variable (s : ℕ)
local instance nativeTubeFrameTopologyG18 : TopologicalSpace
    (TotalSpace (Fin s → ℝ) (fun x : M ↦ ↥(Dist x))) :=
  TopologicalSpace.induced
    (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) inferInstance
variable (frame : Trivialization (Fin s → ℝ)
  (TotalSpace.proj (F := Fin s → ℝ) (E := fun x : M ↦ ↥(Dist x))))
variable [hframe : frame.IsLinear ℝ]
/-- The native inverse projection is locally near-isometric on the source tangent distribution near
a zero-normal diagonal in the original metric. -/
theorem native_physical_projection_nearisometry_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Q : TopologicalSpace.Opens Φ.family.centerDomain) (W : Set E)
    (e : Q → OpenPartialHomeomorph ((Fin d → ℝ) × K) E)
    (ht : ∀ q, (e q).target = W)
    (he : ∀ q, ContDiffOn ℝ 1 (e q).symm (e q).target)
    (hbase : ∀ q, ∀ z ∈ (e q).source, z.1 ∈ Metric.ball 0 Φ.family.radius)
    (hc : ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2) (univ ×ˢ W))
    (hd : ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W))
    {B : Type*} [TopologicalSpace B] (q : B → Q) (hq : Continuous q)
    (σ : B → frame.baseSet) (hσ : Continuous σ)
    (hσchart : ∀ t, (σ t).val ∈ (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).source)
    (hσtarget : ∀ t, extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor (σ t).val ∈ W)
    (τ : B → M)
    (hτformula : ∀ t, τ t = (Φ.family.plaque (q t).val).param
      ((e (q t)).symm (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor (σ t).val)).1)
    (V : B → E →L[ℝ] E)
    (hVformula : ∀ t, V t = fderiv ℝ
      (fun w ↦ H.coordinate (q t).val ((e (q t)).symm w).1)
      (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor (σ t).val))
    (t₀ : B) (hσ₀ : (σ t₀).val = (q t₀).val.val)
    (hinv₀ : (e (q t₀)).symm
      (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor (σ t₀).val) = 0)
    (hV₀ : V t₀ = plaqueMetricProjection
      (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate (q t₀).val 0))
      (fderiv ℝ (H.coordinate (q t₀).val) 0)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) Φ.family.receivingAnchor
    ∀ (hσtr : ∀ t, (σ t).val ∈ tr.baseSet) (hτtr : ∀ t, τ t ∈ tr.baseSet),
    let A : ∀ t : B, Dist (σ t).val →L[ℝ] TangentSpace 𝓘(ℝ,E) (τ t) := fun t ↦
      (tr.continuousLinearEquivAt ℝ (τ t) (hτtr t)).symm.toContinuousLinearMap.comp
        ((V t).comp ((tr.continuousLinearEquivAt ℝ (σ t).val (hσtr t)).toContinuousLinearMap.comp
          (Dist (σ t).val).subtypeL))
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 t₀, ∀ v : Dist (σ t).val,
      (1-ε)*‖v‖ ≤ ‖A t v‖ ∧ ‖A t v‖ ≤ (1+ε)*‖v‖ := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
  dsimp only
  intro hσtr hτtr ε hε
  let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
  let coords : B → Q × E := fun t ↦ (q t,ca (σ t).val)
  have hcoords : Continuous coords := hq.prodMk
    ((continuousOn_extChartAt (I := 𝓘(ℝ,E)) Φ.family.receivingAnchor).comp_continuous
      (continuous_subtype_val.comp hσ) hσchart)
  have hmaps : ∀ t, coords t ∈ univ ×ˢ W := fun t ↦ ⟨mem_univ _,hσtarget t⟩
  have hinv : Continuous (fun t ↦ (e (q t)).symm (ca (σ t).val)) :=
    hc.comp_continuous hcoords hmaps
  have hu : ∀ t, ((e (q t)).symm (ca (σ t).val)).1 ∈ Metric.ball 0 Φ.family.radius := by
    intro t
    exact hbase (q t) _ ((e (q t)).map_target (by rw [ht]; exact hσtarget t))
  have hτ : Continuous τ :=
    (Φ.family.jointly_continuous.comp
      ((continuous_subtype_val.comp hq).prodMk (hinv.fst.subtype_mk hu))).congr
        (fun t ↦ (hτformula t).symm)
  have hV : Continuous V :=
    ((native_inverse_projection_derivative_continuous_g18 H Q W e ht he hbase hc hd).comp_continuous
      hcoords hmaps).congr (fun t ↦ (hVformula t).symm)
  apply physical_frame_nearisometry_g18 Dist g frame hframe Φ.family.receivingAnchor
    σ hσ τ hτ hσtr hτtr V hV t₀ ?_ ε hε
  intro v
  dsimp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Submodule.subtypeL_apply]
  rw [hV₀]
  have hzero : (0 : Fin d → ℝ) ∈ Metric.ball 0 Φ.family.radius :=
    Metric.mem_ball_self Φ.family.radius_pos
  have hsource : (σ t₀).val = (Φ.family.plaque (q t₀).val).param 0 :=
    hσ₀.trans (Φ.family.plaque (q t₀).val).centered.symm
  have htarget : τ t₀ = (Φ.family.plaque (q t₀).val).param 0 := by
    rw [hτformula, hinv₀]
    rfl
  exact native_physical_projection_norm_diagonal_g18 H g (q t₀).val 0 hzero
    (σ t₀).val (τ t₀) hsource htarget _ _ v

/-- The native projection is near-isometric in the original metric on a common ambient open
neighborhood for center labels and source points. -/
theorem native_physical_projection_open_nearisometry_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Q : TopologicalSpace.Opens Φ.family.centerDomain) (W : Set E) (hW : IsOpen W)
    (e : Q → OpenPartialHomeomorph ((Fin d → ℝ) × K) E)
    (ht : ∀ q, (e q).target = W)
    (he : ∀ q, ContDiffOn ℝ 1 (e q).symm (e q).target)
    (hbase : ∀ q, ∀ z ∈ (e q).source, z.1 ∈ Metric.ball 0 Φ.family.radius)
    (hc : ContinuousOn (fun z : Q × E ↦ (e z.1).symm z.2) (univ ×ˢ W))
    (hd : ContinuousOn (fun z : Q × E ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W))
    (q₀ : Q) (hpframe : q₀.val.val ∈ frame.baseSet)
    (hpchart : q₀.val.val ∈ (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).source)
    (hptarget : extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor q₀.val.val ∈ W)
    (hinv₀ : (e q₀).symm (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor q₀.val.val) = 0)
    (hderiv₀ : HasFDerivAt (fun w ↦ H.coordinate q₀.val ((e q₀).symm w).1)
      (plaqueMetricProjection
        (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q₀.val 0))
        (fderiv ℝ (H.coordinate q₀.val) 0))
      (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor q₀.val.val))
    (ε : ℝ) (hε : 0 < ε) :
    let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) Φ.family.receivingAnchor
    let τ : Q → M → M := fun q x ↦ (Φ.family.plaque q.val).param ((e q).symm (ca x)).1
    let V : Q → M → E →L[ℝ] E := fun q x ↦
      fderiv ℝ (fun w ↦ H.coordinate q.val ((e q).symm w).1) (ca x)
    ∃ A : Set M, IsOpen A ∧ q₀.val.val ∈ A ∧
      A ⊆ ca.source ∩ ca ⁻¹' W ∧
      ∀ q : Q, q.val.val ∈ A → ∀ x ∈ A,
        ∃ (hx : x ∈ tr.baseSet) (hy : τ q x ∈ tr.baseSet),
          ∀ v : Dist x,
            let av := (tr.continuousLinearEquivAt ℝ (τ q x) hy).symm
              (V q x ((tr.continuousLinearEquivAt ℝ x hx) v.val))
            (1-ε)*Real.sqrt (g.inner x v.val v.val) ≤
                Real.sqrt (g.inner (τ q x) av av) ∧
              Real.sqrt (g.inner (τ q x) av av) ≤
                (1+ε)*Real.sqrt (g.inner x v.val v.val) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x) := ⟨g.toRiemannianMetric⟩
  dsimp only
  let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) Φ.family.receivingAnchor
  let Ux : Set M := frame.baseSet ∩ (ca.source ∩ ca ⁻¹' W)
  have hUx : IsOpen Ux := frame.open_baseSet.inter
    ((continuousOn_extChartAt (I := 𝓘(ℝ,E)) Φ.family.receivingAnchor).isOpen_inter_preimage
      (isOpen_extChartAt_source _) hW)
  let Ω : Set (Q × M) := univ ×ˢ Ux
  have hΩ : IsOpen Ω := isOpen_univ.prod hUx
  let t₀ : Ω := ⟨(q₀,q₀.val.val),mem_univ _,hpframe,hpchart,hptarget⟩
  let q : Ω → Q := fun t ↦ t.val.1
  let σ : Ω → frame.baseSet := fun t ↦ ⟨t.val.2,t.property.2.1⟩
  let τ : Ω → M := fun t ↦
    (Φ.family.plaque (q t).val).param ((e (q t)).symm (ca (σ t).val)).1
  let V : Ω → E →L[ℝ] E := fun t ↦
    fderiv ℝ (fun w ↦ H.coordinate (q t).val ((e (q t)).symm w).1) (ca (σ t).val)
  have hq : Continuous q := continuous_fst.comp continuous_subtype_val
  have hσ : Continuous σ := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hσchart : ∀ t : Ω, (σ t).val ∈ ca.source := fun t ↦ t.property.2.2.1
  have hσtarget : ∀ t : Ω, ca (σ t).val ∈ W := fun t ↦ t.property.2.2.2
  have hσtr : ∀ t : Ω, (σ t).val ∈ tr.baseSet := by
    intro t
    simpa only [tr,ca,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hσchart t
  have hτtr : ∀ t : Ω, τ t ∈ tr.baseSet := by
    intro t
    have hu := hbase (q t) _ ((e (q t)).map_target (by rw [ht]; exact hσtarget t))
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      Φ.family.receiving_domain (q t).val _ hu
  have hnear := native_physical_projection_nearisometry_g18 g s frame H Q W e
    ht he hbase hc hd q hq σ hσ hσchart hσtarget τ (fun _ ↦ rfl) V (fun _ ↦ rfl)
    t₀ rfl hinv₀ hderiv₀.fderiv hσtr hτtr ε hε
  obtain ⟨T,hpoint,hTopen,ht₀⟩ := eventually_nhds_iff.mp hnear
  let τQ : Q → M → M := fun q x ↦ (Φ.family.plaque q.val).param ((e q).symm (ca x)).1
  let VQ : Q → M → E →L[ℝ] E := fun q x ↦
    fderiv ℝ (fun w ↦ H.coordinate q.val ((e q).symm w).1) (ca x)
  let result : Q × M → Prop := fun z ↦
    ∃ (hx : z.2 ∈ tr.baseSet) (hy : τQ z.1 z.2 ∈ tr.baseSet),
      ∀ v : Dist z.2,
        let av := (tr.continuousLinearEquivAt ℝ (τQ z.1 z.2) hy).symm
          (VQ z.1 z.2 ((tr.continuousLinearEquivAt ℝ z.2 hx) v.val))
        (1-ε)*Real.sqrt (g.inner z.2 v.val v.val) ≤
            Real.sqrt (g.inner (τQ z.1 z.2) av av) ∧
          Real.sqrt (g.inner (τQ z.1 z.2) av av) ≤
            (1+ε)*Real.sqrt (g.inner z.2 v.val v.val)
  have hresult (t : Ω) (htT : t ∈ T) : result t.val := by
    refine ⟨hσtr t,hτtr t,?_⟩
    intro v
    have hv := hpoint t htT v
    change (1-ε)*‖v.val‖ ≤ _ ∧ _ ≤ (1+ε)*‖v.val‖ at hv
    dsimp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Submodule.subtypeL_apply] at hv
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner] at hv
    exact hv
  have himage : IsOpen ((Subtype.val : Ω → Q × M) '' T) :=
    hΩ.isOpenEmbedding_subtypeVal.isOpenMap _ hTopen
  have hnhds : (Subtype.val : Ω → Q × M) '' T ∈ 𝓝 (q₀,q₀.val.val) :=
    himage.mem_nhds ⟨t₀,ht₀,rfl⟩
  have hresultNear : ∀ᶠ z : Q × M in 𝓝 (q₀,q₀.val.val), result z := by
    filter_upwards [hnhds] with z hz
    obtain ⟨t,htT,heq⟩ := hz
    exact heq ▸ hresult t htT
  obtain ⟨A,hA,hp,hAG,hcontrol⟩ := open_label_relation_localization_g18
    (fun q : Q ↦ q.val.val)
    (Φ.family.centerDomain_open.isOpenEmbedding_subtypeVal.comp
      Q.isOpen.isOpenEmbedding_subtypeVal) q₀ (fun q x ↦ result (q,x)) hresultNear
    Ux hUx ⟨hpframe,hpchart,hptarget⟩
  exact ⟨A,hA,hp,(fun _ hx ↦ (hAG hx).2),hcontrol⟩

end NativeNearIsometry
end HolomorphicAnosov.HPS

end

noncomputable section
open scoped Manifold ContDiff
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
/-- An identity between physical and intrinsic derivatives transfers original-metric bounds to the
intrinsic pullback Hermitian norm. -/
theorem intrinsic_nearisometry_of_physical_g18
    {rx ry d : ℕ} {X Y M : Type*}
    [TopologicalSpace X] [ChartedSpace (Fin rx → ℝ) X]
    [TopologicalSpace Y] [ChartedSpace (Fin ry → ℝ) Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (incX : X → M) (incY : Y → M) (p : X → Y) (x : X)
    (h : HermitianTangentMetricCore d M)
    (g : ∀ z : M, TangentSpace (realModel d) z →L[ℝ]
      TangentSpace (realModel d) z →L[ℝ] ℝ)
    (hg : ∀ z v w, g z v w = hermitianTangentRealPairing h z v w)
    (A : TangentSpace (realModel d) (incX x) →L[ℝ]
      TangentSpace (realModel d) (incY (p x)))
    (hA : ∀ v, A (mfderiv 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x v) =
      mfderiv 𝓘(ℝ,Fin ry → ℝ) (realModel d) incY (p x)
        (mfderiv 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) p x v))
    (ε : ℝ)
    (hbound : ∀ w ∈ (mfderiv 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x).range,
      (1-ε)*Real.sqrt (g (incX x) w w) ≤
          Real.sqrt (g (incY (p x)) (A w) (A w)) ∧
        Real.sqrt (g (incY (p x)) (A w) (A w)) ≤
          (1+ε)*Real.sqrt (g (incX x) w w))
    (v : TangentSpace 𝓘(ℝ,Fin rx → ℝ) x) :
    (1-ε)*leafPullbackHermitianNorm incX h x v ≤
        leafPullbackHermitianNorm incY h (p x)
          (mfderiv 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) p x v) ∧
      leafPullbackHermitianNorm incY h (p x)
          (mfderiv 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) p x v) ≤
        (1+ε)*leafPullbackHermitianNorm incX h x v := by
  have hh := hbound (mfderiv 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x v) ⟨v,rfl⟩
  simpa only [hg,hA,leafPullbackHermitianNorm,leafPullbackHermitianPairing] using hh

end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped Manifold ContDiff
universe u
/-- The pullback Hermitian norm is zero exactly on the zero tangent vector when the inclusion
derivative is injective and the Hermitian form is positive definite. -/
theorem leafPullbackHermitianNorm_eq_zero_of_immersion_g18 {r d : ℕ} {L M : Type u} [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) (h : HermitianTangentMetricCore d M) (z : L)
    (v : TangentSpace 𝓘(ℝ,Fin r → ℝ) z)
    (hi : Function.Injective (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) inc z))
    (hv : leafPullbackHermitianNorm inc h z v = 0) : v = 0 := by
  let w := (complexTangentToReal d (inc z)).symm
    (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) inc z v)
  have hre : ((h (inc z)).inner w w).re = 0 :=
    (Real.sqrt_eq_zero ((h (inc z)).re_inner_nonneg w)).mp hv
  have him : ((h (inc z)).inner w w).im = 0 := by
    have hh := congrArg Complex.im ((h (inc z)).conj_inner_symm w w)
    simp only [Complex.conj_im] at hh
    linarith only [hh]
  have hw : w = 0 := (h (inc z)).definite w (Complex.ext hre him)
  apply hi
  have hh := congrArg (complexTangentToReal d (inc z)) hw
  simpa only [w,ContinuousLinearEquiv.apply_symm_apply,map_zero] using hh

end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped Manifold ContDiff
universe u
/-- The pullback Hermitian norm of the zero tangent vector is zero. -/
theorem leafPullbackHermitianNorm_zero_g18 {r d : ℕ} {L M : Type u} [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) (h : HermitianTangentMetricCore d M) (z : L) :
    leafPullbackHermitianNorm (r := r) inc h z 0 = 0 := by
  have hh := (h (inc z)).smul_left (0 : TangentSpace (complexModel d) (inc z)) 0 (0 : ℂ)
  simp only [zero_smul,map_zero,zero_mul] at hh
  simp only [leafPullbackHermitianNorm,leafPullbackHermitianPairing,
    hermitianTangentRealPairing,hermitianTangentPairing,map_zero,hh,Complex.zero_re,Real.sqrt_zero]

end HolomorphicAnosov

