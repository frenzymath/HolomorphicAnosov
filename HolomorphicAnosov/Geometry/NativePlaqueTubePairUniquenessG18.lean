import HolomorphicAnosov.Geometry.PlaquePhysicalNormalG18
import HolomorphicAnosov.Geometry.NativePlaqueMetricTubeG18

noncomputable section
open Set Metric
open scoped _root_.Topology
namespace HolomorphicAnosov

/-- Equal images in a normal tube injective on a closed plaque ball times an open normal ball have
equal plaque coordinates. (HPS, proof of (6.1), pp. 94–95) -/
theorem native_plaque_tube_equal_base_g18
    {V K M : Type*} [PseudoMetricSpace V] [PseudoMetricSpace K] [Zero V] [Zero K]
    (ρ ε : ℝ) (F : V × K → M)
    (hF : InjOn F (Metric.closedBall 0 ρ ×ˢ Metric.ball 0 ε))
    {u v : V} {k l : K}
    (hu : u ∈ Metric.closedBall 0 ρ) (hv : v ∈ Metric.closedBall 0 ρ)
    (hk : k ∈ Metric.ball 0 ε) (hl : l ∈ Metric.ball 0 ε)
    (he : F (u,k) = F (v,l)) : u = v := by
  exact congrArg Prod.fst (hF ⟨hu,hk⟩ ⟨hv,hl⟩ he)

/-- Two pairs satisfying the plaque and normal coefficient bounds have equal plaque coordinates if
their images in an injective tube agree. -/
theorem native_plaque_tube_unique_of_pair_bounds_g18
    {U K X : Type*} [NormedAddCommGroup U] [NormedAddCommGroup K]
    (ρ ε C : ℝ) (F : U × K → X)
    (hF : InjOn F (Metric.closedBall 0 ρ ×ˢ Metric.ball 0 ε))
    (hC : 0 < C)
    {u v : U} (hu : u ∈ Metric.closedBall 0 ρ) (hv : v ∈ Metric.closedBall 0 ρ)
    {xu xv : X} {su sv : ℝ}
    (hxu : ∃ k : K, F (u,k) = xu ∧ ‖k‖ ≤ C * su)
    (hxv : ∃ l : K, F (v,l) = xv ∧ ‖l‖ ≤ C * sv)
    (hsu : su < ε / C) (hsv : sv < ε / C) (he : xu = xv) : u = v := by
  obtain ⟨k,hk,hkn⟩ := hxu
  obtain ⟨l,hl,hln⟩ := hxv
  have hks : k ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hkn.trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hC).mp hsu)
  have hls : l ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hln.trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hC).mp hsv)
  exact congrArg Prod.fst (hF ⟨hu,hks⟩ ⟨hv,hls⟩ (hk.trans (he.trans hl.symm)))

end HolomorphicAnosov


open Bundle
open scoped Manifold ContDiff
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

omit [FiniteDimensional ℝ E] in
/-- Every physical normal vector has a coefficient in the native normal frame satisfying the
supplied quantitative bound. (HPS, proof of (6.1), pp. 94–95) -/
theorem native_physical_normal_coefficient_g18 [T2Space M]
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ q : Φ.family.centerDomain) (u : Fin d → ℝ)
    (hu : u ∈ Metric.ball 0 Φ.family.radius)
    (ν : TangentSpace 𝓘(ℝ,E) ((Φ.family.plaque q).param u))
    (hν : ∀ v ∈ Dist ((Φ.family.plaque q).param u),
      g.inner ((Φ.family.plaque q).param u) ν v = 0)
    (C : ℝ) :
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    let ct := extChartAt 𝓘(ℝ,E).tangent
      (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
    (∀ w : E, (∀ v, b (q,u) w (D (q,u) v) = 0) →
      ∃ k : K, N (q,u) k = w ∧ ‖k‖ ≤ C * Real.sqrt (b (q,u) w w)) →
    ∃ k : K,
      ct.symm (H.coordinate q u,N (q,u) k) =
        (⟨(Φ.family.plaque q).param u,ν⟩ : TangentBundle 𝓘(ℝ,E) M) ∧
      ‖k‖ ≤ C * Real.sqrt (g.inner ((Φ.family.plaque q).param u) ν ν) := by
  dsimp only
  intro hcoeff
  let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
  let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
    originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
  let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
  let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
  let ca := extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
  let ct := extChartAt 𝓘(ℝ,E).tangent
    (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
  let P := Φ.family.plaque q
  have huP : u ∈ P.domain := by rw [Φ.family.domain_eq]; exact hu
  have hx := Φ.family.receiving_domain q u hu
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) Φ.family.receivingAnchor
  have hx' : P.param u ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  let J := tr.continuousLinearEquivAt ℝ (P.param u) hx'
  have heq : H.coordinate q =ᶠ[𝓝 u] (ca ∘ P.param) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hu] with v hv
    exact H.coordinate_eq q hv
  have hD : D (q,u) = fderiv ℝ (ca ∘ P.param) u := heq.fderiv_eq
  have hb : b (q,u) = originalMetricChartTensor_g18 g Φ.family.receivingAnchor
      (ca (P.param u)) := by
    change originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q u) = _
    rw [H.coordinate_eq q hu]
  have hν' : ∀ v ∈ (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) P.param u).range,
      g.inner (P.param u) ν v = 0 := by
    rw [P.tangent u huP]
    exact hν
  have hn := plaque_physical_to_coordinate_normal_g18 g Φ.family.receivingAnchor P.param u
    (((P.smooth u huP).contMDiffAt (P.domain_open.mem_nhds huP)).mdifferentiableAt (by simp))
    hx ν hν'
  have hnormal : ∀ v, b (q,u) (J ν) (D (q,u) v) = 0 := by
    rw [hD,hb]
    exact hn.1
  have hmetric : b (q,u) (J ν) (J ν) = g.inner (P.param u) ν ν := by
    rw [hb]
    exact hn.2
  obtain ⟨k,hN,hbound⟩ := hcoeff (J ν) hnormal
  refine ⟨k,?_,?_⟩
  · change ct.symm (H.coordinate q u,N (q,u) k) = _
    rw [H.coordinate_eq q hu]
    change ct.symm (ca (P.param u),N (q,u) k) = _
    rw [hN,extChartAt_tangent_symm_fibre_g18 Φ.family.receivingAnchor (P.param u) hx]
    change (⟨P.param u,J.symm (J ν)⟩ : TangentBundle 𝓘(ℝ,E) M) = _
    rw [J.symm_apply_apply]
  · change ‖k‖ ≤ C * Real.sqrt (b (q,u) (J ν) (J ν)) at hbound
    simpa only [hmetric] using hbound
/-- Sufficiently small normal vectors in the original metric with equal exponential endpoints in a
fixed native plaque tube have equal plaque base coordinates. (HPS, proof of (6.1), pp. 94–95) -/
theorem native_physical_normal_uniqueness_g18 [T2Space M]
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ q : Φ.family.centerDomain) (ρ ε C : ℝ) (hC : 0 < C) :
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    let ct := extChartAt 𝓘(ℝ,E).tangent
      (⟨Φ.family.receivingAnchor,0⟩ : TangentBundle 𝓘(ℝ,E) M)
    let T := fun z : (Fin d → ℝ) × K ↦
      riemannianExponential g (ct.symm (H.coordinate q z.1,N (q,z.1) z.2))
    InjOn T (Metric.closedBall 0 ρ ×ˢ Metric.ball 0 ε) →
    ∀ u v : Fin d → ℝ,
      u ∈ Metric.ball 0 Φ.family.radius → v ∈ Metric.ball 0 Φ.family.radius →
      u ∈ Metric.closedBall 0 ρ → v ∈ Metric.closedBall 0 ρ →
      (∀ w : E, (∀ t, b (q,u) w (D (q,u) t) = 0) →
        ∃ k : K, N (q,u) k = w ∧ ‖k‖ ≤ C * Real.sqrt (b (q,u) w w)) →
      (∀ w : E, (∀ t, b (q,v) w (D (q,v) t) = 0) →
        ∃ k : K, N (q,v) k = w ∧ ‖k‖ ≤ C * Real.sqrt (b (q,v) w w)) →
      ∀ (ν : TangentSpace 𝓘(ℝ,E) ((Φ.family.plaque q).param u))
        (μ : TangentSpace 𝓘(ℝ,E) ((Φ.family.plaque q).param v)),
      (∀ w ∈ Dist ((Φ.family.plaque q).param u), g.inner ((Φ.family.plaque q).param u) ν w = 0) →
      (∀ w ∈ Dist ((Φ.family.plaque q).param v), g.inner ((Φ.family.plaque q).param v) μ w = 0) →
      Real.sqrt (g.inner ((Φ.family.plaque q).param u) ν ν) < ε / C →
      Real.sqrt (g.inner ((Φ.family.plaque q).param v) μ μ) < ε / C →
      riemannianExponential g (⟨(Φ.family.plaque q).param u,ν⟩ : TangentBundle 𝓘(ℝ,E) M) =
        riemannianExponential g (⟨(Φ.family.plaque q).param v,μ⟩ : TangentBundle 𝓘(ℝ,E) M) → u = v := by
  dsimp only
  intro hT u v hu hv huR hvR hcu hcv ν μ hν hμ hνs hμs he
  obtain ⟨ku,hku,hkun⟩ := native_physical_normal_coefficient_g18 H g p₀ q u hu ν hν C hcu
  obtain ⟨kv,hkv,hkvn⟩ := native_physical_normal_coefficient_g18 H g p₀ q v hv μ hμ C hcv
  apply native_plaque_tube_unique_of_pair_bounds_g18 ρ ε C _ hT hC huR hvR
    (xu := riemannianExponential g (⟨(Φ.family.plaque q).param u,ν⟩ : TangentBundle 𝓘(ℝ,E) M))
    (xv := riemannianExponential g (⟨(Φ.family.plaque q).param v,μ⟩ : TangentBundle 𝓘(ℝ,E) M))
    (su := Real.sqrt (g.inner ((Φ.family.plaque q).param u) ν ν))
    (sv := Real.sqrt (g.inner ((Φ.family.plaque q).param v) μ μ))
    ⟨ku,congrArg (riemannianExponential g) hku,hkun⟩
    ⟨kv,congrArg (riemannianExponential g) hkv,hkvn⟩ hνs hμs he
end HolomorphicAnosov.HPS
