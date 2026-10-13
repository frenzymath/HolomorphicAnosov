import HolomorphicAnosov.Geometry.ConnectionSpraySmooth
import HolomorphicAnosov.Geometry.ConnectionTangentChartTransitionLaw
import HolomorphicAnosov.Geometry.ConnectionTangentChartTransitionGerm
import HolomorphicAnosov.Geometry.ConnectionTangentChartSmooth
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Coordinates
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Transition
import HolomorphicAnosov.Geometry.ConnectionGeodesicSprayHelpers
import HolomorphicAnosov.Geometry.ConnectionSprayAllChartCompatibility
import HolomorphicAnosov.Geometry.ConnectionSprayCurves
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
Smooth geodesic sprays, covariant differentiation along curves, and time rescaling of geodesics.
(Andrews, pp.74–75, 83–85)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The covariant derivative of a smooth field along a smooth curve has the formula `z′ + Γ(x′, z)`
in every admissible chart containing the curve point. (Andrews, Prop. 8.4.1, pp.74–75) -/
theorem covariantDerivativeAlongCurve_coordinates
    (nabla : SmoothAffineConnection E M) {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (γ : ℝ → M) (Z : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (γ t))
    (J : Set ℝ) (hJ : IsOpen J)
    (_hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ J)
    (hZ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
      (fun t ↦ (⟨γ t, Z t⟩ : TangentBundle 𝓘(ℝ, E) M)) J)
    (t : ℝ) (ht : t ∈ J)
    (htc : (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M) ∈ c.source) :
    alongCurveCoordinate c γ (covariantDerivativeAlongCurve nabla γ Z) t =
      covariantDerivativeCoordinate nabla b c hc γ Z t := by
  let c₀ := chartAt E (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
  have hc₀ := chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
  have hp₀ : (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M) ∈ c₀.source :=
    mem_chart_source E _
  let h := connectionChartMap c ∘ connectionChartInverse c₀
  let x := connectionChartMap c₀ ∘ γ
  let z := alongCurveCoordinate c₀ γ Z
  let σ (s : ℝ) : TangentBundle 𝓘(ℝ, E) M := ⟨γ s, Z s⟩
  have hσ := hZ.contMDiffAt (hJ.mem_nhds ht)
  have hq : DifferentiableAt ℝ (fun s ↦ (x s, z s)) t :=
    ((connectionTangentChart_chartAt_contMDiffAt (σ t)).comp t hσ).contDiffAt.differentiableAt
      (by simp)
  have hx : HasDerivAt x (deriv x t) t := hq.fst.hasDerivAt
  have hz : HasDerivAt z (deriv z t) t := hq.snd.hasDerivAt
  have hh : ContDiffAt ℝ ∞ h (x t) := by
    have hinv := contMDiffAt_symm_of_mem_maximalAtlas hc₀ (c₀.map_source hp₀)
    have hout := contMDiffAt_of_mem_maximalAtlas hc htc
    exact (hout.comp_of_eq hinv (c₀.left_inv hp₀)).contDiffAt
  have hh₁ := hh.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hh₂ := (hh.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have heq₀ := connectionTangentChart_transition_eventuallyEq c₀ c hc₀ hc (σ t) hp₀ htc
  have heq := heq₀.comp_tendsto hσ.continuousAt
  have hx' : connectionChartMap c ∘ γ =ᶠ[𝓝 t] h ∘ x := by
    filter_upwards [heq] with s hs
    exact congrArg Prod.fst hs
  have hz' : alongCurveCoordinate c γ Z =ᶠ[𝓝 t]
      (fun s ↦ fderiv ℝ h (x s) (z s)) := by
    filter_upwards [heq] with s hs
    exact congrArg Prod.snd hs
  have hdx : deriv (connectionChartMap c ∘ γ) t = fderiv ℝ h (x t) (deriv x t) := by
    rw [hx'.deriv_eq]
    exact (hh₁.hasFDerivAt.comp_hasDerivAt t hx).deriv
  have hdz : deriv (alongCurveCoordinate c γ Z) t =
      fderiv ℝ (fderiv ℝ h) (x t) (deriv x t) (z t) +
        fderiv ℝ h (x t) (deriv z t) := by
    rw [hz'.deriv_eq]
    exact ((hh₂.hasFDerivAt.comp_hasDerivAt t hx).clm_apply hz).deriv
  have hΓ := connectionChristoffel_transition nabla (Module.finBasis ℝ E) b c₀ c hc₀ hc
    (γ t) hp₀ htc (deriv x t) (z t)
  change connectionChristoffelBilinear nabla b c hc (γ t)
      (fderiv ℝ h (x t) (deriv x t)) (fderiv ℝ h (x t) (z t)) =
    fderiv ℝ h (x t) (connectionChristoffelBilinear nabla (Module.finBasis ℝ E) c₀ hc₀
      (γ t) (deriv x t) (z t)) - fderiv ℝ (fderiv ℝ h) (x t) (deriv x t) (z t) at hΓ
  have hcov : covariantDerivativeCoordinate nabla b c hc γ Z t =
      fderiv ℝ h (x t)
        (covariantDerivativeCoordinate nabla (Module.finBasis ℝ E) c₀ hc₀ γ Z t) := by
    unfold covariantDerivativeCoordinate
    rw [hdz, hdx, hz'.eq_of_nhds, hΓ]
    change _ = fderiv ℝ h (x t)
      (deriv z t + connectionChristoffelBilinear nabla (Module.finBasis ℝ E) c₀ hc₀
        (γ t) (deriv x t) (z t))
    rw [map_add]
    abel
  have hcan : alongCurveCoordinate c₀ γ (covariantDerivativeAlongCurve nabla γ Z) t =
      covariantDerivativeCoordinate nabla (Module.finBasis ℝ E) c₀ hc₀ γ Z t := by
    have heqinv := (⊤ : Opens M).chartAt_subtype_val_symm_eventuallyEq
      (H := E) (x := (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M))
    change (chartAt E (γ t)).symm =ᶠ[𝓝 (connectionChartMap c₀ (γ t))]
      connectionChartInverse c₀ at heqinv
    have hd := heqinv.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    have hid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E (γ t)).symm
        (connectionChartMap c₀ (γ t)) = ContinuousLinearMap.id ℝ E := by
      simpa [c₀, connectionChartMap] using!
        (mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := γ t))
    have hdModel := congrArg (fun D ↦ (tangentSpaceCastModel 𝓘(ℝ, E)
      ((chartAt E (γ t)).symm (connectionChartMap c₀ (γ t)))).toContinuousLinearMap.comp D) hd
    simp only [hid] at hdModel
    change ContinuousLinearMap.id ℝ E = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartInverse c₀)
      (connectionChartMap c₀ (γ t)) at hdModel
    have hdchart : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c₀) (γ t) =
        ContinuousLinearMap.id ℝ E := by
      simpa [c₀, connectionChartMap] using! (mfderiv_extChartAt_self (I := 𝓘(ℝ, E)) (x := γ t))
    unfold alongCurveCoordinate covariantDerivativeAlongCurve
    change tangentSpaceCastModel 𝓘(ℝ, E) _
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c₀) (γ t)
        ((tangentSpaceCastModel 𝓘(ℝ, E) (γ t)).symm
          (tangentSpaceCastModel 𝓘(ℝ, E) _
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartInverse c₀)
              (connectionChartMap c₀ (γ t)) _)))) = _
    rw [hdchart, ← hdModel]
    rfl
  have hvector := congrArg Prod.snd (connectionTangentChart_transition c₀ c hc₀ hc
    (⟨γ t, covariantDerivativeAlongCurve nabla γ Z t⟩ : TangentBundle 𝓘(ℝ, E) M) hp₀ htc)
  change alongCurveCoordinate c γ (covariantDerivativeAlongCurve nabla γ Z) t =
    fderiv ℝ h (x t) (alongCurveCoordinate c₀ γ (covariantDerivativeAlongCurve nabla γ Z) t)
    at hvector
  rw [hvector, hcan]
  exact hcov.symm

/-- A smooth affine connection on a Hausdorff manifold determines a unique smooth geodesic spray,
vanishing on the zero section. Its smooth integral curves on open intervals are exactly tangent
lifts of geodesics. (Andrews, pp.74–75, 83–85) -/
theorem exists_connectionGeodesicSpray [T2Space M] (nabla : SmoothAffineConnection E M) :
    ∃ G : (z : TangentBundle 𝓘(ℝ, E) M) → TangentSpace (𝓘(ℝ, E)).tangent z,
      ContMDiff (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).tangent).tangent ∞
        (fun z ↦ (⟨z, G z⟩ : TangentBundle (𝓘(ℝ, E)).tangent
          (TangentBundle 𝓘(ℝ, E) M))) ∧
      HasConnectionSprayCoordinates nabla G ∧
      (∀ G', HasConnectionSprayCoordinates nabla G' → G' = G) ∧
      (∀ p : M, G ⟨p, 0⟩ = 0) ∧
      (∀ (J : Set ℝ), IsOpen J → OrdConnected J →
        ∀ c : ℝ → TangentBundle 𝓘(ℝ, E) M,
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞ c J →
          (IsMIntegralCurveOn (I := (𝓘(ℝ, E)).tangent) c G J ↔
            IsConnectionGeodesicOn nabla (fun t ↦ (c t).proj) J ∧
              EqOn c (curveTangentLift (fun t ↦ (c t).proj)) J)) := by
  let c (z : TangentBundle 𝓘(ℝ, E) M) :=
    chartAt E (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  let hc (z : TangentBundle 𝓘(ℝ, E) M) :=
    chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
      (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  let G (z : TangentBundle 𝓘(ℝ, E) M) : TangentSpace (𝓘(ℝ, E)).tangent z :=
    (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart (c z)) z).inverse
      ((tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart (c z) z)).symm
        ((connectionTangentChart (c z) z).2,
          -connectionChristoffelBilinear nabla (Module.finBasis ℝ E) (c z) (hc z)
            z.proj (connectionTangentChart (c z) z).2 (connectionTangentChart (c z) z).2))
  have hGcanonical (z : TangentBundle 𝓘(ℝ, E) M) :
      tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart (c z) z)
        (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart (c z)) z (G z)) =
      ((connectionTangentChart (c z) z).2,
        -connectionChristoffelBilinear nabla (Module.finBasis ℝ E) (c z) (hc z)
          z.proj (connectionTangentChart (c z) z).2 (connectionTangentChart (c z) z).2) := by
    dsimp only [G]
    rw [(connectionTangentChart_chartAt_mfderiv_isInvertible z).self_apply_inverse]
    exact (tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart (c z) z)).apply_symm_apply _
  have hGzero (p : M) : G ⟨p, 0⟩ = 0 := by
    let z : TangentBundle 𝓘(ℝ, E) M := ⟨p, 0⟩
    apply connectionTangentChart_chartAt_mfderiv_injective z
    apply (tangentSpaceCastModel 𝓘(ℝ, E × E)
      (connectionTangentChart (c z) z)).injective
    rw [hGcanonical]
    have hv : (connectionTangentChart (c z) z).2 = 0 := by
      simp [connectionTangentChart, z]
    rw [hv]
    simp [connectionChristoffelBilinear]
  suffices h :
      ContMDiff (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).tangent).tangent ∞
        (fun z ↦ (⟨z, G z⟩ : TangentBundle (𝓘(ℝ, E)).tangent
          (TangentBundle 𝓘(ℝ, E) M))) ∧
      HasConnectionSprayCoordinates nabla G ∧
      (∀ (J : Set ℝ), IsOpen J → OrdConnected J →
        ∀ c : ℝ → TangentBundle 𝓘(ℝ, E) M,
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞ c J →
          (IsMIntegralCurveOn (I := (𝓘(ℝ, E)).tangent) c G J ↔
            IsConnectionGeodesicOn nabla (fun t ↦ (c t).proj) J ∧
              EqOn c (curveTangentLift (fun t ↦ (c t).proj)) J)) by
    obtain ⟨hsmooth, hcoord, hcurve⟩ := h
    exact ⟨G, hsmooth, hcoord,
      fun _ hG' ↦ hasConnectionSprayCoordinates_unique nabla hcoord hG', hGzero, hcurve⟩
  have hcoord : HasConnectionSprayCoordinates nabla G := by
    intro n b c' hc' z hz
    exact connectionSprayVector_allChartCoordinates nabla z (G z) (by simpa using hGcanonical z) b c' hc' hz
  refine ⟨HasConnectionSprayCoordinates.contMDiff nabla hcoord, hcoord, ?_⟩
  intro J hJ hJconn cσ hcs
  exact HasConnectionSprayCoordinates.isMIntegralCurveOn_iff nabla hcoord cσ J hJ hcs

/-- The geodesic spray determined by a smooth affine connection. (Andrews, Prop. 8.11.2 and Ex.
8.11.3, p.84) -/
def connectionGeodesicSpray [T2Space M] (nabla : SmoothAffineConnection E M) :=
  Classical.choose (exists_connectionGeodesicSpray nabla)

/-- Time rescaling `s ↦ γ(a * s)` preserves geodesics on the full preimage domain. When the original
domain contains zero, the initial point is unchanged and the initial velocity is multiplied by
`a`. (Andrews, Prop. 8.11.4, p.85) -/
theorem connectionGeodesic_rescale (nabla : SmoothAffineConnection E M)
    (γ : ℝ → M) (J : Set ℝ) (hJ : IsOpen J) (_hJc : OrdConnected J)
    (hγ : IsConnectionGeodesicOn nabla γ J) (a : ℝ) :
    IsConnectionGeodesicOn nabla (fun s ↦ γ (a * s)) {s | a * s ∈ J} ∧
      (0 ∈ J → γ (a * 0) = γ 0 ∧
        curveVelocity (E := E) (fun s ↦ γ (a * s)) 0 = a • curveVelocity (E := E) γ 0) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ ↦ a * s) :=
    (contDiff_const.mul contDiff_id).contMDiff
  have hv (t : ℝ) (ht : a * t ∈ J) :
      curveVelocity (E := E) (fun s ↦ γ (a * s)) t = a • curveVelocity (E := E) γ (a * t) := by
    have hg := (hγ.1.contMDiffAt (hJ.mem_nhds ht)).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hm := (hs.contMDiffAt (x := t)).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    unfold curveVelocity
    rw [show (fun s ↦ γ (a * s)) = γ ∘ (fun s ↦ a * s) from rfl,
      mfderiv_comp t hg hm]
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (a * t))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s ↦ a * s) t)
        ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)) = _
    have hD : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s ↦ a * s) t)
        ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1) =
        a • (tangentSpaceCastModel 𝓘(ℝ, ℝ) (a * t)).symm 1 := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun s ↦ a * s) t 1 = a • (1 : ℝ)
      have hd : fderiv ℝ (fun s ↦ a * s) t =
          a • ContinuousLinearMap.id ℝ ℝ := by
        simpa using ((hasFDerivAt_id (𝕜 := ℝ) t).const_mul a).fderiv
      rw [hd]
      rfl
    rw [hD, map_smul]
  constructor
  · constructor
    · exact hγ.1.comp hs.contMDiffOn (fun _ ht ↦ ht)
    · intro t ht
      have hev (c : OpenPartialHomeomorph (ConnectionWhole M) E) :
          alongCurveCoordinate c (fun s ↦ γ (a * s))
              (curveVelocity (E := E) (fun s ↦ γ (a * s))) =ᶠ[𝓝 t]
            (fun s ↦ a • alongCurveCoordinate c γ (curveVelocity (E := E) γ) (a * s)) := by
        have hn : {s : ℝ | a * s ∈ J} ∈ 𝓝 t :=
          (hJ.preimage (continuous_const.mul continuous_id)).mem_nhds ht
        filter_upwards [hn] with s hs
        simp only [alongCurveCoordinate, hv s hs, map_smul]
      have hdcoord {n : ℕ} (b : Basis (Fin n) ℝ E)
          (c : OpenPartialHomeomorph (ConnectionWhole M) E)
          (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M)) :
          covariantDerivativeCoordinate nabla b c hc (fun s ↦ γ (a * s))
              (curveVelocity (E := E) (fun s ↦ γ (a * s))) t =
            (a * a) • covariantDerivativeCoordinate nabla b c hc γ
              (curveVelocity (E := E) γ) (a * t) := by
        unfold covariantDerivativeCoordinate
        rw [(hev c).deriv_eq, deriv_fun_const_smul_field, deriv_comp_mul_left]
        have hvcoord : alongCurveCoordinate c (fun s ↦ γ (a * s))
            (curveVelocity (E := E) (fun s ↦ γ (a * s))) t =
            a • alongCurveCoordinate c γ (curveVelocity (E := E) γ) (a * t) :=
          (hev c).eq_of_nhds
        rw [hvcoord]
        change a • a • deriv (alongCurveCoordinate c γ (curveVelocity (E := E) γ)) (a * t) +
          connectionChristoffelBilinear nabla b c hc (γ (a * t))
            (deriv (fun s ↦ (connectionChartMap c ∘ γ) (a * s)) t)
            (a • alongCurveCoordinate c γ (curveVelocity (E := E) γ) (a * t)) = _
        rw [deriv_comp_mul_left]
        simp only [connectionChristoffelBilinear_smul_smul, smul_smul, smul_add]
      unfold covariantDerivativeAlongCurve
      dsimp only
      rw [hdcoord]
      simp only [map_smul]
      have hh := hγ.2 (a * t) ht
      unfold covariantDerivativeAlongCurve at hh
      dsimp only at hh
      rw [hh, smul_zero]
  · intro h0
    refine ⟨by simp, ?_⟩
    have h := hv 0 (by simpa using h0)
    change (tangentSpaceCastModel 𝓘(ℝ, E) (γ (a * 0)))
      (curveVelocity (E := E) (fun s ↦ γ (a * s)) 0) =
      a • (tangentSpaceCastModel 𝓘(ℝ, E) (γ 0)) (curveVelocity (E := E) γ 0)
    have hh := congrArg (tangentSpaceCastModel 𝓘(ℝ, E) (γ (a * 0))) h
    simp only [map_smul] at hh
    convert hh using 1
    congr 1
    exact congrArg (fun x ↦ (tangentSpaceCastModel 𝓘(ℝ, E) (γ x))
      (curveVelocity (E := E) γ x)) (mul_zero a).symm


end
end HolomorphicAnosov


