import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Coordinates
import HolomorphicAnosov.Geometry.CovariantDerivativeAlongCurveZero
import HolomorphicAnosov.Geometry.ConnectionTangentChartSmooth
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
Integral curves of the connection spray are tangent lifts of geodesics. (Andrews, Prop. 8.11.2,
p.84; Prop. 8.4.1, pp.74–75)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- On an open time domain, a smooth tangent-bundle curve is an integral curve of the connection
spray if and only if its projection is a geodesic and it equals the tangent lift of that
projection. (Andrews, Prop. 8.11.2, p.84) -/
theorem HasConnectionSprayCoordinates.isMIntegralCurveOn_iff
    (nabla : SmoothAffineConnection E M)
    {G : (z : TangentBundle 𝓘(ℝ, E) M) → TangentSpace (𝓘(ℝ, E)).tangent z}
    (hG : HasConnectionSprayCoordinates nabla G)
    (σ : ℝ → TangentBundle 𝓘(ℝ, E) M) (J : Set ℝ) (hJ : IsOpen J)
    (hσ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞ σ J) :
    IsMIntegralCurveOn (I := (𝓘(ℝ, E)).tangent) σ G J ↔
      IsConnectionGeodesicOn nabla (fun t ↦ (σ t).proj) J ∧
        EqOn σ (curveTangentLift (fun t ↦ (σ t).proj)) J := by
  let γ := fun t ↦ (σ t).proj
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ J :=
    (contMDiff_proj (TangentSpace 𝓘(ℝ, E))).comp_contMDiffOn hσ
  let c (t : ℝ) := chartAt E (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
  let hc (t : ℝ) := chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
  let q (t : ℝ) := connectionTangentChart (c t) ∘ σ
  let v (t : ℝ) := (q t t).2
  let A (t : ℝ) := connectionChristoffelBilinear nabla (Module.finBasis ℝ E)
    (c t) (hc t) (γ t) (v t) (v t)
  have hσd (t : ℝ) (ht : t ∈ J) :=
    (hσ.contMDiffAt (hJ.mem_nhds ht)).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hqd (t : ℝ) (ht : t ∈ J) : DifferentiableAt ℝ (q t) t :=
    ((connectionTangentChart_chartAt_contMDiffAt (σ t)).comp t
      (hσ.contMDiffAt (hJ.mem_nhds ht))).contDiffAt.differentiableAt (by simp)
  have hpair (t : ℝ) (ht : t ∈ J) :
      deriv (q t) t = (v t, -A t) ↔
        mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent σ t
          ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1) = G (σ t) := by
    have hd := mfderiv_comp_apply t
      ((connectionTangentChart_chartAt_contMDiffAt (σ t)).mdifferentiableAt (by simp))
      (hσd t ht) ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)
    rw [mfderiv_eq_fderiv] at hd
    have hdModel := congrArg (tangentSpaceCastModel 𝓘(ℝ, E × E)
      (connectionTangentChart (c t) (σ t))) hd
    change deriv (q t) t = tangentSpaceCastModel 𝓘(ℝ, E × E) _
      (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart (c t)) (σ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent σ t
          ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1))) at hdModel
    have hg := hG (finrank ℝ E) (Module.finBasis ℝ E) (c t) (hc t) (σ t)
      (mem_chart_source E _)
    change tangentSpaceCastModel 𝓘(ℝ, E × E) _
      (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart (c t)) (σ t)
        (G (σ t))) = (v t, -A t) at hg
    rw [hdModel, ← hg]
    exact ((tangentSpaceCastModel 𝓘(ℝ, E × E) _).injective.comp
      (connectionTangentChart_chartAt_mfderiv_injective (σ t))).eq_iff
  have hint : IsMIntegralCurveOn (I := (𝓘(ℝ, E)).tangent) σ G J ↔
      ∀ t ∈ J, deriv (q t) t = (v t, -A t) := by
    constructor
    · intro h t ht
      apply (hpair t ht).mpr
      have hd := ((h t ht).hasMFDerivAt (hJ.mem_nhds ht)).mfderiv
      rw [hd]
      change (1 : ℝ) • G (σ t) = G (σ t)
      exact one_smul ℝ _
    · intro h t ht
      have hd : mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent σ t =
          (1 : ℝ →L[ℝ] ℝ).smulRight (G (σ t)) := by
        apply ContinuousLinearMap.ext_ring
        simpa using! (hpair t ht).mp (h t ht)
      rw [← hd]
      exact (hσd t ht).hasMFDerivAt.hasMFDerivWithinAt
  have hfst (t : ℝ) (ht : t ∈ J) :
      (deriv (q t) t).1 =
        alongCurveCoordinate (c t) γ (curveVelocity γ) t := by
    have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (chartAt E (γ t)) (γ t) :=
      contMDiffAt_of_mem_maximalAtlas
        (chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) (γ t))
        (mem_chart_source E (γ t))
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (connectionChartMap (c t)) (γ t) at hchart
    have hd := mfderiv_comp_apply t (hchart.mdifferentiableAt (by simp))
      ((hγ.contMDiffAt (hJ.mem_nhds ht)).mdifferentiableAt (by simp))
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)
    rw [mfderiv_eq_fderiv] at hd
    have hdModel := congrArg
      (tangentSpaceCastModel 𝓘(ℝ, E) (connectionChartMap (c t) (γ t))) hd
    change deriv (connectionChartMap (c t) ∘ γ) t =
      alongCurveCoordinate (c t) γ (curveVelocity γ) t at hdModel
    exact (hqd t ht).hasFDerivAt.fst.hasDerivAt.deriv.symm.trans hdModel
  have hlift (t : ℝ) (ht : t ∈ J) :
      (deriv (q t) t).1 = v t ↔ σ t = curveTangentLift γ t := by
    rw [hfst t ht]
    have hinj := (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (x := γ t) (y := γ t) (mem_extChartAt_source (γ t))).injective
    change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap (c t)) (γ t)) at hinj
    constructor
    · intro h
      have hv : curveVelocity γ t = (σ t).snd := hinj
        ((tangentSpaceCastModel 𝓘(ℝ, E) _).injective h)
      exact TotalSpace.ext rfl (heq_of_eq hv.symm)
    · intro h
      have hv : (σ t).snd = curveVelocity γ t := by
        have hh := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦
          tangentSpaceCastModel 𝓘(ℝ, E) z.proj z.snd) h
        exact (tangentSpaceCastModel 𝓘(ℝ, E) (γ t)).injective hh
      change alongCurveCoordinate (c t) γ (curveVelocity γ) t =
        tangentSpaceCastModel 𝓘(ℝ, E) _
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap (c t)) (γ t) (σ t).snd)
      rw [hv]
      rfl
  have hacc (hl : EqOn σ (curveTangentLift γ) J) (t : ℝ) (ht : t ∈ J) :
      covariantDerivativeAlongCurve nabla γ (curveVelocity γ) t = 0 ↔
        (deriv (q t) t).2 = -A t := by
    rw [covariantDerivativeAlongCurve_eq_zero_iff]
    have hvel : alongCurveCoordinate (c t) γ (curveVelocity γ) =ᶠ[𝓝 t]
        (fun s ↦ (q t s).2) := by
      filter_upwards [hJ.mem_nhds ht] with s hs
      have h := congrArg (connectionTangentChart (c t)) (hl hs)
      exact (congrArg Prod.snd h).symm
    have hbase : deriv (connectionChartMap (c t) ∘ γ) t = v t := by
      exact (hqd t ht).hasFDerivAt.fst.hasDerivAt.deriv.trans
        ((hfst t ht).trans hvel.eq_of_nhds)
    change deriv (alongCurveCoordinate (c t) γ (curveVelocity γ)) t +
      connectionChristoffelBilinear nabla (Module.finBasis ℝ E) (c t) (hc t)
        (γ t) (deriv (connectionChartMap (c t) ∘ γ) t)
        (alongCurveCoordinate (c t) γ (curveVelocity γ) t) = 0 ↔ _
    rw [hvel.deriv_eq, (hqd t ht).hasFDerivAt.snd.hasDerivAt.deriv, hbase, hvel.eq_of_nhds]
    exact add_eq_zero_iff_eq_neg
  rw [hint]
  constructor
  · intro h
    have hl : EqOn σ (curveTangentLift γ) J := fun t ht ↦
      (hlift t ht).mp (congrArg Prod.fst (h t ht))
    exact ⟨⟨hγ, fun t ht ↦ (hacc hl t ht).mpr (congrArg Prod.snd (h t ht))⟩, hl⟩
  · rintro ⟨hgeod, hl⟩ t ht
    exact Prod.ext ((hlift t ht).mpr (hl ht)) ((hacc hl t ht).mp (hgeod.2 t ht))

end
end HolomorphicAnosov

