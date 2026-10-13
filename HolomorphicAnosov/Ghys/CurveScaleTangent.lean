import HolomorphicAnosov.Ghys.CurveContactTangent
import HolomorphicAnosov.Ghys.CurveGermReparametrizeAdmissible

/-! Source scaling multiplies the ambient tangent of a curve germ. (Ghys, §3 p.591) -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov.Ghys
open Filter Bundle
open scoped ContDiff Manifold _root_.Topology
variable {L : Type*} [TopologicalSpace L] [ChartedSpace ℂ L]
  [IsManifold 𝓘(ℂ) ∞ L]

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- Source scaling by `omega` multiplies the ambient tangent of an admissible parametrization by
`omega`. (Ghys, §3 p.591) -/
theorem curveParamGerm_scale_ambient_tangent
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (f : L → M) (hf : ContMDiff 𝓘(ℂ) I ∞ f)
    (γ : CurveParamGerm L) (omega : ℂˣ) :
    let δ := curveParamGermReparametrize L (.scale omega) γ
    (⟨f (δ.val.out 0), mfderiv 𝓘(ℂ) I (f ∘ δ.val.out) 0
      ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩ : TangentBundle I M) =
    ⟨f (γ.val.out 0), (omega : ℂ) • mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0
      ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩ := by
  dsimp only
  let δ := curveParamGermReparametrize L (.scale omega) γ
  let r : ℂ → ℂ := fun z ↦ (omega : ℂ) * z
  have hcomp : δ.val = ((γ.val.out ∘ r : ℂ → L) : CurveGerm L) := by
    change γ.val.compTendsto (CurveJetReparametrization.scale omega).apply
      (CurveJetReparametrization.scale omega).tendsto_zero = _
    conv_lhs => rw [← Quotient.out_eq γ.val]
    erw [Germ.coe_compTendsto]
    congr 1
    funext z
    simp [r, CurveJetReparametrization.scale, CurveJetReparametrization.apply]
  have hevent : δ.val.out =ᶠ[𝓝 (0 : ℂ)] γ.val.out ∘ r :=
    Germ.coe_eq.mp ((Quotient.out_eq δ.val).trans hcomp)
  have hamb : f ∘ δ.val.out =ᶠ[𝓝 (0 : ℂ)] (f ∘ γ.val.out) ∘ r :=
    hevent.fun_comp f
  have hb : f (δ.val.out 0) = f (γ.val.out 0) := by
    simpa [r] using hamb.eq_of_nhds
  have hg := mdifferentiableAt_of_mfderiv_injective
    (curveParamGerm_mfderiv_bijective γ).injective
  have hr : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) r 0 := by
    exact ((hasDerivAt_id (0 : ℂ)).const_mul (omega : ℂ)).differentiableAt.mdifferentiableAt
  have hv : @Eq E
      (mfderiv 𝓘(ℂ) I (f ∘ δ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1))
      ((omega : ℂ) • mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)) := by
    rw [hamb.mfderiv_eq]
    have hfg : MDifferentiableAt 𝓘(ℂ) I (f ∘ γ.val.out) (r 0) := by
      simpa [r] using (hf.mdifferentiable (by simp) _).comp 0 hg
    rw [mfderiv_comp 0 hfg hr, ContinuousLinearMap.comp_apply]
    dsimp only [tangentSpaceCast, tangentSpaceCastModel, ContinuousLinearEquiv.coe_coe, r]
    erw [mul_zero]
    change mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) r 0 (1 : ℂ)) =
        (omega : ℂ) • mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0 (1 : ℂ)
    rw [mfderiv_eq_fderiv]
    have hd : fderiv ℂ r 0 (1 : ℂ) = (omega : ℂ) := by
      rw [fderiv_apply_one_eq_deriv]
      simp [r]
    erw [hd]
    simpa only [smul_eq_mul, mul_one] using
      (mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0).map_smul (omega : ℂ) (1 : ℂ)
  exact TotalSpace.ext hb (heq_of_eq hv)

end HolomorphicAnosov.Ghys
