import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Invertible differentials of admissible curve germs and their nonzero ambient tangents under
holomorphic immersions. (Ghys, §3 p.591) -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Filter
open scoped Manifold ContDiff Topology _root_.Topology

variable {L : Type*} [TopologicalSpace L] [ChartedSpace ℂ L]
  [IsManifold 𝓘(ℂ) ∞ L]

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- The differential at zero of a representative of an admissible curve parametrization germ is
bijective. (Ghys, §3 p.591) -/
theorem curveParamGerm_mfderiv_bijective (gamma : CurveParamGerm L) :
    Function.Bijective (mfderiv 𝓘(ℂ) 𝓘(ℂ) gamma.val.out 0) := by
  obtain ⟨e, he0, he, hei, heq⟩ := gamma.property
  have hevent : gamma.val.out =ᶠ[𝓝 (0 : ℂ)] e :=
    Germ.coe_eq.mp ((Quotient.out_eq gamma.val).trans heq.symm)
  have hd : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  rw [hevent.mfderiv_eq]
  exact (tangentSpaceCast 𝓘(ℂ) (e 0) (gamma.val.out 0)).bijective.comp
    (hd.mfderiv_bijective he0)

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- A holomorphic immersion sends the unit tangent of an admissible curve germ to a nonzero ambient
tangent vector. (Ghys, §3 p.591) -/
theorem curveParamGerm_immersion_tangent_ne_zero
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (f : L → M) (hf : ContMDiff 𝓘(ℂ) I ∞ f)
    (hinj : ∀ z, Function.Injective (mfderiv 𝓘(ℂ) I f z))
    (gamma : CurveParamGerm L) :
    mfderiv 𝓘(ℂ) I (fun z : ℂ ↦ f (gamma.val.out z)) 0
      ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1) ≠ 0 := by
  have hg := (curveParamGerm_mfderiv_bijective gamma).injective
  have hgd := mdifferentiableAt_of_mfderiv_injective hg
  have hcomp : Function.Injective
      (mfderiv 𝓘(ℂ) I (fun z : ℂ ↦ f (gamma.val.out z)) 0) := by
    change Function.Injective (mfderiv 𝓘(ℂ) I (f ∘ gamma.val.out) 0)
    rw [mfderiv_comp 0 (hf.mdifferentiable (by simp) _) hgd]
    exact (hinj _).comp hg
  intro hz
  have hz' := hcomp (hz.trans (map_zero _).symm)
  have hunit := congrArg (tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)) hz'
  simp at hunit

end HolomorphicAnosov.Ghys
