import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Ghys.CurveParamGermTangent
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! Holomorphic curve tangency in a native real immersed leaf (Ghys, §2) -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold _root_.Topology
open Filter
universe u
variable {d : ℕ} {M L : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
  [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ L]
  [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
attribute [local instance] complex_isManifold_real

omit [IsManifold (complexModel d) ∞ M] [IsManifold 𝓘(ℂ, ℂ) ∞ L] in
/-- The complex tangent of an admissible curve in a native real leaf belongs to its chosen complex tangent line. (Ghys, §2–3) -/
theorem native_holomorphic_curve_tangent_mem
    {D : RealTangentDistribution (realModel d) M}
    (hRank : HasComplexRankOne D) (N : HPS.NativeLeaf (r := 2) D L)
    (hhol : ContMDiff 𝓘(ℂ) (complexModel d) ∞ N.inclusion)
    (gamma : CurveParamGerm L) (v : TangentSpace 𝓘(ℂ) (0 : ℂ)) :
    mfderiv 𝓘(ℂ) (complexModel d) (N.inclusion ∘ gamma.val.out) 0 v ∈
      (hRank (N.inclusion (gamma.val.out 0))).choose := by
  obtain ⟨e, he0, he, hei, heq⟩ := gamma.property
  have hevent : gamma.val.out =ᶠ[𝓝 (0 : ℂ)] e :=
    Germ.coe_eq.mp ((Quotient.out_eq gamma.val).trans heq.symm)
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ gamma.val.out 0 :=
    (he.contMDiffAt (e.open_source.mem_nhds he0)).congr_of_eventuallyEq hevent
  have hc := hhol.contMDiffAt.comp 0 hg
  have hr : ContMDiffAt 𝓘(ℝ, ℂ) (realModel d) ∞
      (N.inclusion ∘ gamma.val.out) 0 := by
    obtain ⟨hcont, hsmooth⟩ := contMDiffAt_iff.mp hc
    exact contMDiffAt_iff.mpr ⟨hcont, hsmooth.restrict_scalars ℝ⟩
  have hgr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) ∞ gamma.val.out 0 :=
    (ContMDiffAt.iff_comp_isImmersionAt
      (N.immersion.isImmersionAt (gamma.val.out 0))).mpr ⟨hg.continuousAt, hr⟩
  let vr : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ) :=
    (tangentSpaceCastModel 𝓘(ℝ, ℂ) (0 : ℂ)).symm
      (tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ) v)
  have hreal : mfderiv 𝓘(ℝ, ℂ) (realModel d) (N.inclusion ∘ gamma.val.out) 0 vr =
      complexTangentToReal d (N.inclusion (gamma.val.out 0))
        (mfderiv 𝓘(ℂ) (complexModel d) (N.inclusion ∘ gamma.val.out) 0 v) := by
    have hcd := hc.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    have hrd := hr.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    have hd : DifferentiableAt ℂ
        (writtenInExtChartAt 𝓘(ℂ) (complexModel d) (0 : ℂ)
          (N.inclusion ∘ gamma.val.out)) 0 := by
      simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id,
        differentiableWithinAt_univ, extChartAt_self_apply, id_eq] using
        hcd.differentiableWithinAt_writtenInExtChartAt
    rw [hrd.mfderiv, hcd.mfderiv]
    simp only [realModel, complexModel, modelWithCornersSelf_coe, Set.range_id,
      fderivWithin_univ]
    change (fderiv ℝ (writtenInExtChartAt 𝓘(ℂ) (complexModel d) (0 : ℂ)
      (N.inclusion ∘ gamma.val.out)) 0) v =
      (fderiv ℂ (writtenInExtChartAt 𝓘(ℂ) (complexModel d) (0 : ℂ)
      (N.inclusion ∘ gamma.val.out)) 0) v
    exact congrArg (fun A ↦ A v) (hd.fderiv_restrictScalars (𝕜 := ℝ))
  have hmem : complexTangentToReal d (N.inclusion (gamma.val.out 0))
        (mfderiv 𝓘(ℂ) (complexModel d) (N.inclusion ∘ gamma.val.out) 0 v) ∈
      D (N.inclusion (gamma.val.out 0)) := by
    rw [← hreal, mfderiv_comp 0
      (N.immersion.contMDiff.mdifferentiable (by simp) _)
      (hgr.mdifferentiableAt (by simp)), ← N.tangent]
    exact ⟨mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℝ) gamma.val.out 0 vr, rfl⟩
  rw [← (hRank _).choose_spec.2] at hmem
  obtain ⟨w, hw, heq⟩ := hmem
  have hv := (complexTangentToReal d _).injective heq
  exact hv ▸ hw

end HolomorphicAnosov.Ghys
