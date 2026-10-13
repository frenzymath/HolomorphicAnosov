import HolomorphicAnosov.Ghys.CurveParamGermTangent
import HolomorphicAnosov.Ghys.CurveGermBaseCoe
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! First contact and ambient tangent vectors under holomorphic maps. (Ghys, §3 p.591; Michor,
§§1.3–1.6) -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open Filter Bundle
open scoped ContDiff Manifold _root_.Topology
universe u v
variable {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
  [IsManifold 𝓘(ℂ) ∞ L]

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- First-contact-equivalent parametrizations have the same ambient tangent after any holomorphic
map. (Ghys, §3 p.591; Michor, §§1.3–1.6) -/
theorem curveContact1_ambient_tangent_eq
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (f : L → M) (hf : ContMDiff 𝓘(ℂ) I ∞ f)
    (γ δ : CurveParamGerm L) (h : CurveContact1 L γ δ) :
    (⟨f (γ.val.out 0), mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0
      ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩ : TangentBundle I M) =
    ⟨f (δ.val.out 0), mfderiv 𝓘(ℂ) I (f ∘ δ.val.out) 0
      ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩ := by
  obtain ⟨hb, c, hc, ha⟩ := h
  have hbase (η : CurveParamGerm L) : curveGermBase L η.val = η.val.out 0 := by
    conv_lhs => rw [← Quotient.out_eq η.val]
    rfl
  have hb' : γ.val.out 0 = δ.val.out 0 := by
    rw [← hbase, ← hbase]
    exact hb
  have hcoef (η : CurveParamGerm L) :
      curveGermFirst L c η = deriv (c.val ∘ η.val.out) 0 := by
    change germFirst (η.val.map (c.val : L → ℂ)) = _
    conv_lhs => rw [← Quotient.out_eq η.val]
    rfl
  have hg (η : CurveParamGerm L) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) η.val.out 0 :=
    mdifferentiableAt_of_mfderiv_injective (curveParamGerm_mfderiv_bijective η).injective
  have hcγ : γ.val.out 0 ∈ c.val.source := hbase γ ▸ hc
  have hcδ : δ.val.out 0 ∈ c.val.source := hb' ▸ hcγ
  have hcD : c.val.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas c.property).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas c.property).mdifferentiableOn (by simp)⟩
  have hformula (η : CurveParamGerm L) (hη : η.val.out 0 ∈ c.val.source) :
      mfderiv 𝓘(ℂ) 𝓘(ℂ) c.val (η.val.out 0)
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) η.val.out 0
          ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)) =
        curveGermFirst L c η := by
    rw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp 0 (hcD.mdifferentiableAt hη) (hg η),
      hcoef, mfderiv_eq_fderiv]
    rfl
  have hv : @Eq ℂ
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) γ.val.out 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) δ.val.out 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)) := by
    apply hcD.mfderiv_injective hcγ
    rw [hformula γ hcγ, ha]
    rw [hb']
    exact (hformula δ hcδ).symm
  have hamb : @Eq E
      (mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1))
      (mfderiv 𝓘(ℂ) I (f ∘ δ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)) := by
    rw [mfderiv_comp 0 (hf.mdifferentiable (by simp) _) (hg γ),
      mfderiv_comp 0 (hf.mdifferentiable (by simp) _) (hg δ),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hv, hb']
  exact TotalSpace.ext (congrArg f hb') (heq_of_eq hamb)

/-- For an injective holomorphic immersion, first contact is equivalent to equality of ambient
tangent vectors. (Ghys, §3 p.591; Michor, §§1.3–1.6) -/
theorem curveContact1_iff_ambient_tangent_eq
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (f : L → M) (hf : ContMDiff 𝓘(ℂ) I ∞ f)
    (hf_inj : Function.Injective f)
    (hdf_inj : ∀ x, Function.Injective (mfderiv 𝓘(ℂ) I f x))
    (γ δ : CurveParamGerm L) :
    CurveContact1 L γ δ ↔
      (⟨f (γ.val.out 0), mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩ : TangentBundle I M) =
      ⟨f (δ.val.out 0), mfderiv 𝓘(ℂ) I (f ∘ δ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)⟩ := by
  refine ⟨curveContact1_ambient_tangent_eq I f hf γ δ, ?_⟩
  intro h
  have hb : γ.val.out 0 = δ.val.out 0 := hf_inj (congrArg TotalSpace.proj h)
  have hbase (η : CurveParamGerm L) : curveGermBase L η.val = η.val.out 0 := by
    conv_lhs => rw [← Quotient.out_eq η.val]
    rfl
  have hg (η : CurveParamGerm L) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) η.val.out 0 :=
    mdifferentiableAt_of_mfderiv_injective (curveParamGerm_mfderiv_bijective η).injective
  have hamb : @Eq E
      (mfderiv 𝓘(ℂ) I (f ∘ γ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1))
      (mfderiv 𝓘(ℂ) I (f ∘ δ.val.out) 0
        ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)) :=
    eq_of_heq (TotalSpace.ext_iff.mp h).2
  rw [mfderiv_comp 0 (hf.mdifferentiable (by simp) _) (hg γ),
    mfderiv_comp 0 (hf.mdifferentiable (by simp) _) (hg δ),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hb] at hamb
  have hv := hdf_inj _ hamb
  let c : LeafChart L := ⟨chartAt ℂ (γ.val.out 0), IsManifold.chart_mem_maximalAtlas _⟩
  have hcγ : γ.val.out 0 ∈ c.val.source := mem_chart_source _ _
  have hcδ : δ.val.out 0 ∈ c.val.source := hb ▸ hcγ
  have hcoef (η : CurveParamGerm L) (hc : η.val.out 0 ∈ c.val.source) :
      curveGermFirst L c η =
        mfderiv 𝓘(ℂ) 𝓘(ℂ) c.val (η.val.out 0)
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) η.val.out 0
            ((tangentSpaceCastModel 𝓘(ℂ) (0 : ℂ)).symm 1)) := by
    have hcD := (contMDiffAt_of_mem_maximalAtlas c.property hc).mdifferentiableAt
      (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    rw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp 0 hcD (hg η),
      mfderiv_eq_fderiv]
    change germFirst (η.val.map (c.val : L → ℂ)) = _
    conv_lhs => rw [← Quotient.out_eq η.val]
    rfl
  refine ⟨by rw [hbase, hbase, hb], c, ?_, ?_⟩
  · rw [hbase]
    exact hcγ
  · rw [hcoef γ hcγ, hcoef δ hcδ, hv, hb]


end HolomorphicAnosov.Ghys

