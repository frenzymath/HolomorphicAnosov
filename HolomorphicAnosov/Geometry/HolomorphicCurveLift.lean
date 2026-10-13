import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! This file proves holomorphicity of lifts through immersed complex curves. (Ghys, §3.) -/



noncomputable section
namespace HolomorphicAnosov
open scoped Manifold ContDiff Topology _root_.Topology

/-- A continuous lift through a holomorphic immersed complex curve is holomorphic when its ambient composite is holomorphic. (Ghys, §3.) -/
theorem holomorphic_curve_lift
    {d : ℕ} {M L P : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace L] [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
    [TopologicalSpace P] [ChartedSpace ℂ P] [IsManifold 𝓘(ℂ) ∞ P]
    (i : L → M) (hi : ContMDiff 𝓘(ℂ) (complexModel d) ∞ i)
    (hi' : ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) i z))
    (h : P → L) (hc : Continuous h)
    (hh : ContMDiff 𝓘(ℂ) (complexModel d) ∞ (i ∘ h)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ h := by
  intro x
  let y := h x
  let a := extChartAt 𝓘(ℂ) x x
  let b := extChartAt 𝓘(ℂ) y y
  let g := writtenInExtChartAt 𝓘(ℂ) (complexModel d) y i
  let q := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x h
  have hg : ContDiffAt ℂ ∞ g b := by
    simpa only [g, b, writtenInExtChartAt, modelWithCornersSelf_coe, Set.range_id,
      contDiffWithinAt_univ] using (contMDiffAt_iff.mp (hi y)).2
  have hginj : Function.Injective (fderiv ℂ g b) := by
    have he := (hi y).mdifferentiableAt (by simp)
    intro u v huv
    apply (tangentSpaceCastModel 𝓘(ℂ) y).symm.injective
    apply hi' y
    rw [he.mfderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, modelWithCornersSelf_coe, Set.range_id,
      fderivWithin_univ]
    change (tangentSpaceCastModel (complexModel d) (i y)).symm ((fderiv ℂ g b) u) =
      (tangentSpaceCastModel (complexModel d) (i y)).symm ((fderiv ℂ g b) v)
    rw [huv]
  have hg1 : (fderiv ℂ g b) 1 ≠ 0 := by
    intro hz
    exact one_ne_zero (hginj (hz.trans (map_zero _).symm))
  obtain ⟨j, hj⟩ : ∃ j : Fin d, (fderiv ℂ g b) 1 j ≠ 0 := by
    by_contra hn
    apply hg1
    ext j
    simpa using not_exists.mp hn j
  let f : ℂ → ℂ := fun z ↦ g z j
  have hf : ContDiffAt ℂ ∞ f b := (contDiffAt_pi.mp hg) j
  let D : ℂ ≃L[ℂ] ℂ :=
    (LinearEquiv.smulOfNeZero ℂ ℂ ((fderiv ℂ g b) 1 j) hj).toContinuousLinearEquiv
  have hD : HasFDerivAt f (D : ℂ →L[ℂ] ℂ) b := by
    convert! (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp b
      (hg.differentiableAt (by simp)).hasFDerivAt using 1
    try rfl
    apply ContinuousLinearMap.ext
    intro v
    simp [D, LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit, mul_comm]
  let e := hf.toOpenPartialHomeomorph f hD (by simp)
  have hb : b ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hD (by simp)
  have hk : ContDiffAt ℂ ∞ e.symm (f b) := by
    exact hf.to_localInverse hD (by simp)
  have hq : ContinuousAt q a := by
    have ht : ContinuousAt (extChartAt 𝓘(ℂ) y ∘ h)
        ((extChartAt 𝓘(ℂ) x).symm a) := by
      simpa only [a, extChartAt_to_inv] using
        (continuousAt_extChartAt (I := 𝓘(ℂ)) y).comp hc.continuousAt
    exact ht.comp (continuousAt_extChartAt_symm (I := 𝓘(ℂ)) x)
  have hqa : q a = b := by
    simp [q, a, b, y, writtenInExtChartAt]
  have hhcoord : ContDiffAt ℂ ∞
      (writtenInExtChartAt 𝓘(ℂ) (complexModel d) x (i ∘ h)) a := by
    simpa only [writtenInExtChartAt, modelWithCornersSelf_coe, Set.range_id,
      contDiffWithinAt_univ, a] using (contMDiffAt_iff.mp (hh x)).2
  have hcomp : writtenInExtChartAt 𝓘(ℂ) (complexModel d) x (i ∘ h) =ᶠ[𝓝 a]
      g ∘ q := by
    simpa only [g, q, a, y, modelWithCornersSelf_coe, Set.range_id, Set.inter_univ,
      Set.preimage_univ, Set.univ_inter, nhdsWithin_univ] using
      (writtenInExtChartAt_comp (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (I'' := complexModel d) (x := x) (g := i) (hc.continuousAt.continuousWithinAt (s := Set.univ)))
  have hfgq : ContDiffAt ℂ ∞ (f ∘ q) a := by
    have he : ContDiffAt ℂ ∞ (g ∘ q) a := hhcoord.congr_of_eventuallyEq hcomp.symm
    exact (contDiffAt_pi.mp he) j
  have hfinal : ContDiffAt ℂ ∞ q a := by
    have hinv : (e.symm ∘ f ∘ q) =ᶠ[𝓝 a] q := by
      filter_upwards [hq.preimage_mem_nhds (hqa.symm ▸ e.open_source.mem_nhds hb)] with z hz
      exact e.left_inv hz
    have hs : ContDiffAt ℂ ∞ (e.symm ∘ f ∘ q) a :=
      (hqa.symm ▸ hk).comp a hfgq
    exact hs.congr_of_eventuallyEq hinv.symm
  apply contMDiffAt_iff.mpr
  refine ⟨hc.continuousAt, ?_⟩
  simpa only [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ,
    q, a, writtenInExtChartAt] using hfinal

end HolomorphicAnosov

