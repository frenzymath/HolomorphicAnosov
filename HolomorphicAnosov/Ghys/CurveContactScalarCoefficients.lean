import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! This file proves that composition with a complex smooth scalar function preserves the first and
normalized second coefficients of germs with second-order contact. (Ghys, §3, p.591; Michor,
§§1.3–1.6, pp.2–3) -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped Manifold ContDiff
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
variable [IsManifold 𝓘(ℂ) ∞ L]

omit [IsManifold 𝓘(ℂ) ∞ L] in
/-- Two parametrization germs with second-order contact have equal first and normalized second
coefficients after composition with any scalar function complex smooth at their common base
point. (Ghys, §3, p.591; Michor, §§1.3–1.6, pp.2–3) -/
theorem curveContact2_scalar_coefficients
    (γ δ : CurveParamGerm L) (h : CurveContact2 L γ δ) (φ : L → ℂ)
    (hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (curveGermBase L γ.1)) :
    germFirst (γ.1.map φ) = germFirst (δ.1.map φ) ∧
      germSecond (γ.1.map φ) = germSecond (δ.1.map φ) := by
  have hformula (η : CurveParamGerm L) (e : LeafChart L)
      (he : curveGermBase L η.1 ∈ e.1.source)
      (hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (curveGermBase L η.1)) :
      germFirst (η.1.map φ) =
        deriv (φ ∘ e.1.symm) (e.1 (curveGermBase L η.1)) * curveGermFirst L e η ∧
      germSecond (η.1.map φ) =
        deriv (φ ∘ e.1.symm) (e.1 (curveGermBase L η.1)) * curveGermSecond L e η +
        (iteratedDeriv 2 (φ ∘ e.1.symm) (e.1 (curveGermBase L η.1)) / 2) *
          curveGermFirst L e η ^ 2 := by
    obtain ⟨g, hg0, hg, _, hge⟩ := η.2
    have hb : curveGermBase L η.1 = g 0 := by rw [← hge]; rfl
    rw [hb] at he hφ ⊢
    have hg' := hg.contMDiffAt (g.open_source.mem_nhds hg0)
    have hc : ContDiffAt ℂ 2 (e.1 ∘ g) 0 :=
      ((contMDiffAt_of_mem_maximalAtlas e.2 he).comp 0 hg').contDiffAt.of_le (by simp)
    have hi := contMDiffAt_symm_of_mem_maximalAtlas e.2 (e.1.map_source he)
    have hφ' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ φ (e.1.symm (e.1 (g 0))) := by
      simpa only [e.1.left_inv he] using hφ
    have hh : ContDiffAt ℂ 2 (φ ∘ e.1.symm) (e.1 (g 0)) :=
      (hφ'.comp _ hi).contDiffAt.of_le (by simp)
    have heq : (φ ∘ g) =ᶠ[𝓝 (0 : ℂ)] (φ ∘ e.1.symm) ∘ (e.1 ∘ g) := by
      filter_upwards [hg'.continuousAt.preimage_mem_nhds (e.1.open_source.mem_nhds he)] with t ht
      simp only [Function.comp_apply, e.1.left_inv ht]
    unfold curveGermFirst curveGermSecond
    rw [← hge]
    change deriv (φ ∘ g) 0 = _ * deriv (e.1 ∘ g) 0 ∧
      iteratedDeriv 2 (φ ∘ g) 0 / 2 =
        _ * (iteratedDeriv 2 (e.1 ∘ g) 0 / 2) + _ * deriv (e.1 ∘ g) 0 ^ 2
    constructor
    · rw [heq.deriv_eq, deriv_comp 0 (hh.differentiableAt (by norm_num))
        (hc.differentiableAt (by norm_num))]
      rfl
    · rw [heq.iteratedDeriv_eq 2, iteratedDeriv_comp_two hh hc]
      dsimp only [Function.comp_apply]
      ring
  obtain ⟨hb, e, he, ha, hb2⟩ := h
  have hγ := hformula γ e he hφ
  have hδ := hformula δ e (hb ▸ he) (hb ▸ hφ)
  constructor
  · rw [hγ.1, hδ.1, hb, ha]
  · rw [hγ.2, hδ.2, hb, ha, hb2]

end HolomorphicAnosov.Ghys
