import HolomorphicAnosov.Ghys.AffineTransformationGermRigidity
import Mathlib.Topology.LocallyConstant.Basic

open Set Filter _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov.Ghys

universe u

/-- Affine developments on a connected complex curve differ by a single affine transformation.
(Thurston, §3.5, p.35) -/
theorem affine_developing_uniqueness
    (L : Type u) [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [ConnectedSpace L] (A : ComplexAffineAtlas L)
    (D₁ D₂ : L → ℂ)
    (h₁ : ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₁ y = a.apply (c y))
    (h₂ : ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D₂ y = a.apply (c y)) :
    ∃ a : ComplexAffineTransformation, ∀ x, D₂ x = a.apply (D₁ x) := by
  classical
  have hlocal : ∀ x, ∃ a : ComplexAffineTransformation,
      ∀ᶠ y in 𝓝 x, D₂ y = a.apply (D₁ y) := by
    intro x
    obtain ⟨c, hc, hxc⟩ := A.cover x
    obtain ⟨a, ha⟩ := h₁ c hc x hxc
    obtain ⟨b, hb⟩ := h₂ c hc x hxc
    refine ⟨⟨b.slope / a.slope, div_ne_zero b.slope_ne_zero a.slope_ne_zero,
      b.translation - (b.slope / a.slope) * a.translation⟩, ?_⟩
    filter_upwards [ha, hb] with y hay hby
    rw [hay, hby]
    dsimp [ComplexAffineTransformation.apply]
    field_simp [a.slope_ne_zero]
    ring
  have hunique : ∀ x (a b : ComplexAffineTransformation),
      (∀ᶠ y in 𝓝 x, D₂ y = a.apply (D₁ y)) →
      (∀ᶠ y in 𝓝 x, D₂ y = b.apply (D₁ y)) → a = b := by
    intro x a b ha hb
    obtain ⟨c, hc, hxc⟩ := A.cover x
    obtain ⟨e, he⟩ := h₁ c hc x hxc
    let ae : ComplexAffineTransformation := ⟨a.slope * e.slope,
      mul_ne_zero a.slope_ne_zero e.slope_ne_zero,
      a.slope * e.translation + a.translation⟩
    let be : ComplexAffineTransformation := ⟨b.slope * e.slope,
      mul_ne_zero b.slope_ne_zero e.slope_ne_zero,
      b.slope * e.translation + b.translation⟩
    have hab : ae = be := affineTransformation_eq_of_eventuallyEq c hxc (by
      filter_upwards [ha, hb, he] with y hay hby hey
      have hy := hay.symm.trans hby
      rw [hey] at hy
      dsimp [ae, be, ComplexAffineTransformation.apply] at hy ⊢
      linear_combination hy)
    have hs : a.slope = b.slope := mul_right_cancel₀ e.slope_ne_zero
      (congrArg ComplexAffineTransformation.slope hab)
    have ht : a.translation = b.translation := by
      have ht := congrArg ComplexAffineTransformation.translation hab
      dsimp [ae, be] at ht
      rw [hs] at ht
      exact add_left_cancel ht
    cases a
    cases b
    simp_all
  choose a ha using hlocal
  have hlc : IsLocallyConstant a := (IsLocallyConstant.iff_eventually_eq a).2 (by
    intro x
    filter_upwards [eventually_eventually_nhds.mpr (ha x)] with y hy
    exact hunique y (a y) (a x) (ha y) hy)
  let x₀ : L := Classical.arbitrary L
  refine ⟨a x₀, fun x ↦ ?_⟩
  rw [← hlc.apply_eq_of_preconnectedSpace x x₀]
  exact (ha x).self_of_nhds

end HolomorphicAnosov.Ghys
