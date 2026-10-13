import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Set Filter _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov.Ghys

universe u


theorem affine_developing_isLocalDiffeomorph
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineAtlas L) (D : L → ℂ)
    (hD : ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = a.apply (c y)) :
    IsLocalDiffeomorph (complexModel 1) 𝓘(ℂ) ∞ D := by
  intro x
  obtain ⟨c, hc, hx⟩ := A.cover x
  obtain ⟨a, ha⟩ := hD c hc x hx
  obtain ⟨U, hU, hUopen, hxU⟩ := mem_nhds_iff.mp ha
  let e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ∞ :=
    { toFun := a.apply
      invFun := fun z ↦ a.slope⁻¹ * (z - a.translation)
      left_inv := by
        intro z
        simp [ComplexAffineTransformation.apply, a.slope_ne_zero]
      right_inv := by
        intro z
        simp [ComplexAffineTransformation.apply, a.slope_ne_zero]
      contMDiff_toFun := by
        exact (contDiff_const.mul contDiff_id |>.add contDiff_const).contMDiff
      contMDiff_invFun := by
        exact (contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff }
  let r := c.restr U
  let p : PartialDiffeomorph (complexModel 1) 𝓘(ℂ) L ℂ ∞ :=
    { toPartialEquiv := r.toPartialEquiv
      open_source := r.open_source
      open_target := r.open_target
      contMDiffOn_toFun := (A.holomorphic c hc).1.mono (by
        intro y hy
        exact hy.1)
      contMDiffOn_invFun := (A.holomorphic c hc).2.mono (by
        intro z hz
        exact hz.1) }
  refine ⟨p.trans e.toPartialDiffeomorph, ?_, ?_⟩
  · change x ∈ r.source ∩ r ⁻¹' Set.univ
    exact ⟨by simpa [r, hUopen.interior_eq] using And.intro hx hxU, trivial⟩
  · intro y hy
    exact hU (interior_subset hy.1.2)

end HolomorphicAnosov.Ghys
