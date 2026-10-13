import HolomorphicAnosov.Ghys.AffineSchwarzianIdentity

/-! Affine coordinate independence of the Schwarzian quadratic form (Ghys, §4) -/
noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v
variable {L₀ : Type u} {L₁ : Type v}
  [TopologicalSpace L₀] [TopologicalSpace L₁]
  [ChartedSpace (ComplexModel 1) L₀] [ChartedSpace (ComplexModel 1) L₁]

set_option backward.isDefEq.respectTransparency false in
/-- The Schwarzian quadratic form is independent of both affine coordinates. (Ghys, §4) -/
theorem schwarzian_quadratic_coordinate_independent
    (A₀ : ComplexAffineStructure L₀) (A₁ : ComplexAffineStructure L₁)
    (h : OpenPartialHomeomorph L₀ L₁) (hh : IsHolomorphicCurveLocalMap h)
    (c c' : OpenPartialHomeomorph L₀ ℂ) (d d' : OpenPartialHomeomorph L₁ ℂ)
    (hc : c ∈ ComplexAffineStructure.maximalAtlas L₀ A₀)
    (hc' : c' ∈ ComplexAffineStructure.maximalAtlas L₀ A₀)
    (hd : d ∈ ComplexAffineStructure.maximalAtlas L₁ A₁)
    (hd' : d' ∈ ComplexAffineStructure.maximalAtlas L₁ A₁)
    (x : L₀) (hxc : x ∈ c.source) (hxc' : x ∈ c'.source)
    (hxh : x ∈ h.source) (hxd : h x ∈ d.source) (hxd' : h x ∈ d'.source) :
    schwarzianQuadraticAt c h d x = schwarzianQuadraticAt c' h d' x := by
  have hid₀ : IsHolomorphicCurveLocalMap (OpenPartialHomeomorph.refl L₀) :=
    ⟨contMDiffOn_id, contMDiffOn_id⟩
  have hid₁ : IsHolomorphicCurveLocalMap (OpenPartialHomeomorph.refl L₁) :=
    ⟨contMDiffOn_id, contMDiffOn_id⟩
  have hsrc := (affine_local_map_schwarzian_calculus A₀ A₀ A₁
    (OpenPartialHomeomorph.refl L₀) hid₀ c c' hc hc' x hxc (Set.mem_univ x) hxc').2.2.2.2
      h d hh hd hxh hxd
  have htgt := (affine_local_map_schwarzian_calculus A₀ A₁ A₁
    h hh c' d hc' hd x hxc' hxh hxd).2.2.2.2
      (OpenPartialHomeomorph.refl L₁) d' hid₁ hd' (Set.mem_univ (h x)) hxd'
  ext v
  have hs := hsrc.2 v
  have ht := htgt.2 v
  simp only [OpenPartialHomeomorph.refl_trans,
    schwarzian_quadratic_identity A₀ c c' hc hc' x hxc hxc', zero_apply, zero_add] at hs
  change schwarzianQuadraticAt c h d x v = schwarzianQuadraticAt c' h d x
    (mfderiv (complexModel 1) (complexModel 1) id x v) at hs
  rw [mfderiv_id] at hs
  simp only [OpenPartialHomeomorph.trans_refl,
    schwarzian_quadratic_identity A₁ d d' hd hd' (h x) hxd hxd', zero_apply, add_zero] at ht
  exact hs.trans ht.symm

end HolomorphicAnosov.Ghys
