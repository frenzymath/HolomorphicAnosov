import HolomorphicAnosov.Ghys.AffineLocalMapSchwarzianCalculus

/-! This file proves that the identity map has zero Schwarzian in compatible affine coordinates.
(Ghys, §4, p.594) -/
noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u

/-- The Schwarzian quadratic form of the identity vanishes in any pair of charts from the same
maximal affine atlas. (Ghys, §4, p.594) -/
theorem schwarzian_quadratic_identity {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineStructure L) (a b : OpenPartialHomeomorph L ℂ)
    (ha : a ∈ ComplexAffineStructure.maximalAtlas L A)
    (hb : b ∈ ComplexAffineStructure.maximalAtlas L A)
    (p : L) (hpa : p ∈ a.source) (hpb : p ∈ b.source) :
    schwarzianQuadraticAt a (OpenPartialHomeomorph.refl L) b p = 0 := by
  have hid : IsHolomorphicCurveLocalMap (OpenPartialHomeomorph.refl L) :=
    ⟨contMDiffOn_id, contMDiffOn_id⟩
  apply (affine_local_map_schwarzian_calculus A A A
    (OpenPartialHomeomorph.refl L) hid a b ha hb p hpa (Set.mem_univ p) hpb).2.2.2.1
  obtain ⟨r, hr, hpr⟩ := A.out.cover p
  obtain ⟨α, hα⟩ := ha.2 r hr p ⟨hpr, hpa⟩
  obtain ⟨β, hβ⟩ := hb.2 r hr p ⟨hpr, hpb⟩
  refine ⟨⟨β.slope / α.slope, div_ne_zero β.slope_ne_zero α.slope_ne_zero,
    β.translation - β.slope / α.slope * α.translation⟩, ?_⟩
  have hcont : ContinuousAt a.symm (a p) :=
    a.continuousAt_symm (a.map_source hpa)
  have hα' := hcont.eventually (by simpa [a.left_inv hpa] using hα)
  have hβ' := hcont.eventually (by simpa [a.left_inv hpa] using hβ)
  filter_upwards [hα', hβ', a.open_target.mem_nhds (a.map_source hpa)] with z hzα hzβ hz
  change b (a.symm z) = _
  have hhα : z = α.slope * r (a.symm z) + α.translation := by
    simpa [ComplexAffineTransformation.apply, a.right_inv hz] using hzα
  rw [hzβ]
  dsimp [ComplexAffineTransformation.apply]
  conv_rhs => rw [hhα]
  field_simp [α.slope_ne_zero]
  ring

end HolomorphicAnosov.Ghys
