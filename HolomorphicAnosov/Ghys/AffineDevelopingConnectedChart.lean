import HolomorphicAnosov.Ghys.AffineDevelopingUniqueness


noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u


theorem affine_of_locally_affine_on_connected_g1
    {L : Type u} [TopologicalSpace L]
    (D : L → ℂ) (c : OpenPartialHomeomorph L ℂ)
    {V : Set L} (hVc : V ⊆ c.source)
    (hconn : IsPreconnected V) {p : L} (hp : p ∈ V)
    (hlocal : ∀ x : V, ∃ b : ComplexAffineTransformation,
      ∀ᶠ y in 𝓝 x.val, D y = b.apply (c y)) :
    ∃ b : ComplexAffineTransformation, ∀ x ∈ V, D x = b.apply (c x) := by
  classical
  choose b hb using hlocal
  have hloc : IsLocallyConstant b := (IsLocallyConstant.iff_eventually_eq b).mpr (by
    intro x
    have hnear := continuous_subtype_val.continuousAt.preimage_mem_nhds
      (eventually_eventually_nhds.mpr (hb x))
    filter_upwards [hnear] with y hy
    apply affineTransformation_eq_of_eventuallyEq c (hVc y.property)
    filter_upwards [hb y, hy] with z hzy hzx
    exact hzy.symm.trans hzx)
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hconn
  refine ⟨b ⟨p, hp⟩, ?_⟩
  intro x hx
  rw [← hloc.apply_eq_of_preconnectedSpace (⟨x, hx⟩ : V) ⟨p, hp⟩]
  exact (hb ⟨x, hx⟩).self_of_nhds


theorem maximal_affine_charts_compatible_g1
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineStructure L) (c d : OpenPartialHomeomorph L ℂ)
    (hc : c ∈ A.maximalAtlas L) (hd : d ∈ A.maximalAtlas L) :
    AffineChartsCompatible L c d := by
  intro x hx
  obtain ⟨e,he,hxe⟩ := A.out.cover x
  obtain ⟨b,hb⟩ := hc.2 e he x ⟨hxe,hx.1⟩
  obtain ⟨a,ha⟩ := hd.2 e he x ⟨hxe,hx.2⟩
  refine ⟨⟨a.slope / b.slope,div_ne_zero a.slope_ne_zero b.slope_ne_zero,
    a.translation - a.slope / b.slope * b.translation⟩,?_⟩
  filter_upwards [ha,hb] with y hay hby
  rw [hay,hby]
  dsimp [ComplexAffineTransformation.apply]
  field_simp [b.slope_ne_zero]
  ring


theorem affine_structure_eq_of_maximal_charts_g1
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A B : ComplexAffineStructure L)
    (h : ∀ c, c ∈ A.maximalAtlas L ↔ c ∈ B.maximalAtlas L) : A = B := by
  have hAB : AffineAtlasesEquivalent L A.out B.out := by
    intro c hc d hd
    have hdmax : d ∈ B.maximalAtlas L :=
      ⟨B.out.holomorphic d hd,fun e he ↦ B.out.compatible e he d hd⟩
    exact ((h d).mpr hdmax).2 c hc
  have heq : Quotient.mk (complexAffineAtlasSetoid L) A.out =
      Quotient.mk (complexAffineAtlasSetoid L) B.out := Quotient.sound hAB
  exact (Quotient.out_eq A).symm.trans (heq.trans (Quotient.out_eq B))


theorem affine_global_developing_normalized_chart_g1
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineStructure L)
    (D : Diffeomorph (complexModel 1) 𝓘(ℂ) L ℂ ∞)
    (hD : ∀ c ∈ A.out.charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y))
    (x y : L) (hxy : x ≠ y) :
    ∃ c : OpenPartialHomeomorph L ℂ,
      c ∈ A.maximalAtlas L ∧ c.source = univ ∧
      ∀ z, c z = (D z - D x) / (D y - D x) := by
  have hn : D y - D x ≠ 0 := sub_ne_zero.mpr (fun h ↦ hxy (D.injective h.symm))
  let B : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ∞ :=
    { toFun := fun z ↦ (z - D x) / (D y - D x)
      invFun := fun z ↦ (D y - D x) * z + D x
      left_inv := fun z ↦ by field_simp; ring
      right_inv := fun z ↦ by field_simp; ring
      contMDiff_toFun := (contMDiff_id.sub contMDiff_const).div_const _
      contMDiff_invFun := (contMDiff_const.mul contMDiff_id).add contMDiff_const }
  let E := D.trans B
  refine ⟨E.toHomeomorph.toOpenPartialHomeomorph,⟨?_,?_⟩,rfl,fun _ ↦ rfl⟩
  · exact ⟨E.contMDiff.contMDiffOn,E.symm.contMDiff.contMDiffOn⟩
  · intro c hc z hz
    obtain ⟨b,hb⟩ := hD c hc z hz.1
    refine ⟨⟨b.slope / (D y - D x), div_ne_zero b.slope_ne_zero hn,
      (b.translation - D x) / (D y - D x)⟩,?_⟩
    filter_upwards [hb] with w hw
    change (D w - D x) / (D y - D x) = _
    rw [hw]
    dsimp [ComplexAffineTransformation.apply]
    ring


theorem affine_developing_on_preconnected_chart
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineAtlas L) (D : L → ℂ)
    (hD : ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y))
    (c : OpenPartialHomeomorph L ℂ)
    (hc : c ∈ ComplexAffineStructure.maximalAtlas L
      (Quotient.mk (complexAffineAtlasSetoid L) A))
    (hconn : IsPreconnected c.source) {p : L} (hp : p ∈ c.source) :
    ∃ b : ComplexAffineTransformation, ∀ x ∈ c.source, D x = b.apply (c x) := by
  classical
  rw [ComplexAffineStructure.maximalAtlas_eq_of_representative] at hc
  have hlocal : ∀ x : c.source, ∃ b : ComplexAffineTransformation,
      ∀ᶠ y in 𝓝 x.val, D y = b.apply (c y) := by
    intro x
    obtain ⟨d, hd, hxd⟩ := A.cover x.val
    obtain ⟨b, hb⟩ := hD d hd x.val hxd
    obtain ⟨e, he⟩ := hc.2 d hd x.val ⟨hxd, x.property⟩
    refine ⟨⟨b.slope / e.slope, div_ne_zero b.slope_ne_zero e.slope_ne_zero,
      b.translation - b.slope / e.slope * e.translation⟩, ?_⟩
    filter_upwards [hb, he] with y hy hy'
    rw [hy, hy']
    dsimp [ComplexAffineTransformation.apply]
    field_simp [e.slope_ne_zero]
    ring
  exact affine_of_locally_affine_on_connected_g1 D c (fun _ hx ↦ hx)
    hconn hp hlocal

end HolomorphicAnosov.Ghys
