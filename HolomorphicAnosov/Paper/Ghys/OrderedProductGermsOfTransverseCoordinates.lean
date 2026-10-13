import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import HolomorphicAnosov.Paper.Ghys.SurfaceHolomorphicProductChartsAtlasHelper
import HolomorphicAnosov.Paper.Ghys.CompleteAffineProjectiveCoordinate

/-! This file constructs ordered product transition germs from paired transverse coordinates (Ghys, §5). -/
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys.OrderedProductGerm
universe u

/-- A PSL action is determined by its values on an infinite set of finite points. -/
theorem finite_unique (a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (V : Set ℂ) (hV : V.Infinite)
    (heq : ∀ z ∈ V, a • OnePoint.equivProjectivization ℂ (z : OnePoint ℂ) =
      b • OnePoint.equivProjectivization ℂ (z : OnePoint ℂ)) : a = b := by
  obtain ⟨g, hg⟩ := psl_transformation_mobius a
  obtain ⟨h, hh⟩ := psl_transformation_mobius b
  have hgh : g = h := by
    apply mobius_eq_of_infinite_finite_eq g h V hV
    intro z hz
    have ht := congrArg (OnePoint.equivProjectivization ℂ).symm (heq z hz)
    simpa only [hg, hh, Equiv.symm_apply_apply] using ht
  apply eq_of_smul_eq_smul (α := ComplexProjectiveLine)
  intro p
  apply (OnePoint.equivProjectivization ℂ).symm.injective
  rw [hg, hh, hgh]

/-- Agreement on a nonempty open projective set determines the PSL element. -/
theorem open_unique (a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (U : Set ComplexProjectiveLine) (hU : IsOpen U) (hne : U.Nonempty)
    (heq : ∀ p ∈ U, a • p = b • p) : a = b := by
  let e := NativeProjectiveTopology.nativeProjectiveLineHomeomorphOnePoint
  have hO : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hn : (e.symm ⁻¹' U).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨e p, by simpa using hp⟩
  obtain ⟨z, hz⟩ := OnePoint.denseRange_coe.exists_mem_open hO hn
  let V : Set ℂ := (fun z : ℂ ↦ e.symm (z : OnePoint ℂ)) ⁻¹' U
  have hV : IsOpen V := hO.preimage OnePoint.continuous_coe
  have hinf : V.Infinite := infinite_of_mem_nhds z (hV.mem_nhds hz)
  apply finite_unique a b V hinf
  intro w hw
  exact heq _ hw

/-- Both coordinates of an ordered transition are determined on a nonempty open product set. -/
theorem pair_open_unique
    (a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ×
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (U : Set (ComplexProjectiveLine × ComplexProjectiveLine))
    (hU : IsOpen U) (hne : U.Nonempty)
    (heq : ∀ p ∈ U, (a.1 • p.1, a.2 • p.2) = (b.1 • p.1, b.2 • p.2)) : a = b := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨V, W, hV, hpV, hW, hpW, hVW⟩ := mem_nhds_prod_iff'.mp (hU.mem_nhds hp)
  apply Prod.ext
  · apply open_unique a.1 b.1 V hV ⟨p.1, hpV⟩
    intro z hz
    exact congrArg Prod.fst (heq (z, p.2) (hVW ⟨hz, hpW⟩))
  · apply open_unique a.2 b.2 W hW ⟨p.2, hpW⟩
    intro z hz
    exact congrArg Prod.snd (heq (p.1, z) (hVW ⟨hpV, hz⟩))

/-- Ordered transition germs are unique at a source point. -/
theorem chart_germ_unique {X : Type*} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (ComplexProjectiveLine × ComplexProjectiveLine))
    (x : X) (hx : x ∈ c.source)
    (a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ×
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (heq : ∀ᶠ y in 𝓝 x,
      (a.1 • (c y).1, a.2 • (c y).2) = (b.1 • (c y).1, b.2 • (c y).2)) : a = b := by
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp
    (heq.and (c.open_source.mem_nhds hx))
  have hsource : U ⊆ c.source := fun y hy ↦ (hUsub hy).2
  apply pair_open_unique a b (c '' U)
    (c.isOpen_image_of_subset_source hUopen hsource) ⟨c x, x, hxU, rfl⟩
  rintro p ⟨y, hy, rfl⟩
  exact (hUsub hy).1


/-- The open image of a product chart determines the ordered PSL transition germ. (Ghys, §5) -/
theorem local_unique {X : Type u} [TopologicalSpace X] {ι : Type u}
    (chart : ι → OpenPartialHomeomorph X
      (ComplexProjectiveLine × ComplexProjectiveLine))
    (i j : ι) (x : X) (hx : x ∈ (chart i).source ∩ (chart j).source)
    (g h : OrderedProjectiveTransition)
    (hg : OrderedProjectiveProductGerm ι chart i j x g)
    (hh : OrderedProjectiveProductGerm ι chart i j x h) : g = h := by
  obtain ⟨N, hN, hxN, _, hgN⟩ := hg
  obtain ⟨V, hV, hxV, _, hhV⟩ := hh
  apply chart_germ_unique (chart i) x hx.1 g h
  filter_upwards [hN.mem_nhds hxN, hV.mem_nhds hxV] with y hyN hyV
  exact (hgN y hyN).symm.trans (hhV y hyV)

end HolomorphicAnosov.Ghys.OrderedProductGerm

namespace HolomorphicAnosov.Ghys
universe u
open Set Filter _root_.Topology

/-- The two transverse coordinates determine an ordered local transition germ, uniquely. (Ghys, §5) -/
theorem ordered_product_germs_of_transverse_coordinates
    {X : Type u} [TopologicalSpace X] {ι : Type u}
    (chart : ι → OpenPartialHomeomorph X
      (ComplexProjectiveLine × ComplexProjectiveLine))
    (stable unstable : ι → X → ComplexProjectiveLine)
    (hchart : ∀ i x, x ∈ (chart i).source →
      ∀ᶠ y in 𝓝 x, chart i y = (stable i y, unstable i y))
    (hstable : ∀ i j x, x ∈ (chart i).source ∩ (chart j).source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ y in 𝓝 x, stable j y = g.apply (stable i y))
    (hunstable : ∀ i j x, x ∈ (chart i).source ∩ (chart j).source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ y in 𝓝 x, unstable j y = g.apply (unstable i y)) :
    (∀ i j x, x ∈ (chart i).source ∩ (chart j).source →
      ∃ g : OrderedProjectiveTransition,
        OrderedProjectiveProductGerm ι chart i j x g) ∧
    (∀ i j x, x ∈ (chart i).source ∩ (chart j).source →
      ∀ g h : OrderedProjectiveTransition,
        OrderedProjectiveProductGerm ι chart i j x g →
        OrderedProjectiveProductGerm ι chart i j x h → g = h) := by
  refine ⟨?_, OrderedProductGerm.local_unique chart⟩
  intro i j x hx
  obtain ⟨s, hs⟩ := hstable i j x hx
  obtain ⟨u, hu⟩ := hunstable i j x hx
  obtain ⟨a, ha, _⟩ := complex_mobius_psl_normalization s
  obtain ⟨b, hb, _⟩ := complex_mobius_psl_normalization u
  have heq : ∀ᶠ y in 𝓝 x,
      chart j y = (a • (chart i y).1, b • (chart i y).2) := by
    filter_upwards [hchart i x hx.1, hchart j x hx.2, hs, hu] with y hi hj hs hu
    rw [hi, hj, hs, hu, ha, hb]
  obtain ⟨N, hNsub, hNo, hxN⟩ := mem_nhds_iff.mp
    (heq.and (((chart i).open_source.inter (chart j).open_source).mem_nhds hx))
  exact ⟨(a,b), N, hNo, hxN, fun y hy ↦ (hNsub hy).2,
    fun y hy ↦ (hNsub hy).1⟩

end HolomorphicAnosov.Ghys
