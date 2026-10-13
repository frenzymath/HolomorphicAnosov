import HolomorphicAnosov.Geometry.Holonomy.StableBoxPath
import Mathlib.Topology.Separation.Lemmas
import HolomorphicAnosov.Geometry.FoliationPlaqueLabelFiberCountableG9
import HolomorphicAnosov.Paper.Ghys.CompleteAffineProjectiveCoordinate

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u

variable {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s 2 M)
  (C : IntrinsicComplexUnstableLeaves F)

/-- The open plaque parametrization into its intrinsic unstable leaf. (Hirsch–Pugh–Shub, §7
pp.115–116) -/
def unstablePlaqueCoordinate (b : F.boxIndex) (z : FoliationCoordinateDisk s) :
    letI := F.unstableTopology (F.unstableLabel b z)
    OpenPartialHomeomorph (FoliationCoordinateDisk 2)
      (IntrinsicFoliationLeaf F.unstablePartition (F.unstableLabel b z)) := by
  letI := F.unstableTopology (F.unstableLabel b z)
  letI : Nonempty (FoliationCoordinateDisk 2) := ⟨⟨0, by simp⟩⟩
  exact (F.unstable_plaque b z).toOpenPartialHomeomorph _

/-- The projective coordinate on an intrinsic unstable plaque obtained from its transverse
coordinate. -/
def unstablePlaqueProjectiveCoordinate (b : F.boxIndex) (z : FoliationCoordinateDisk s)
    (c : OpenPartialHomeomorph (FoliationCoordinateDisk 2) ComplexProjectiveLine) :
    letI := F.unstableTopology (F.unstableLabel b z)
    OpenPartialHomeomorph
      (IntrinsicFoliationLeaf F.unstablePartition (F.unstableLabel b z))
      ComplexProjectiveLine :=
  letI := F.unstableTopology (F.unstableLabel b z)
  (unstablePlaqueCoordinate F b z).symm.trans c

/-- The source of the plaque projective coordinate consists exactly of the plaque points whose
transverse parameters lie in the coordinate source. (Ghys, §4 p.594) -/
theorem unstablePlaqueProjectiveCoordinate_source
    (b : F.boxIndex) (z : FoliationCoordinateDisk s)
    (c : OpenPartialHomeomorph (FoliationCoordinateDisk 2) ComplexProjectiveLine) :
    letI := F.unstableTopology (F.unstableLabel b z)
    (unstablePlaqueProjectiveCoordinate F b z c).source =
      {p | ∃ w : FoliationCoordinateDisk 2, w ∈ c.source ∧
        p.val = ((F.box b).chart (z,w)).val} := by
  let := F.unstableTopology (F.unstableLabel b z)
  let e := unstablePlaqueCoordinate F b z
  have he (w : FoliationCoordinateDisk 2) :
      e w = ⟨((F.box b).chart (z,w)).val, F.unstable_label b z w⟩ := rfl
  have hes : e.source = univ := rfl
  ext p
  constructor
  · intro hp
    change p ∈ e.target ∧ e.symm p ∈ c.source at hp
    refine ⟨e.symm p, hp.2, ?_⟩
    have h := congrArg Subtype.val (e.right_inv hp.1)
    exact h.symm
  · rintro ⟨w, hw, hwp⟩
    have hpw : p = e w := Subtype.ext hwp
    change p ∈ e.target ∧ e.symm p ∈ c.source
    rw [hpw]
    have hw' : w ∈ e.source := hes ▸ mem_univ w
    exact ⟨e.map_source hw', by simpa only [e.left_inv hw'] using hw⟩

/-- The plaque projective coordinate has the same target as its transverse coordinate. -/
theorem unstablePlaqueProjectiveCoordinate_target
    (b : F.boxIndex) (z : FoliationCoordinateDisk s)
    (c : OpenPartialHomeomorph (FoliationCoordinateDisk 2) ComplexProjectiveLine) :
    letI := F.unstableTopology (F.unstableLabel b z)
    (unstablePlaqueProjectiveCoordinate F b z c).target = c.target := by
  let := F.unstableTopology (F.unstableLabel b z)
  change c.target ∩ c.symm ⁻¹' (unstablePlaqueCoordinate F b z).source = c.target
  change c.target ∩ c.symm ⁻¹' univ = c.target
  simp

/-- The projective coordinate of the plaque point with transverse parameter `w` is `c w`. -/
theorem unstablePlaqueProjectiveCoordinate_apply
    (b : F.boxIndex) (z : FoliationCoordinateDisk s)
    (c : OpenPartialHomeomorph (FoliationCoordinateDisk 2) ComplexProjectiveLine)
    (w : FoliationCoordinateDisk 2) :
    letI := F.unstableTopology (F.unstableLabel b z)
    unstablePlaqueProjectiveCoordinate F b z c
      ⟨((F.box b).chart (z,w)).val, F.unstable_label b z w⟩ = c w := by
  let := F.unstableTopology (F.unstableLabel b z)
  let e := unstablePlaqueCoordinate F b z
  change c (e.symm (e w)) = c w
  rw [e.left_inv (show w ∈ e.source from mem_univ w)]

/-- A transverse projective chart whose coordinate is biholomorphic on each unstable plaque in the
specified box. (Ghys, §4 p.594 and §5 p.597) -/
def transverseProjectiveChartOfCoordinate
    (b : F.boxIndex) (U : TopologicalSpace.Opens (FoliationCoordinateDisk s))
    (c : OpenPartialHomeomorph (FoliationCoordinateDisk 2) ComplexProjectiveLine)
    (hc : ∀ z ∈ U,
      letI := F.unstableTopology (F.unstableLabel b z)
      letI := C.charts (F.unstableLabel b z)
      let e := unstablePlaqueProjectiveCoordinate F b z c
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target) :
    TransverseProjectiveChart F C where
  box := b
  stableDomain := U
  coordinate := c
  holomorphic_on_plaque := fun z hz ↦
    ⟨unstablePlaqueProjectiveCoordinate F b z c,
      unstablePlaqueProjectiveCoordinate_source F b z c,
      unstablePlaqueProjectiveCoordinate_target F b z c,
      fun w _ ↦ unstablePlaqueProjectiveCoordinate_apply F b z c w,
      hc z hz⟩

/-- The point-preserving homeomorphism between intrinsic unstable leaves with equal quotient labels. -/
def unstableLabelHomeomorph
    (q q' : Quotient F.unstablePartition) (h : q = q') :
    letI := F.unstableTopology q
    letI := F.unstableTopology q'
    IntrinsicFoliationLeaf F.unstablePartition q ≃ₜ
      IntrinsicFoliationLeaf F.unstablePartition q' := by
  subst q'
  let := F.unstableTopology q
  exact Homeomorph.refl _

@[simp] theorem unstableLabelHomeomorph_val
    (q q' : Quotient F.unstablePartition) (h : q = q') :
    letI := F.unstableTopology q
    letI := F.unstableTopology q'
    ∀ z, (unstableLabelHomeomorph F q q' h z).val = z.val := by
  subst q'
  let := F.unstableTopology q
  intro z
  rfl

@[simp] theorem unstableLabelHomeomorph_symm_val
    (q q' : Quotient F.unstablePartition) (h : q = q') :
    letI := F.unstableTopology q
    letI := F.unstableTopology q'
    ∀ z, ((unstableLabelHomeomorph F q q' h).symm z).val = z.val := by
  subst q'
  let := F.unstableTopology q
  intro z
  rfl

/-- The unstable plaque parametrization into the unstable leaf through a marked box point. -/
def unstablePlaqueCoordinateAt
    (b : F.boxIndex) (z : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk 2) :
    OpenPartialHomeomorph (FoliationCoordinateDisk 2)
      (F.ULeaf ((F.box b).chart (z,w₀)).val) :=
  letI := F.unstableTopology (F.unstableLabel b z)
  (unstablePlaqueCoordinate F b z).trans
    (unstableLabelHomeomorph F _ _ (F.unstable_label b z w₀).symm).toOpenPartialHomeomorph

@[simp] theorem unstablePlaqueCoordinateAt_source
    (b : F.boxIndex) (z : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk 2) :
    (unstablePlaqueCoordinateAt F b z w₀).source = univ := by
  simp [unstablePlaqueCoordinateAt, unstablePlaqueCoordinate]

@[simp] theorem unstablePlaqueCoordinateAt_val
    (b : F.boxIndex) (z : FoliationCoordinateDisk s)
    (w₀ w : FoliationCoordinateDisk 2) :
    (unstablePlaqueCoordinateAt F b z w₀ w).val = ((F.box b).chart (z,w)).val := by
  simp [unstablePlaqueCoordinateAt, OpenPartialHomeomorph.trans_apply,
    unstablePlaqueCoordinate]

/-- The transport between two full unstable plaques in one box that preserves the transverse
parameter. (Ghys, p.594) -/
def fullBoxPlaqueTransport
    (b : F.boxIndex) (z z' : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk 2) :
    LocalPlaqueTransport F ((F.box b).chart (z,w₀)).val ((F.box b).chart (z',w₀)).val := by
  let p := unstablePlaqueCoordinateAt F b z w₀
  let p' := unstablePlaqueCoordinateAt F b z' w₀
  have hp : p.source = univ := unstablePlaqueCoordinateAt_source F b z w₀
  have hp' : p'.source = univ := unstablePlaqueCoordinateAt_source F b z' w₀
  have hx : F.uPoint ((F.box b).chart (z,w₀)).val = p w₀ := by
    apply Subtype.ext
    exact (unstablePlaqueCoordinateAt_val F b z w₀ w₀).symm
  have hy : F.uPoint ((F.box b).chart (z',w₀)).val = p' w₀ := by
    apply Subtype.ext
    exact (unstablePlaqueCoordinateAt_val F b z' w₀ w₀).symm
  refine {
    map := p.symm.trans p'
    source_point := ?_
    map_point := ?_
    box := b
    first := z
    second := z'
    transverse := w₀
    first_point := rfl
    second_point := rfl
    source_in_plaque := ?_
    coordinate_map := ?_ }
  · change F.uPoint _ ∈ p.target ∧ p.symm (F.uPoint _) ∈ p'.source
    rw [hx]
    exact ⟨p.map_source (hp ▸ mem_univ _), hp' ▸ mem_univ _⟩
  · change p' (p.symm (F.uPoint _)) = F.uPoint _
    rw [hx, hy, p.left_inv (hp ▸ mem_univ _)]
  · intro v hv
    refine ⟨p.symm v, ?_⟩
    have h := congrArg Subtype.val (p.right_inv hv.1)
    exact (unstablePlaqueCoordinateAt_val F b z w₀ (p.symm v)).symm.trans h
  · intro v w hv hw
    have hvw : p w = v := by
      apply Subtype.ext
      exact (unstablePlaqueCoordinateAt_val F b z w₀ w).trans hw
    change (p' (p.symm v)).val = _
    rw [← hvw, p.left_inv (hp ▸ mem_univ _)]
    exact unstablePlaqueCoordinateAt_val F b z' w₀ w

/-- The holonomy representative along a stable path in one box given by full plaque transport.
(Ghys, p.594) -/
def fullBoxPathHolonomy
    (b : F.boxIndex) (z z' : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk 2) :
    letI := F.stableTopology (F.stableLabel b w)
    PathHolonomyRepresentative F (stableBoxPath F b z z' w) 0 1 := by
  let := F.stableTopology (F.stableLabel b w)
  let γ := stableBoxPath F b z z' w
  let e := rebasePlaqueTransport F (fullBoxPlaqueTransport F b z z' w)
    (congrArg Subtype.val γ.source).symm (congrArg Subtype.val γ.target).symm
  exact {
    toPointedLeafHomeomorph := e.toPointedLeafHomeomorph
    chain := PlaqueChainAlong.single 0 1 (by simp) e (by
      intro t _ _
      change ∃ v, ((F.box e.box).chart (v, e.transverse)).val = (γ t).val
      exact (rebasePlaqueTransport_segment F _ _ _ _).mpr
        (stableBoxPath_in_plaque F b z z' w t)) }
/-- The receiving transverse coordinate is constant on a connected piece of a stable plaque
contained in another box. (Hirsch–Pugh–Shub, §7 pp.115–116) -/
theorem boxTransition_stable_constant
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    (b b' : F.boxIndex) (V : Set (FoliationCoordinateDisk s))
    (hV : IsPreconnected V) (z z' : V) (w : FoliationCoordinateDisk 2)
    (hinc : ∀ v ∈ V, ((F.box b).chart (v,w)).val ∈ (F.box b').image) :
    ((F.box b').chart.symm ⟨((F.box b).chart (z.val,w)).val, hinc z.val z.property⟩).2 =
    ((F.box b').chart.symm ⟨((F.box b).chart (z'.val,w)).val, hinc z'.val z'.property⟩).2 := by
  let q := F.stableLabel b w
  let coords : V → FoliationCoordinateDisk s × FoliationCoordinateDisk 2 :=
    fun v ↦ (F.box b').chart.symm
      ⟨((F.box b).chart (v.val,w)).val, hinc v.val v.property⟩
  have hc : Continuous coords := (F.box b').chart.symm.continuous.comp
    ((continuous_subtype_val.comp ((F.box b).chart.continuous.comp
      (continuous_subtype_val.prodMk continuous_const))).subtype_mk _)
  have hl (v : V) : F.stableLabel b' (coords v).2 = q := by
    have he : ((F.box b').chart (coords v)).val = ((F.box b).chart (v.val,w)).val :=
      congrArg Subtype.val ((F.box b').chart.apply_symm_apply _)
    rw [← F.stable_label b' (coords v).1 (coords v).2, he]
    exact F.stable_label b v.val w
  have hr : range (fun v : V ↦ (coords v).2) ⊆
      {t | F.stableLabel b' t = q} := by
    rintro _ ⟨v, rfl⟩
    exact hl v
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hV
  exact (stable_plaque_label_fiber_countable_g9 F b' q (hsep q)).isTotallyDisconnected
    _ hr (isPreconnected_range hc.snd) (mem_range_self z) (mem_range_self z')

/-- Near each box-overlap point, the transverse component of the box transition is independent of
the stable variable on a product neighborhood. (Hirsch–Pugh–Shub, §7 pp.115–116) -/
theorem boxTransition_local_product
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    (b b' : F.boxIndex) (z : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk 2)
    (hx : ((F.box b).chart (z,w)).val ∈ (F.box b').image) :
    ∃ (V : Set (FoliationCoordinateDisk s)) (W : Set (FoliationCoordinateDisk 2)),
      IsOpen V ∧ ∃ hz : z ∈ V, IsOpen W ∧ w ∈ W ∧
      ∃ hinc : ∀ v ∈ V, ∀ t ∈ W, ((F.box b).chart (v,t)).val ∈ (F.box b').image,
      ∀ v : V, ∀ t : W,
        ((F.box b').chart.symm ⟨((F.box b).chart (v.val,t.val)).val,
          hinc v.val v.property t.val t.property⟩).2 =
        ((F.box b').chart.symm ⟨((F.box b).chart (z,t.val)).val,
          hinc z hz t.val t.property⟩).2 := by
  let : LocallyConnectedSpace (FoliationCoordinateDisk s) := Metric.isOpen_ball.locallyConnectedSpace
  have hc : Continuous (fun p : FoliationCoordinateDisk s × FoliationCoordinateDisk 2 ↦
      ((F.box b).chart p).val) := continuous_subtype_val.comp (F.box b).chart.continuous
  have hn := ((F.box b').isOpen_image.preimage hc).mem_nhds hx
  obtain ⟨V₀, hV₀, W₀, hW₀, hprod⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨V, hVV, hVo, hz, hVc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance z V₀ hV₀
  obtain ⟨W, hWW, hWo, hw⟩ := mem_nhds_iff.mp hW₀
  have hi : ∀ v ∈ V, ∀ t ∈ W, ((F.box b).chart (v,t)).val ∈ (F.box b').image :=
    fun v hv t ht ↦ hprod ⟨hVV hv, hWW ht⟩
  refine ⟨V, W, hVo, hz, hWo, hw, hi, ?_⟩
  intro v t
  exact boxTransition_stable_constant F hsep b b' V hVc.isPreconnected v ⟨z,hz⟩
    t.val (fun v hv ↦ hi v hv t.val t.property)

@[simp] theorem transverseCoordinate_on_box
    (c : TransverseProjectiveChart F C)
    (z : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk 2) :
    c.transverseCoordinate F C ((F.box c.box).chart (z,w)).val = c.coordinate w := by
  classical
  simp [TransverseProjectiveChart.transverseCoordinate]

/-- An identity between transverse coordinates on an unstable plaque extends to an ambient germ at
the same point. (Ghys, §4 p.594) -/
theorem transverse_germ_of_plaque_germ
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    (c d : TransverseProjectiveChart F C)
    (z : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk 2)
    (hx : ((F.box c.box).chart (z,w)).val ∈ (F.box d.box).image)
    (g : ComplexProjectiveLine → ComplexProjectiveLine)
    (hg : ∀ᶠ t in 𝓝 w,
      d.transverseCoordinate F C ((F.box c.box).chart (z,t)).val = g (c.coordinate t)) :
    ∀ᶠ y in 𝓝 ((F.box c.box).chart (z,w)).val,
      d.transverseCoordinate F C y = g (c.transverseCoordinate F C y) := by
  classical
  obtain ⟨V, W, hVo, hz, hWo, hw, hi, he⟩ :=
    boxTransition_local_product F hsep c.box d.box z w hx
  have hbox : IsOpenEmbedding (fun p : FoliationCoordinateDisk s × FoliationCoordinateDisk 2 ↦
      ((F.box c.box).chart p).val) :=
    (F.box c.box).isOpen_image.isOpenEmbedding_subtypeVal.comp
      (F.box c.box).chart.isOpenEmbedding
  rw [← hbox.map_nhds_eq (z,w)]
  change ∀ᶠ p : FoliationCoordinateDisk s × FoliationCoordinateDisk 2 in 𝓝 (z,w),
    d.transverseCoordinate F C ((F.box c.box).chart p).val =
      g (c.transverseCoordinate F C ((F.box c.box).chart p).val)
  have hV : ∀ᶠ p : FoliationCoordinateDisk s × FoliationCoordinateDisk 2 in 𝓝 (z,w),
      p.1 ∈ V := continuousAt_fst.eventually (hVo.mem_nhds hz)
  have hW : ∀ᶠ p : FoliationCoordinateDisk s × FoliationCoordinateDisk 2 in 𝓝 (z,w),
      p.2 ∈ W := continuousAt_snd.eventually (hWo.mem_nhds hw)
  have hG : ∀ᶠ p : FoliationCoordinateDisk s × FoliationCoordinateDisk 2 in 𝓝 (z,w),
      d.transverseCoordinate F C ((F.box c.box).chart (z,p.2)).val = g (c.coordinate p.2) :=
    (show ContinuousAt Prod.snd (z,w) from continuousAt_snd).eventually hg
  filter_upwards [hV, hW, hG] with p hpV hpW hpG
  rw [transverseCoordinate_on_box]
  rw [← hpG]
  simp only [TransverseProjectiveChart.transverseCoordinate, dite_eq_left (hi p.1 hpV p.2 hpW),
    dite_eq_left (hi z hz p.2 hpW)]
  exact congrArg d.coordinate (he ⟨p.1,hpV⟩ ⟨p.2,hpW⟩)

/-- Every complex affine transformation is the restriction of a projective transformation to the
finite chart. -/
theorem affine_transformation_native_mobius (a : ComplexAffineTransformation) :
    ∃ g : ComplexMobiusTransformation, ∀ z : ℂ,
      g.apply (complexProjectiveLineFinite z) = complexProjectiveLineFinite (a.apply z) := by
  obtain ⟨g, hg⟩ := affine_transformation_mobius a
  refine ⟨mobiusGroupToComplexMobius g, ?_⟩
  intro z
  rw [mobiusGroupToComplexMobius_apply, complexProjectiveLineFinite_to_onePoint, hg]
  apply (OnePoint.equivProjectivization ℂ).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (complexProjectiveLineFinite_to_onePoint (a.apply z)).symm

/-- Two functions locally projective in the same affine leaf structure differ by a projective
transformation near the marked point. (Ghys, §§3–4 pp.590,594) -/
theorem projective_germ_of_common_affine_structure
    {L : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineStructure L) (k l : L → ComplexProjectiveLine) (p : L)
    (hk : ∃ c ∈ A.maximalAtlas L, p ∈ c.source ∧ ∃ g : ComplexMobiusTransformation,
      ∀ᶠ y in 𝓝 p, k y = g.apply (complexProjectiveLineFinite (c y)))
    (hl : ∃ c ∈ A.maximalAtlas L, p ∈ c.source ∧ ∃ g : ComplexMobiusTransformation,
      ∀ᶠ y in 𝓝 p, l y = g.apply (complexProjectiveLineFinite (c y))) :
    ∃ g : ComplexMobiusTransformation, ∀ᶠ y in 𝓝 p, l y = g.apply (k y) := by
  obtain ⟨c, hc, hpc, g, hg⟩ := hk
  obtain ⟨d, hd, hpd, h, hh⟩ := hl
  obtain ⟨r, hr, hpr⟩ := A.out.cover p
  obtain ⟨ac, hac⟩ := hc.2 r hr p ⟨hpr,hpc⟩
  obtain ⟨ad, had⟩ := hd.2 r hr p ⟨hpr,hpd⟩
  obtain ⟨gc, hgc⟩ := affine_transformation_native_mobius ac
  obtain ⟨gd, hgd⟩ := affine_transformation_native_mobius ad
  obtain ⟨mg, hmg⟩ := g.property
  obtain ⟨mh, hmh⟩ := h.property
  obtain ⟨mc, hmc⟩ := gc.property
  obtain ⟨md, hmd⟩ := gd.property
  refine ⟨ComplexMobiusTransformation.ofMatrix ((mh * md) * (mg * mc)⁻¹), ?_⟩
  filter_upwards [hg, hh, hac, had] with y hky hly hcy hdy
  rw [hly, hky, hcy, hdy, ← hgc, ← hgd]
  change h.val (gd.val _) = ((mh * md) * (mg * mc)⁻¹) • g.val (gc.val _)
  rw [hmh, hmd, hmg, hmc]
  simp [mul_smul]

/-- The condition that a transverse chart is locally projective in maximal coordinates of the
specified affine leaf family. -/
def TransverseChartAffineCompatible
    (affine : AffineUnstableLeafStructures F C) (c : TransverseProjectiveChart F C) : Prop :=
  ∀ x : M, ∀ z : F.ULeaf x,
    letI := C.charts (Quotient.mk F.unstablePartition x)
    z.val ∈ c.domain F C →
    ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C x),
      z ∈ b.source ∧ ∃ g : ComplexMobiusTransformation,
        ∀ᶠ w in 𝓝 z,
          w ∈ b.source ∧ w.val ∈ c.domain F C ∧
            c.transverseCoordinate F C w.val = g.apply (complexProjectiveLineFinite (b w))

/-- Transverse charts locally projective in the same affine leaf family have projective comparison
germs on their overlaps. (Ghys, §4 p.594 and §5 p.597) -/
theorem transverseCharts_compatible_of_affine
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    (affine : AffineUnstableLeafStructures F C) (c d : TransverseProjectiveChart F C)
    (hc : TransverseChartAffineCompatible F C affine c)
    (hd : TransverseChartAffineCompatible F C affine d) :
    TransverseProjectiveChartsCompatible F C c d := by
  intro x hx
  obtain ⟨hxbox, hxz, hxw⟩ := hx.1
  let z := ((F.box c.box).chart.symm ⟨x,hxbox⟩).1
  let w := ((F.box c.box).chart.symm ⟨x,hxbox⟩).2
  let x' := ((F.box c.box).chart (z,w)).val
  have hxx : x' = x := congrArg Subtype.val ((F.box c.box).chart.apply_symm_apply ⟨x,hxbox⟩)
  let := C.charts (Quotient.mk F.unstablePartition x')
  have hc' := hc x' (F.uPoint x') (by change x' ∈ c.domain F C; rw [hxx]; exact hx.1)
  have hd' := hd x' (F.uPoint x') (by change x' ∈ d.domain F C; rw [hxx]; exact hx.2)
  obtain ⟨g, hg⟩ := projective_germ_of_common_affine_structure
    (affine.atPoint F C x')
    (fun y : F.ULeaf x' ↦ c.transverseCoordinate F C y.val)
    (fun y : F.ULeaf x' ↦ d.transverseCoordinate F C y.val) (F.uPoint x')
    (by
      obtain ⟨b,hb,hzb,g,hg⟩ := hc'
      exact ⟨b,hb,hzb,g,hg.mono (fun _ h ↦ h.2.2)⟩)
    (by
      obtain ⟨b,hb,hzb,g,hg⟩ := hd'
      exact ⟨b,hb,hzb,g,hg.mono (fun _ h ↦ h.2.2)⟩)
  let p := unstablePlaqueCoordinateAt F c.box z w
  have hp : p w = F.uPoint x' := by
    apply Subtype.ext
    exact unstablePlaqueCoordinateAt_val F c.box z w w
  have hgp : ∀ᶠ t in 𝓝 w,
      d.transverseCoordinate F C ((F.box c.box).chart (z,t)).val = g.apply (c.coordinate t) := by
    have h := (p.continuousAt (show w ∈ p.source by rw [show p.source = univ from unstablePlaqueCoordinateAt_source F c.box z w]; trivial)).eventually
      (show ∀ᶠ y in 𝓝 (p w),
        d.transverseCoordinate F C y.val = g.apply (c.transverseCoordinate F C y.val) by
        rw [hp]
        exact hg)
    filter_upwards [h] with t ht
    simpa only [p, unstablePlaqueCoordinateAt_val, transverseCoordinate_on_box] using ht
  refine ⟨g, ?_⟩
  rw [← hxx]
  exact transverse_germ_of_plaque_germ F C hsep c d z w
    (by rw [show ((F.box c.box).chart (z,w)).val = x from hxx]; exact hx.2.choose)
    g.apply hgp

/-- The point-preserving homeomorphism between equal unstable quotient classes is biholomorphic in
their complex atlases. -/
theorem unstableLabelHomeomorph_smooth
    (q q' : Quotient F.unstablePartition) (h : q = q') :
    letI := F.unstableTopology q; letI := F.unstableTopology q'
    letI := C.charts q; letI := C.charts q'
    ContMDiff (complexModel 1) (complexModel 1) ∞ (unstableLabelHomeomorph F q q' h) ∧
      ContMDiff (complexModel 1) (complexModel 1) ∞ (unstableLabelHomeomorph F q q' h).symm := by
  subst q'
  let := F.unstableTopology q
  let := C.charts q
  exact ⟨contMDiff_id, contMDiff_id⟩

/-- Holomorphic full-box plaque transport remains holomorphic in both directions when expressed on
quotient-labeled intrinsic leaves. (Ghys, §2 pp.588–589 and §4 p.594) -/
theorem labeledPlaqueTransport_holomorphic
    (b : F.boxIndex) (z z' : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk 2)
    (h : letI := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z,w)).val)
      letI := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z',w)).val)
      let H := (fullBoxPlaqueTransport F b z z' w).map
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ H H.source ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ H.symm H.target) :
    letI := F.unstableTopology (F.unstableLabel b z)
    letI := F.unstableTopology (F.unstableLabel b z')
    letI := C.charts (F.unstableLabel b z)
    letI := C.charts (F.unstableLabel b z')
    let H := (unstablePlaqueCoordinate F b z).symm.trans (unstablePlaqueCoordinate F b z')
    ContMDiffOn (complexModel 1) (complexModel 1) ∞ H H.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ H.symm H.target := by
  let := F.unstableTopology (F.unstableLabel b z)
  let := F.unstableTopology (F.unstableLabel b z')
  let := C.charts (F.unstableLabel b z)
  let := C.charts (F.unstableLabel b z')
  let := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z,w)).val)
  let := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z',w)).val)
  let E := unstableLabelHomeomorph F _ _ (F.unstable_label b z w).symm
  let E' := unstableLabelHomeomorph F _ _ (F.unstable_label b z' w).symm
  have he := unstableLabelHomeomorph_smooth F C _ _ (F.unstable_label b z w).symm
  have he' := unstableLabelHomeomorph_smooth F C _ _ (F.unstable_label b z' w).symm
  let H := (fullBoxPlaqueTransport F b z z' w).map
  let K := (unstablePlaqueCoordinate F b z).symm.trans (unstablePlaqueCoordinate F b z')
  have hforward : MapsTo E K.source H.source := by
    intro v hv
    simpa [E, H, K, fullBoxPlaqueTransport, unstablePlaqueCoordinateAt,
      OpenPartialHomeomorph.trans_source] using hv
  have hbackward : MapsTo E' K.target H.target := by
    intro v hv
    simpa [E', H, K, fullBoxPlaqueTransport, unstablePlaqueCoordinateAt,
      OpenPartialHomeomorph.trans_target] using hv
  constructor
  · have hh := he'.2.comp_contMDiffOn (h.1.comp he.1.contMDiffOn hforward)
    apply hh.congr
    intro v hv
    simp [fullBoxPlaqueTransport, unstablePlaqueCoordinateAt]
  · have hh := he.2.comp_contMDiffOn (h.2.comp he'.1.contMDiffOn hbackward)
    apply hh.congr
    intro v hv
    simp [fullBoxPlaqueTransport, unstablePlaqueCoordinateAt]

/-- A complete affine coordinate on one unstable plaque determines a transverse projective chart on
the full box when stable plaque transports are holomorphic. (Ghys, §4 p.594 and §5 p.597) -/
theorem transverseChart_of_complete_coordinate
    (b : F.boxIndex) (z₀ : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk 2)
    (e : letI := F.unstableTopology (F.unstableLabel b z₀)
      letI := C.charts (F.unstableLabel b z₀)
      Diffeomorph (complexModel 1) 𝓘(ℂ)
        (IntrinsicFoliationLeaf F.unstablePartition (F.unstableLabel b z₀)) ℂ ∞)
    (hhol : ∀ z : FoliationCoordinateDisk s,
      letI := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z,w₀)).val)
      letI := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z₀,w₀)).val)
      let H := (fullBoxPlaqueTransport F b z z₀ w₀).map
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ H H.source ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ H.symm H.target) :
    ∃ c : TransverseProjectiveChart F C,
      c.box = b ∧ c.stableDomain = ⊤ ∧ c.coordinate.source = univ ∧
      ∀ w : FoliationCoordinateDisk 2,
        c.coordinate w = complexProjectiveLineFinite
          (e ⟨((F.box b).chart (z₀,w)).val, F.unstable_label b z₀ w⟩) := by
  let := F.unstableTopology (F.unstableLabel b z₀)
  let := C.charts (F.unstableLabel b z₀)
  obtain ⟨B,hBs,hBt,hBval,hBhol,hBinv⟩ := projective_affine_coordinate_chart e 1
  have hB (v) : B v = complexProjectiveLineFinite (e v) := by simpa using hBval v
  let p₀ := unstablePlaqueCoordinate F b z₀
  let c := p₀.trans B
  have hcs : c.source = univ := by simp [c, p₀, unstablePlaqueCoordinate, hBs]
  have hc : ∀ z ∈ (⊤ : Opens (FoliationCoordinateDisk s)),
      letI := F.unstableTopology (F.unstableLabel b z)
      letI := C.charts (F.unstableLabel b z)
      let H := unstablePlaqueProjectiveCoordinate F b z c
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ H H.source ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ H.symm H.target := by
    intro z hz
    let := F.unstableTopology (F.unstableLabel b z)
    let := C.charts (F.unstableLabel b z)
    have hK := labeledPlaqueTransport_holomorphic F C b z z₀ w₀ (hhol z)
    let K := (unstablePlaqueCoordinate F b z).symm.trans p₀
    dsimp only [unstablePlaqueProjectiveCoordinate, c]
    rw [← OpenPartialHomeomorph.trans_assoc]
    constructor
    · exact hBhol.comp (hK.1.mono inter_subset_left) (fun v hv ↦ hv.2)
    · exact hK.2.comp (hBinv.mono inter_subset_left) (fun v hv ↦ hv.2)
  let out := transverseProjectiveChartOfCoordinate F C b ⊤ c hc
  refine ⟨out, rfl, rfl, hcs, ?_⟩
  intro w
  exact hB (p₀ w)

/-- The condition that a transverse coordinate has a projective comparison germ with a maximal
affine chart at a point of an intrinsic unstable leaf. -/
def leafAffineProjectiveGerm
    (affine : AffineUnstableLeafStructures F C) (c : TransverseProjectiveChart F C)
    (q : Quotient F.unstablePartition) (p : IntrinsicFoliationLeaf F.unstablePartition q) : Prop :=
  letI := F.unstableTopology q; letI := C.charts q
  ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.structureAt q),
    p ∈ b.source ∧ ∃ g : ComplexMobiusTransformation,
      ∀ᶠ w in 𝓝 p,
        w ∈ b.source ∧ w.val ∈ c.domain F C ∧
          c.transverseCoordinate F C w.val = g.apply (complexProjectiveLineFinite (b w))

/-- The affine-projective germ condition is preserved under equal leaf labels and equal ambient
points. -/
theorem leafAffineProjectiveGerm_relabel
    (affine : AffineUnstableLeafStructures F C) (c : TransverseProjectiveChart F C)
    (q q' : Quotient F.unstablePartition) (hq : q = q')
    (p : IntrinsicFoliationLeaf F.unstablePartition q)
    (p' : IntrinsicFoliationLeaf F.unstablePartition q') (hp : p.val = p'.val)
    (h : leafAffineProjectiveGerm F C affine c q p) :
    leafAffineProjectiveGerm F C affine c q' p' := by
  subst q'
  have hpp : p = p' := Subtype.ext hp
  subst p'
  exact h

/-- Transverse affine compatibility follows from the affine-projective germ condition at each
canonical leaf point in the chart domain. -/
theorem transverseChartAffineCompatible_of_centers
    (affine : AffineUnstableLeafStructures F C) (c : TransverseProjectiveChart F C)
    (h : ∀ x ∈ c.domain F C,
      leafAffineProjectiveGerm F C affine c (Quotient.mk F.unstablePartition x) (F.uPoint x)) :
    TransverseChartAffineCompatible F C affine c := by
  intro x p hp
  exact leafAffineProjectiveGerm_relabel F C affine c _ _ p.property
    (F.uPoint p.val) p rfl (h p.val hp)

/-- A scalar chart transported by the point-preserving identity between equal unstable leaf classes. -/
def relabeledScalarChart (q q' : Quotient F.unstablePartition) (h : q = q')
    (b : letI := F.unstableTopology q
      OpenPartialHomeomorph (IntrinsicFoliationLeaf F.unstablePartition q) ℂ) :
    letI := F.unstableTopology q'
    OpenPartialHomeomorph (IntrinsicFoliationLeaf F.unstablePartition q') ℂ :=
  letI := F.unstableTopology q
  letI := F.unstableTopology q'
  (unstableLabelHomeomorph F q q' h).symm.toOpenPartialHomeomorph.trans b

theorem relabeledScalarChart_maximal
    (affine : AffineUnstableLeafStructures F C)
    (q q' : Quotient F.unstablePartition) (h : q = q')
    (b : letI := F.unstableTopology q
      OpenPartialHomeomorph (IntrinsicFoliationLeaf F.unstablePartition q) ℂ)
    (hb : letI := F.unstableTopology q; letI := C.charts q
      b ∈ ComplexAffineStructure.maximalAtlas _ (affine.structureAt q)) :
    letI := F.unstableTopology q'; letI := C.charts q'
    relabeledScalarChart F q q' h b ∈ ComplexAffineStructure.maximalAtlas _ (affine.structureAt q') := by
  subst q'
  let := F.unstableTopology q
  let := C.charts q
  simpa [relabeledScalarChart, unstableLabelHomeomorph] using hb

/-- The condition that full-box stable plaque transports have projective germs in maximal affine
endpoint coordinates. (Ghys, Prop.4.1) -/
def FullBoxProjectiveHolonomy (affine : AffineUnstableLeafStructures F C) : Prop :=
  ∀ (b : F.boxIndex) (z z' : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk 2),
    let x := ((F.box b).chart (z,w)).val
    let y := ((F.box b).chart (z',w)).val
    letI := C.charts (Quotient.mk F.unstablePartition x)
    letI := C.charts (Quotient.mk F.unstablePartition y)
    ∀ (c : OpenPartialHomeomorph (F.ULeaf x) ℂ)
      (d : OpenPartialHomeomorph (F.ULeaf y) ℂ),
      c ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C x) →
      d ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C y) →
      F.uPoint x ∈ c.source → F.uPoint y ∈ d.source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ v in 𝓝 (F.uPoint x),
          v ∈ (fullBoxPlaqueTransport F b z z' w).map.source ∧ v ∈ c.source ∧
          (fullBoxPlaqueTransport F b z z' w).map v ∈ d.source ∧
          complexProjectiveLineFinite (d ((fullBoxPlaqueTransport F b z z' w).map v)) =
            g.apply (complexProjectiveLineFinite (c v))

/-- A transverse chart with full stable and transverse domains has domain equal to its box image. -/
theorem transverseChart_full_domain
    (c : TransverseProjectiveChart F C) (hs : c.stableDomain = ⊤)
    (hu : c.coordinate.source = univ) : c.domain F C = (F.box c.box).image := by
  ext x
  constructor
  · rintro ⟨hx,_⟩
    exact hx
  · intro hx
    exact ⟨hx, by rw [hs]; trivial, by rw [hu]; trivial⟩

/-- A full-box transverse coordinate extending a maximal affine reference coordinate is locally
projective in the same affine family when full-box holonomy is projective. (Ghys, Prop.4.1 p.593
and §4 p.594) -/
theorem transverseChart_affineCompatible_of_holonomy
    (affine : AffineUnstableLeafStructures F C) (hproj : FullBoxProjectiveHolonomy F C affine)
    (c : TransverseProjectiveChart F C) (z₀ : FoliationCoordinateDisk s)
    (e : letI := F.unstableTopology (F.unstableLabel c.box z₀)
      letI := C.charts (F.unstableLabel c.box z₀)
      Diffeomorph (complexModel 1) 𝓘(ℂ)
        (IntrinsicFoliationLeaf F.unstablePartition (F.unstableLabel c.box z₀)) ℂ ∞)
    (he : letI := F.unstableTopology (F.unstableLabel c.box z₀)
      letI := C.charts (F.unstableLabel c.box z₀)
      e.toHomeomorph.toOpenPartialHomeomorph ∈ ComplexAffineStructure.maximalAtlas _
        (affine.structureAt (F.unstableLabel c.box z₀)))
    (hs : c.stableDomain = ⊤) (hu : c.coordinate.source = univ)
    (hc : ∀ w : FoliationCoordinateDisk 2, c.coordinate w = complexProjectiveLineFinite
      (e ⟨((F.box c.box).chart (z₀,w)).val, F.unstable_label c.box z₀ w⟩)) :
    TransverseChartAffineCompatible F C affine c := by
  apply transverseChartAffineCompatible_of_centers F C affine c
  intro x hx
  have hxbox := (transverseChart_full_domain F C c hs hu).symm ▸ hx
  let z := ((F.box c.box).chart.symm ⟨x,hxbox⟩).1
  let w := ((F.box c.box).chart.symm ⟨x,hxbox⟩).2
  let x' := ((F.box c.box).chart (z,w)).val
  let y := ((F.box c.box).chart (z₀,w)).val
  have hxx : x' = x := congrArg Subtype.val ((F.box c.box).chart.apply_symm_apply ⟨x,hxbox⟩)
  let := F.unstableTopology (F.unstableLabel c.box z₀)
  let := C.charts (F.unstableLabel c.box z₀)
  let := C.charts (Quotient.mk F.unstablePartition x')
  let := C.charts (Quotient.mk F.unstablePartition y)
  let d := relabeledScalarChart F _ _ (F.unstable_label c.box z₀ w).symm
    e.toHomeomorph.toOpenPartialHomeomorph
  have hd : d ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C y) :=
    relabeledScalarChart_maximal F C affine _ _ _ _ he
  have hds : d.source = univ := by simp [d, relabeledScalarChart]
  obtain ⟨b,hb,hpb⟩ := (affine.atPoint F C x').out.cover (F.uPoint x')
  have hbm : b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C x') :=
    ⟨(affine.atPoint F C x').out.holomorphic b hb,
      fun b' hb' ↦ (affine.atPoint F C x').out.compatible b' hb' b hb⟩
  obtain ⟨g,hg⟩ := hproj c.box z z₀ w b d hbm hd hpb (by rw [hds]; trivial)
  have hresult : leafAffineProjectiveGerm F C affine c
      (Quotient.mk F.unstablePartition x') (F.uPoint x') := by
    refine ⟨b,hbm,hpb,g,?_⟩
    filter_upwards [hg] with v hv
    let H := fullBoxPlaqueTransport F c.box z z₀ w
    obtain ⟨t,ht⟩ := H.source_in_plaque v hv.1
    have hvpoint : v.val = ((F.box c.box).chart (z,t)).val := ht.symm
    have hHpoint : (H.map v).val = ((F.box c.box).chart (z₀,t)).val :=
      H.coordinate_map v t hv.1 ht
    have hdval : d (H.map v) = e
        ⟨((F.box c.box).chart (z₀,t)).val, F.unstable_label c.box z₀ t⟩ := by
      apply congrArg e
      apply Subtype.ext
      simpa [d, relabeledScalarChart, unstableLabelHomeomorph_val] using hHpoint
    refine ⟨hv.2.1, ?_, ?_⟩
    · rw [transverseChart_full_domain F C c hs hu, hvpoint]
      exact ((F.box c.box).chart (z,t)).property
    · rw [hvpoint, transverseCoordinate_on_box, hc, ← hdval]
      exact hv.2.2.2
  exact leafAffineProjectiveGerm_relabel F C affine c _ _
    (congrArg (Quotient.mk F.unstablePartition) hxx) (F.uPoint x') (F.uPoint x) hxx hresult

/-- The condition that every full-box plaque transport is holomorphic in both directions. -/
def FullBoxHolomorphic : Prop :=
  ∀ (b : F.boxIndex) (z z' : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk 2),
    letI := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z,w)).val)
    letI := C.charts (Quotient.mk F.unstablePartition ((F.box b).chart (z',w)).val)
    let H := (fullBoxPlaqueTransport F b z z' w).map
    ContMDiffOn (complexModel 1) (complexModel 1) ∞ H H.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ H.symm H.target

/-- Complete affine unstable leaves with holomorphic and projective stable plaque transports
determine a covering transverse projective atlas compatible with the affine family. (Ghys,
Prop.4.1 p.593 and §5 p.597) -/
theorem transverseProjectiveAtlas_of_complete_affine_holonomy
    (hsep : ∀ q : Quotient F.stablePartition,
      letI := F.stableTopology q
      SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
    (affine : AffineUnstableLeafStructures F C)
    (hcomplete : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q; letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q))
    (hhol : FullBoxHolomorphic F C) (hproj : FullBoxProjectiveHolonomy F C affine) :
    ∃ atlas : TransverseProjectiveAtlas F C,
      ∀ c ∈ atlas.charts, TransverseChartAffineCompatible F C affine c := by
  classical
  have hchart (b : F.boxIndex) : ∃ c : TransverseProjectiveChart F C,
      c.box = b ∧ c.stableDomain = ⊤ ∧ c.coordinate.source = univ ∧
      TransverseChartAffineCompatible F C affine c := by
    let z₀ : FoliationCoordinateDisk s := ⟨0,by simp⟩
    let w₀ : FoliationCoordinateDisk 2 := ⟨0,by simp⟩
    let q := F.unstableLabel b z₀
    let := F.unstableTopology q
    let := C.charts q
    obtain ⟨e,he⟩ := (hcomplete q).2
    have hemax : e.toHomeomorph.toOpenPartialHomeomorph ∈
        ComplexAffineStructure.maximalAtlas _ (affine.structureAt q) := by
      refine ⟨⟨e.contMDiff.contMDiffOn,e.symm.contMDiff.contMDiffOn⟩, ?_⟩
      intro c hc x hx
      exact he c hc x hx.1
    obtain ⟨c,hcb,hs,hu,hc⟩ := transverseChart_of_complete_coordinate F C b z₀ w₀ e
      (fun z ↦ hhol b z z₀ w₀)
    refine ⟨c,hcb,hs,hu,?_⟩
    subst b
    exact transverseChart_affineCompatible_of_holonomy F C affine hproj c z₀ e hemax hs hu hc
  let atlas : TransverseProjectiveAtlas F C := {
    charts := {c | TransverseChartAffineCompatible F C affine c}
    cover := by
      intro x
      obtain ⟨b,hb⟩ := F.cover x
      obtain ⟨c,hcb,hs,hu,hc⟩ := hchart b
      refine ⟨c,hc,?_⟩
      rw [transverseChart_full_domain F C c hs hu, hcb]
      exact hb
    compatible := fun c hc d hd ↦ transverseCharts_compatible_of_affine F C hsep affine c d hc hd }
  exact ⟨atlas, fun _ hc ↦ hc⟩

/-- The condition that a pointed intrinsic leaf map has projective germs in every pair of maximal
affine endpoint coordinates. -/
def PointedAffineProjective (affine : AffineUnstableLeafStructures F C)
    {x y : M} (H : PointedLeafHomeomorph F x y) : Prop :=
  letI := C.charts (Quotient.mk F.unstablePartition x)
  letI := C.charts (Quotient.mk F.unstablePartition y)
  ∀ (c : OpenPartialHomeomorph (F.ULeaf x) ℂ) (e : OpenPartialHomeomorph (F.ULeaf y) ℂ),
    c ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C x) →
    e ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C y) →
    F.uPoint x ∈ c.source → F.uPoint y ∈ e.source →
    ∃ g : ComplexMobiusTransformation, ∀ᶠ z in 𝓝 (F.uPoint x),
      z ∈ H.map.source ∧ z ∈ c.source ∧ H.map z ∈ e.source ∧
        complexProjectiveLineFinite (e (H.map z)) = g.apply (complexProjectiveLineFinite (c z))

/-- Rebasing equal endpoints preserves the affine-projective germ condition. -/
theorem pointedAffineProjective_rebase
    (affine : AffineUnstableLeafStructures F C) {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x = x') (hy : y = y') :
    PointedAffineProjective F C affine (rebasePlaqueTransport F e hx hy).toPointedLeafHomeomorph ↔
      PointedAffineProjective F C affine e.toPointedLeafHomeomorph := by
  subst x'
  subst y'
  rfl

/-- Projective holonomy along every stable path implies projective holonomy for every full-box
plaque transport. (Ghys, Prop.4.1 p.593) -/
theorem fullBoxProjectiveHolonomy_of_paths
    (affine : AffineUnstableLeafStructures F C)
    (hpath : ∀ (q : Quotient F.stablePartition)
      (x y : IntrinsicFoliationLeaf F.stablePartition q) (γ : Path x y)
      (H : PathHolonomyRepresentative F γ 0 1),
      PointedAffineProjective F C affine H.toPointedLeafHomeomorph) :
    FullBoxProjectiveHolonomy F C affine := by
  intro b z z' w
  have hh := hpath _ _ _ (stableBoxPath F b z z' w) (fullBoxPathHolonomy F b z z' w)
  exact (pointedAffineProjective_rebase F C affine (fullBoxPlaqueTransport F b z z' w)
    (congrArg Subtype.val (stableBoxPath F b z z' w).source).symm
    (congrArg Subtype.val (stableBoxPath F b z z' w).target).symm).mp hh

end HolomorphicAnosov.Ghys

