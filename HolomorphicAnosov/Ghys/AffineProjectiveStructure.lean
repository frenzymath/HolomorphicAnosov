import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Order.Filter.Germ.Basic

/-! This file defines affine and projective structures on complex curves as equivalence classes of
holomorphic atlases with compatible transition germs. It also defines transverse projective
structures and continuity of unstable-leaf affine structures along stable holonomy. (Ghys, §3,
p.590; §4, pp.593–594; §5, p.597; Demailly, V §15.A, p.277) -/

noncomputable section

open Set Filter _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov.Ghys

universe u v

/-- A complex affine transformation consists of a nonzero slope and a translation. (Ghys, §3, p.590) -/
structure ComplexAffineTransformation where
  slope : ℂ
  slope_ne_zero : slope ≠ 0
  translation : ℂ

/-- The affine map `z ↦ a.slope * z + a.translation`. (Ghys, §3, p.590) -/
def ComplexAffineTransformation.apply (a : ComplexAffineTransformation) (z : ℂ) : ℂ :=
  a.slope * z + a.translation

variable (L : Type u) [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]

/-- A scalar chart is holomorphic when its forward and inverse maps are complex smooth on their
domains. (Ghys, §3, p.590) -/
def IsHolomorphicScalarChart (c : OpenPartialHomeomorph L ℂ) : Prop :=
  ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ c c.source ∧
    ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ c.symm c.target

/-- Two scalar charts are affine compatible when their transition germ at each overlap point is an
invertible affine map. (Ghys, §3, p.590) -/
def AffineChartsCompatible (c d : OpenPartialHomeomorph L ℂ) : Prop :=
  ∀ x ∈ c.source ∩ d.source, ∃ a : ComplexAffineTransformation,
    ∀ᶠ y in 𝓝 x, d y = a.apply (c y)

/-- A covering holomorphic atlas with affine transition germs. (Ghys, §3, p.590) -/
structure ComplexAffineAtlas where
  charts : Set (OpenPartialHomeomorph L ℂ)
  cover : ∀ x : L, ∃ c ∈ charts, x ∈ c.source
  holomorphic : ∀ c ∈ charts, IsHolomorphicScalarChart L c
  compatible : ∀ c ∈ charts, ∀ d ∈ charts, AffineChartsCompatible L c d

/-- Two affine atlases are equivalent when every chart of one is affine compatible with every chart
of the other. (Ghys, §3, p.590) -/
def AffineAtlasesEquivalent (A B : ComplexAffineAtlas L) : Prop :=
  ∀ c ∈ A.charts, ∀ d ∈ B.charts, AffineChartsCompatible L c d

/-- Compatibility of the union is an equivalence relation on covering affine atlases. (Ghys, §3,
p.590) -/
theorem affineAtlasesEquivalent_equivalence :
    Equivalence (AffineAtlasesEquivalent L) := by
  classical
  constructor
  · intro A c hc d hd
    exact A.compatible c hc d hd
  · intro A B h c hc d hd x hx
    obtain ⟨a, ha⟩ := h d hd c hc x ⟨hx.2, hx.1⟩
    refine ⟨{ slope := a.slope⁻¹,
               slope_ne_zero := inv_ne_zero a.slope_ne_zero,
               translation := -a.slope⁻¹ * a.translation }, ?_⟩
    filter_upwards [ha] with y hy
    dsimp [ComplexAffineTransformation.apply]
    rw [hy]
    dsimp [ComplexAffineTransformation.apply]
    field_simp [a.slope_ne_zero]
    ring
  · intro A B C hAB hBC c hc d hd x hx
    obtain ⟨b, hb, hxb⟩ := B.cover x
    obtain ⟨a, ha⟩ := hAB c hc b hb x ⟨hx.1, hxb⟩
    obtain ⟨e, he⟩ := hBC b hb d hd x ⟨hxb, hx.2⟩
    refine ⟨{ slope := e.slope * a.slope,
               slope_ne_zero := mul_ne_zero e.slope_ne_zero a.slope_ne_zero,
               translation := e.slope * a.translation + e.translation }, ?_⟩
    filter_upwards [ha, he] with y hay hey
    dsimp [ComplexAffineTransformation.apply] at hay hey ⊢
    rw [hey, hay]
    ring

/-- The setoid on affine atlases defined by compatibility of their union. (Ghys, §3, p.590) -/
def complexAffineAtlasSetoid : Setoid (ComplexAffineAtlas L) where
  r := AffineAtlasesEquivalent L
  iseqv := affineAtlasesEquivalent_equivalence L

/-- A complex affine structure is an equivalence class of covering holomorphic atlases with affine
transition germs. (Ghys, §3, p.590) -/
def ComplexAffineStructure := Quotient (complexAffineAtlasSetoid L)

/-- The maximal affine atlas consists of holomorphic scalar charts compatible with every chart of a
representative atlas. (Ghys, §3, p.590) -/
def ComplexAffineStructure.maximalAtlas (A : ComplexAffineStructure L) :
    Set (OpenPartialHomeomorph L ℂ) :=
  {c | IsHolomorphicScalarChart L c ∧
    ∀ d ∈ A.out.charts, AffineChartsCompatible L d c}

/-- The curve admits a biholomorphism onto the complex plane whose coordinate expression in each
affine chart is locally affine. (Ghys, §3, p.590) -/
def AffinelyBiholomorphicToPlane (A : ComplexAffineStructure L) : Prop :=
  ∃ e : Diffeomorph (complexModel 1) 𝓘(ℂ) L ℂ ∞,
    ∀ c ∈ A.out.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, e y = a.apply (c y)

/-- An affine structure is complete when its curve is simply connected and affinely biholomorphic to
the entire complex plane. (Ghys, §3, p.590) -/
def ComplexAffineStructure.Complete (A : ComplexAffineStructure L) : Prop :=
  SimplyConnectedSpace L ∧ AffinelyBiholomorphicToPlane L A

/-- The affine ratio `(c x - c y) / (c x - c z)` of three points in a scalar coordinate. (Ghys, §3,
p.590) -/
def affineCoordinateRatio (c : OpenPartialHomeomorph L ℂ) (x y z : L) : ℂ :=
  (c x - c y) / (c x - c z)

/-- The germ of a map at `x`, with respect to the neighborhood filter `𝓝 x`. (Ghys, §4, pp.593–594;
§5, p.597) -/
abbrev LocalMapGerm (X : Type u) [TopologicalSpace X] (x : X) (Y : Type v) :=
  Filter.Germ (𝓝 x) Y

/-- A Möbius transformation is a permutation of the complex projective line induced by a nonsingular
complex matrix. (Ghys, §4, pp.593–594; §5, p.597; Demailly, V §15.A, p.277) -/
def ComplexMobiusTransformation :=
  {e : Equiv.Perm (Projectivization ℂ (Fin 2 → ℂ)) //
    ∃ g : GL (Fin 2) ℂ, ∀ p, e p = g • p}

/-- The action of a Möbius transformation on the complex projective line. (Demailly, V §15.A, p.277;
Ghys, §4, pp.593–594) -/
def ComplexMobiusTransformation.apply (g : ComplexMobiusTransformation)
    (p : Projectivization ℂ (Fin 2 → ℂ)) : Projectivization ℂ (Fin 2 → ℂ) :=
  g.val p

/-- The projective transformation induced by a nonsingular complex matrix. (Ghys, §5, p.597) -/
def ComplexMobiusTransformation.ofMatrix (g : GL (Fin 2) ℂ) :
    ComplexMobiusTransformation :=
  ⟨MulAction.toPerm g, ⟨g, fun _ ↦ rfl⟩⟩

/-- The global scalar coordinate on `ComplexModel 1`, given by evaluation at its unique index.
(Ghys, §3, p.590) -/
def canonicalPlaneCoordinate : OpenPartialHomeomorph (ComplexModel 1) ℂ :=
  (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).toOpenPartialHomeomorph

/-- The canonical plane coordinate has full source, is holomorphic, and is affine compatible with
itself. (Ghys, §3, p.590) -/
theorem canonicalPlaneCoordinate_properties :
    (∀ x : ComplexModel 1, x ∈ canonicalPlaneCoordinate.source) ∧
    IsHolomorphicScalarChart (ComplexModel 1) canonicalPlaneCoordinate ∧
    AffineChartsCompatible (ComplexModel 1) canonicalPlaneCoordinate canonicalPlaneCoordinate := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [canonicalPlaneCoordinate]
  · constructor
    · exact (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).contMDiffOn
    · exact (ContinuousLinearMap.pi (fun _ : Fin 1 ↦ ContinuousLinearMap.id ℂ ℂ)).contMDiffOn
  · intro x hx
    refine ⟨⟨1, by norm_num, 0⟩, ?_⟩
    filter_upwards [] with y
    simp [ComplexAffineTransformation.apply, canonicalPlaneCoordinate]


/-- The singleton affine atlas consisting of the global scalar coordinate on the complex plane.
(Ghys, §3, p.590) -/
def canonicalPlaneAffineAtlas : ComplexAffineAtlas (ComplexModel 1) where
  charts := {canonicalPlaneCoordinate}
  cover := fun x ↦ ⟨canonicalPlaneCoordinate, rfl, canonicalPlaneCoordinate_properties.1 x⟩
  holomorphic := fun c hc ↦ by
    subst c
    exact canonicalPlaneCoordinate_properties.2.1
  compatible := fun c hc d hd ↦ by
    subst c
    subst d
    exact canonicalPlaneCoordinate_properties.2.2

/-- The affine structure represented by the canonical global coordinate atlas of the complex plane.
(Ghys, §3, p.590) -/
def canonicalPlaneAffineStructure : ComplexAffineStructure (ComplexModel 1) :=
  Quotient.mk (complexAffineAtlasSetoid (ComplexModel 1)) canonicalPlaneAffineAtlas

/-- The maximal affine atlas equals the set of holomorphic charts compatible with any chosen
representative of the structure. (Ghys, §3, p.590) -/
theorem ComplexAffineStructure.maximalAtlas_eq_of_representative
    (A : ComplexAffineAtlas L) :
    ComplexAffineStructure.maximalAtlas L
      (Quotient.mk (complexAffineAtlasSetoid L) A : ComplexAffineStructure L) =
      {c | IsHolomorphicScalarChart L c ∧
        ∀ d ∈ A.charts, AffineChartsCompatible L d c} := by
  classical
  let Q : ComplexAffineStructure L := Quotient.mk (complexAffineAtlasSetoid L) A
  have hQA : AffineAtlasesEquivalent L Q.out A :=
    Quotient.exact (Quotient.out_eq Q)
  have ht (B D : ComplexAffineAtlas L) (hDB : AffineAtlasesEquivalent L D B)
      (c : OpenPartialHomeomorph L ℂ)
      (hc : ∀ b ∈ B.charts, AffineChartsCompatible L b c) :
      ∀ d ∈ D.charts, AffineChartsCompatible L d c := by
    intro d hd x hx
    obtain ⟨b, hb, hxb⟩ := B.cover x
    obtain ⟨a, ha⟩ := hDB d hd b hb x ⟨hx.1, hxb⟩
    obtain ⟨e, he⟩ := hc b hb x ⟨hxb, hx.2⟩
    refine ⟨⟨e.slope * a.slope, mul_ne_zero e.slope_ne_zero a.slope_ne_zero,
      e.slope * a.translation + e.translation⟩, ?_⟩
    filter_upwards [ha, he] with y hay hey
    dsimp [ComplexAffineTransformation.apply] at hay hey ⊢
    rw [hey, hay]
    ring
  ext c
  change (_ ∧ ∀ d ∈ Q.out.charts, AffineChartsCompatible L d c) ↔ _
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, ht Q.out A ((affineAtlasesEquivalent_equivalence L).symm hQA) c h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, ht A Q.out hQA c h⟩

omit [ChartedSpace (ComplexModel 1) L] in
/-- Affine ratios of distinct triples agree in compatible charts on a sufficiently small common
neighborhood. (Ghys, §3, p.590) -/
theorem affineCoordinateRatio_locally_chart_independent
    (c d : OpenPartialHomeomorph L ℂ) (hcd : AffineChartsCompatible L c d)
    (p : L) (hp : p ∈ c.source ∩ d.source) :
    ∃ U ∈ 𝓝 p, U ⊆ c.source ∩ d.source ∧
      ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x ≠ y → x ≠ z → y ≠ z →
        affineCoordinateRatio L c x y z = affineCoordinateRatio L d x y z := by
  obtain ⟨a, ha⟩ := hcd p hp
  let U := {y | d y = a.apply (c y)} ∩ (c.source ∩ d.source)
  have hU : U ∈ 𝓝 p := ha.and (c.open_source.inter d.open_source |>.mem_nhds hp)
  refine ⟨U, hU, fun x hx ↦ hx.2, ?_⟩
  intro x hx y hy z hz hxy hxz hyz
  dsimp [affineCoordinateRatio]
  rw [hx.1, hy.1, hz.1]
  dsimp [ComplexAffineTransformation.apply]
  have hn : c x - c z ≠ 0 := sub_ne_zero.mpr (fun h ↦
    hxz (c.injOn hx.2.1 hz.2.1 h))
  have hnum : a.slope * c x + a.translation -
      (a.slope * c y + a.translation) = a.slope * (c x - c y) := by ring
  have hden : a.slope * c x + a.translation -
      (a.slope * c z + a.translation) = a.slope * (c x - c z) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ a.slope_ne_zero]

/-- A projective chart is holomorphic when its forward and inverse maps are complex smooth on their
domains. (Ghys, §4, pp.593–594; Demailly, V §15.A, p.277) -/
def IsHolomorphicProjectiveChart (c : OpenPartialHomeomorph L ComplexProjectiveLine) :
    Prop :=
  ContMDiffOn (complexModel 1) (complexModel 1) ∞ c c.source ∧
    ContMDiffOn (complexModel 1) (complexModel 1) ∞ c.symm c.target

/-- Two projective charts are compatible when their transition germ at each overlap point is induced
by a Möbius transformation. (Ghys, §4, pp.593–594; §5, p.597) -/
def ProjectiveChartsCompatible (c d : OpenPartialHomeomorph L ComplexProjectiveLine) :
    Prop :=
  ∀ x ∈ c.source ∩ d.source, ∃ g : ComplexMobiusTransformation,
    ∀ᶠ y in 𝓝 x, d y = g.apply (c y)

/-- A covering holomorphic atlas with Möbius transition germs. (Ghys, §4, pp.593–594; §5, p.597;
Demailly, V §15.A, p.277) -/
structure ComplexProjectiveAtlas where
  charts : Set (OpenPartialHomeomorph L ComplexProjectiveLine)
  cover : ∀ x : L, ∃ c ∈ charts, x ∈ c.source
  holomorphic : ∀ c ∈ charts, IsHolomorphicProjectiveChart L c
  compatible : ∀ c ∈ charts, ∀ d ∈ charts, ProjectiveChartsCompatible L c d

/-- Two projective atlases are equivalent when every chart of one is compatible with every chart of
the other. (Ghys, §4, pp.593–594; §3, p.590) -/
def ProjectiveAtlasesEquivalent (A B : ComplexProjectiveAtlas L) : Prop :=
  ∀ c ∈ A.charts, ∀ d ∈ B.charts, ProjectiveChartsCompatible L c d

/-- Compatibility of the union is an equivalence relation on covering projective atlases. (Ghys, §4,
pp.593–594; §5, p.597) -/
theorem projectiveAtlasesEquivalent_equivalence :
    Equivalence (ProjectiveAtlasesEquivalent L) := by
  classical
  constructor
  · intro A c hc d hd
    exact A.compatible c hc d hd
  · intro A B h c hc d hd x hx
    obtain ⟨g, hg⟩ := h d hd c hc x ⟨hx.2, hx.1⟩
    obtain ⟨m, hm⟩ := g.prop
    refine ⟨ComplexMobiusTransformation.ofMatrix m⁻¹, ?_⟩
    filter_upwards [hg] with y hy
    change d y = m⁻¹ • c y
    rw [hy]
    change d y = m⁻¹ • g.val (d y)
    rw [hm]
    simp
  · intro A B D hAB hBD c hc d hd x hx
    obtain ⟨b, hb, hxb⟩ := B.cover x
    obtain ⟨g, hg⟩ := hAB c hc b hb x ⟨hx.1, hxb⟩
    obtain ⟨k, hk⟩ := hBD b hb d hd x ⟨hxb, hx.2⟩
    obtain ⟨m, hm⟩ := g.prop
    obtain ⟨n, hn⟩ := k.prop
    refine ⟨ComplexMobiusTransformation.ofMatrix (n * m), ?_⟩
    filter_upwards [hg, hk] with y hy hky
    change d y = (n * m) • c y
    rw [hky]
    change k.val (b y) = _
    rw [hn, hy]
    change n • g.val (c y) = _
    rw [hm, mul_smul]

/-- The setoid on projective atlases defined by compatibility of their union. (Ghys, §4, pp.593–594) -/
def complexProjectiveAtlasSetoid : Setoid (ComplexProjectiveAtlas L) where
  r := ProjectiveAtlasesEquivalent L
  iseqv := projectiveAtlasesEquivalent_equivalence L

/-- A complex projective structure is an equivalence class of covering holomorphic atlases with
Möbius transition germs. (Ghys, §4, pp.593–594; §5, p.597) -/
def ComplexProjectiveStructure := Quotient (complexProjectiveAtlasSetoid L)

/-- The maximal projective atlas consists of holomorphic projective charts compatible with every
chart of a representative atlas. (Ghys, §4, pp.593–594) -/
def ComplexProjectiveStructure.maximalAtlas (A : ComplexProjectiveStructure L) :
    Set (OpenPartialHomeomorph L ComplexProjectiveLine) :=
  {c | IsHolomorphicProjectiveChart L c ∧
    ∀ d ∈ A.out.charts, ProjectiveChartsCompatible L d c}

/-- The maximal projective atlas equals the set of holomorphic charts compatible with any chosen
representative of the structure. (Ghys, §4, pp.593–594) -/
theorem ComplexProjectiveStructure.maximalAtlas_eq_of_representative
    (A : ComplexProjectiveAtlas L) :
    ComplexProjectiveStructure.maximalAtlas L
      (Quotient.mk (complexProjectiveAtlasSetoid L) A : ComplexProjectiveStructure L) =
      {c | IsHolomorphicProjectiveChart L c ∧
        ∀ d ∈ A.charts, ProjectiveChartsCompatible L d c} := by
  classical
  let Q : ComplexProjectiveStructure L := Quotient.mk (complexProjectiveAtlasSetoid L) A
  have hQA : ProjectiveAtlasesEquivalent L Q.out A :=
    Quotient.exact (Quotient.out_eq Q)
  have ht (B D : ComplexProjectiveAtlas L) (hDB : ProjectiveAtlasesEquivalent L D B)
      (c : OpenPartialHomeomorph L ComplexProjectiveLine)
      (hc : ∀ b ∈ B.charts, ProjectiveChartsCompatible L b c) :
      ∀ d ∈ D.charts, ProjectiveChartsCompatible L d c := by
    intro d hd x hx
    obtain ⟨b, hb, hxb⟩ := B.cover x
    obtain ⟨g, hg⟩ := hDB d hd b hb x ⟨hx.1, hxb⟩
    obtain ⟨k, hk⟩ := hc b hb x ⟨hxb, hx.2⟩
    obtain ⟨m, hm⟩ := g.prop
    obtain ⟨n, hn⟩ := k.prop
    refine ⟨ComplexMobiusTransformation.ofMatrix (n * m), ?_⟩
    filter_upwards [hg, hk] with y hy hky
    change c y = (n * m) • d y
    rw [hky]
    change k.val (b y) = _
    rw [hn, hy]
    change n • g.val (d y) = _
    rw [hm, mul_smul]
  ext c
  change (_ ∧ ∀ d ∈ Q.out.charts, ProjectiveChartsCompatible L d c) ↔ _
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, ht Q.out A ((projectiveAtlasesEquivalent_equivalence L).symm hQA) c h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, ht A Q.out hQA c h⟩

section Foliation

variable {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
  (F : TransverseContinuousFoliations.{u, v} s 2 M)
  (C : IntrinsicComplexUnstableLeaves F)

/-- A transverse projective chart on a restricted foliation box is a projective coordinate that is
biholomorphic on each intrinsic unstable plaque. (Ghys, §4, pp.593–594; §5, p.597) -/
structure TransverseProjectiveChart where
  box : F.boxIndex
  stableDomain : TopologicalSpace.Opens (FoliationCoordinateDisk s)
  coordinate : OpenPartialHomeomorph (FoliationCoordinateDisk 2) ComplexProjectiveLine
  holomorphic_on_plaque : ∀ z : FoliationCoordinateDisk s,
    z ∈ stableDomain →
    letI := F.unstableTopology (F.unstableLabel box z)
    letI := C.charts (F.unstableLabel box z)
    ∃ e : OpenPartialHomeomorph
        (IntrinsicFoliationLeaf F.unstablePartition (F.unstableLabel box z))
        ComplexProjectiveLine,
      e.source = {p | ∃ w : FoliationCoordinateDisk 2, w ∈ coordinate.source ∧
        p.val = ((F.box box).chart (z, w)).val} ∧
      e.target = coordinate.target ∧
      (∀ w : FoliationCoordinateDisk 2, w ∈ coordinate.source →
        e ⟨((F.box box).chart (z, w)).val, F.unstable_label box z w⟩ = coordinate w) ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target

/-- The open rectangle in a foliation box on which the transverse projective chart is defined.
(Ghys, §5, p.597) -/
def TransverseProjectiveChart.domain (c : TransverseProjectiveChart F C) : Set M :=
  {x | ∃ h : x ∈ (F.box c.box).image,
    ((F.box c.box).chart.symm ⟨x, h⟩).1 ∈ c.stableDomain ∧
      ((F.box c.box).chart.symm ⟨x, h⟩).2 ∈ c.coordinate.source}

/-- The domain of a transverse projective chart is open in the ambient manifold. (Ghys, §5, p.597) -/
theorem TransverseProjectiveChart.isOpen_domain (c : TransverseProjectiveChart F C) :
    IsOpen (c.domain F C) := by
  let B := F.box c.box
  have hrect : IsOpen (c.stableDomain ×ˢ c.coordinate.source) :=
    c.stableDomain.isOpen.prod c.coordinate.open_source
  have hopen : IsOpen (B.chart '' (c.stableDomain ×ˢ c.coordinate.source)) :=
    B.chart.isOpenMap _ hrect
  have hamb : IsOpen (Subtype.val '' (B.chart ''
      (c.stableDomain ×ˢ c.coordinate.source))) :=
    B.isOpen_image.isOpenMap_subtype_val _ hopen
  convert hamb using 1
  ext x
  simp only [TransverseProjectiveChart.domain, Set.mem_image, Set.mem_prod]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨⟨x, h⟩, ⟨B.chart.symm ⟨x, h⟩, ⟨h1, h2⟩, ?_⟩, rfl⟩
    exact B.chart.apply_symm_apply _
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(B.chart z).prop, ?_⟩
    simpa [B] using hz

/-- The projective transverse coordinate determined by the second coordinate of the foliation box.
(Ghys, §5, p.597) -/
def TransverseProjectiveChart.transverseCoordinate
    (c : TransverseProjectiveChart F C) (x : M) : ComplexProjectiveLine := by
  classical
  exact if h : x ∈ (F.box c.box).image then
    c.coordinate (((F.box c.box).chart.symm ⟨x, h⟩).2)
  else complexProjectiveLineInfinity

/-- Two transverse projective charts are compatible when their transition germs on overlapping
domains are induced by Möbius transformations. (Ghys, §4, pp.593–594; §5, p.597) -/
def TransverseProjectiveChartsCompatible (c d : TransverseProjectiveChart F C) : Prop :=
  ∀ x ∈ c.domain F C ∩ d.domain F C,
    ∃ g : ComplexMobiusTransformation,
      ∀ᶠ y in 𝓝 x,
        d.transverseCoordinate F C y = g.apply (c.transverseCoordinate F C y)

/-- A covering foliation atlas of compatible transverse projective charts. (Ghys, §5, p.597) -/
structure TransverseProjectiveAtlas where
  charts : Set (TransverseProjectiveChart F C)
  cover : ∀ x : M, ∃ c ∈ charts, x ∈ c.domain F C
  compatible : ∀ c ∈ charts, ∀ d ∈ charts,
    TransverseProjectiveChartsCompatible F C c d

/-- Two transverse projective atlases are equivalent when every chart of one is compatible with
every chart of the other. (Ghys, §5, p.597) -/
def TransverseProjectiveAtlasesEquivalent
    (A B : TransverseProjectiveAtlas F C) : Prop :=
  ∀ c ∈ A.charts, ∀ d ∈ B.charts, TransverseProjectiveChartsCompatible F C c d

/-- Compatibility of the union is an equivalence relation on transverse projective atlases. (Ghys,
§5, p.597) -/
theorem transverseProjectiveAtlasesEquivalent_equivalence :
    Equivalence (TransverseProjectiveAtlasesEquivalent F C) := by
  classical
  constructor
  · intro A c hc d hd
    exact A.compatible c hc d hd
  · intro A B h c hc d hd x hx
    obtain ⟨g, hg⟩ := h d hd c hc x ⟨hx.2, hx.1⟩
    obtain ⟨m, hm⟩ := g.prop
    refine ⟨ComplexMobiusTransformation.ofMatrix m⁻¹, ?_⟩
    filter_upwards [hg] with y hy
    change d.transverseCoordinate F C y = m⁻¹ • c.transverseCoordinate F C y
    rw [hy]
    change d.transverseCoordinate F C y = m⁻¹ • g.val (d.transverseCoordinate F C y)
    rw [hm]
    simp
  · intro A B D hAB hBD c hc d hd x hx
    obtain ⟨b, hb, hxb⟩ := B.cover x
    obtain ⟨g, hg⟩ := hAB c hc b hb x ⟨hx.1, hxb⟩
    obtain ⟨k, hk⟩ := hBD b hb d hd x ⟨hxb, hx.2⟩
    obtain ⟨m, hm⟩ := g.prop
    obtain ⟨n, hn⟩ := k.prop
    refine ⟨ComplexMobiusTransformation.ofMatrix (n * m), ?_⟩
    filter_upwards [hg, hk] with y hy hky
    change d.transverseCoordinate F C y = (n * m) • c.transverseCoordinate F C y
    rw [hky]
    change k.val (b.transverseCoordinate F C y) = _
    rw [hn, hy]
    change n • g.val (c.transverseCoordinate F C y) = _
    rw [hm, mul_smul]

/-- The setoid on transverse projective atlases defined by compatibility of their union. (Ghys, §5,
p.597) -/
def transverseProjectiveAtlasSetoid : Setoid (TransverseProjectiveAtlas F C) where
  r := TransverseProjectiveAtlasesEquivalent F C
  iseqv := transverseProjectiveAtlasesEquivalent_equivalence F C

/-- A transverse projective structure on the stable foliation with its supplied holomorphic unstable
transversals. (Ghys, §5, p.597) -/
def TransverseProjectiveStructure := Quotient (transverseProjectiveAtlasSetoid F C)

/-- A family of affine structures on the intrinsic unstable leaves with their supplied complex
structures. (Ghys, Prop. 3.1, p.590) -/
structure AffineUnstableLeafStructures where
  structureAt : ∀ q : Quotient F.unstablePartition,
    letI := F.unstableTopology q
    letI := C.charts q
    ComplexAffineStructure (IntrinsicFoliationLeaf F.unstablePartition q)

/-- The affine structure on the intrinsic unstable leaf through an ambient point. (Ghys, §3, p.590) -/
def AffineUnstableLeafStructures.atPoint (A : AffineUnstableLeafStructures F C)
    (x : M) :
    letI := C.charts (Quotient.mk F.unstablePartition x)
    ComplexAffineStructure (F.ULeaf x) :=
  A.structureAt (Quotient.mk F.unstablePartition x)

/-- The holonomy representative along the prefix from time zero to `t` of a supplied stable path.
(Ghys, Prop. 3.1(ii), p.590) -/
def prefixHolonomy {q : Quotient F.stablePartition}
    {a b : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path a b)
    (H : LocalHolonomyContinuation F γ) (t : unitInterval) :=
  (H.representative 0 t (show (0 : unitInterval) ≤ t from bot_le)).map

/-- The affine ratio of a fixed triple transported by stable prefix holonomy, computed in the
supplied target coordinates. (Ghys, Prop. 3.1(ii), p.590) -/
def transportedAffineRatio {q : Quotient F.stablePartition}
    {a b : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path a b)
    (h : ∀ t : unitInterval, PathHolonomyRepresentative F γ 0 t)
    (c : ∀ t : unitInterval, OpenPartialHomeomorph (F.ULeaf (γ t).val) ℂ)
    (x y z : F.ULeaf (γ 0).val) (t : unitInterval) : ℂ :=
  (c t ((h t).map x) - c t ((h t).map y)) /
    (c t ((h t).map x) - c t ((h t).map z))

/-- Along every stable path, prefix holonomy germs admit representatives on a common connected open
neighborhood and affine target charts containing their images at every parameter. The
transported affine ratio of each fixed distinct triple in that neighborhood is continuous in the
path parameter. (Ghys, Prop. 3.1(ii), p.590) -/
def AffineUnstableLeafStructures.ContinuousAlongStableHolonomy
    (A : AffineUnstableLeafStructures F C) : Prop :=
  ∀ (q : Quotient F.stablePartition)
    (a b : IntrinsicFoliationLeaf F.stablePartition q) (γ : Path a b)
    (H : LocalHolonomyContinuation F γ),
    ∃ h : ∀ t : unitInterval, PathHolonomyRepresentative F γ 0 t,
      (∀ t : unitInterval,
        Filter.Germ.ofFun (h t).map =
          (Filter.Germ.ofFun (prefixHolonomy F γ H t) :
            Filter.Germ (𝓝 (F.uPoint (γ 0).val)) (F.ULeaf (γ t).val))) ∧
    ∃ U : Set (F.ULeaf (γ 0).val),
      IsOpen U ∧ IsConnected U ∧ F.uPoint (γ 0).val ∈ U ∧
      (∀ t : unitInterval, U ⊆ (h t).map.source) ∧
    ∃ c : ∀ t : unitInterval, OpenPartialHomeomorph (F.ULeaf (γ t).val) ℂ,
      (∀ t : unitInterval,
        letI := C.charts (Quotient.mk F.unstablePartition (γ t).val)
        c t ∈ ComplexAffineStructure.maximalAtlas (F.ULeaf (γ t).val)
          (A.atPoint F C (γ t).val)) ∧
      (∀ (t : unitInterval) (w : F.ULeaf (γ 0).val), w ∈ U →
        (h t).map w ∈ (c t).source) ∧
      ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x ≠ y → x ≠ z → y ≠ z →
        Continuous (transportedAffineRatio F γ h c x y z)

end Foliation

end HolomorphicAnosov.Ghys

