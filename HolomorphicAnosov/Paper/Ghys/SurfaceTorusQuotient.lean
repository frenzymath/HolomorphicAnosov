import HolomorphicAnosov.Geometry.ProjectiveFixedInfinityAffine
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Targets.Theorem11Support.Surface.lattice_rank_four
import HolomorphicAnosov.SurfaceTorusSupport.LatticeConstruction
import HolomorphicAnosov.Topology.OpenQuotientHomeomorphOfFibres
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Paper.Ghys.SurfaceDomainDichotomy
import HolomorphicAnosov.Paper.Ghys.NormalizedProductBiholomorphProviderG12
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphDomainExcluded
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveProduct
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Convex.Contractible

/-! This file develops the constructions and results stated below. -/

open scoped ContDiff Topology _root_.Topology

universe u v w

namespace HolomorphicAnosov

/-- The deck transformations of the lattice quotient are exactly translations by lattice vectors. -/
private theorem lattice_quotient_deck_translations (L : FullComplexLattice 2) :
    (∀ k : deck (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L),
      ∃! l : L.lattice, ∀ z, k • z = z + (l : ComplexModel 2)) ∧
    (∀ l : L.lattice,
      ∃ k : deck (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L),
        ∀ z, k • z = z + (l : ComplexModel 2)) := by
  let : DiscreteTopology L.lattice := L.discrete
  constructor
  · intro k
    have hm (z : ComplexModel 2) : k • z - z ∈ L.lattice :=
      QuotientAddGroup.eq_iff_sub_mem.mp (deck.proj_smul k z)
    let displacement : ComplexModel 2 → L.lattice := fun z ↦ ⟨k • z - z, hm z⟩
    have hc : Continuous displacement :=
      ((continuous_const_smul k).sub continuous_id).subtype_mk _
    have hlc : IsLocallyConstant displacement :=
      (IsLocallyConstant.iff_continuous displacement).2 hc
    refine ⟨displacement 0, ?_, ?_⟩
    · intro z
      have heq := congrArg Subtype.val (hlc.apply_eq_of_preconnectedSpace z 0)
      change k • z - z = (displacement 0 : ComplexModel 2) at heq
      exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)
    · intro l hl
      apply Subtype.ext
      have h := hl 0
      simpa [displacement] using h.symm
  · intro l
    let tr : ComplexModel 2 ≃ₜ ComplexModel 2 := Homeomorph.addRight (l : ComplexModel 2)
    have htr : tr ∈ deck (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) := by
      apply deck.mem_iff.mpr
      funext z
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change z + (l : ComplexModel 2) - z ∈ L.lattice
      simp [l.property]
    exact ⟨⟨tr, htr⟩, fun z ↦ rfl⟩




/-- The quotient projection is a local biholomorphism for the existing complex structures. -/
private theorem lattice_quotient_local_diffeomorph (L : FullComplexLattice 2) :
    IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞
      (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) := by
  classical
  let := complexTorus_isManifold L
  intro z
  let q : ComplexModel 2 → ComplexTorus L := QuotientAddGroup.mk
  let e := chartAt (ComplexModel 2) (q z)
  have he : e ∈ atlas (ComplexModel 2) (ComplexTorus L) := chart_mem_atlas _ _
  have hx : q z ∈ e.source := mem_chart_source _ _
  have hsymm : (e.symm : ComplexModel 2 → ComplexTorus L) = q := by
    change ∃ x : ComplexTorus L,
      ((torus_quotient_covering L).isLocalHomeomorph.localInverseAt
        ((torus_quotient_covering L).surjective.hasRightInverse.choose x)).trans
        (OpenPartialHomeomorph.refl (ComplexModel 2)) = e at he
    obtain ⟨x, hxe⟩ := he
    rw [← hxe]
    simp [q]
  let l : ComplexModel 2 := e (q z) - z
  have hl : l ∈ L.lattice := by
    change e (q z) - z ∈ L.lattice.toAddSubgroup
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    change q (e (q z)) = q z
    simpa only [hsymm] using e.left_inv hx
  let tr : Diffeomorph (complexModel 2) (complexModel 2)
      (ComplexModel 2) (ComplexModel 2) ∞ :=
    { toEquiv := (Homeomorph.addRight l).toEquiv
      contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  let inv : PartialDiffeomorph (complexModel 2) (complexModel 2)
      (ComplexModel 2) (ComplexTorus L) ∞ :=
    { toPartialEquiv := e.symm.toPartialEquiv
      open_source := e.open_target
      open_target := e.open_source
      contMDiffOn_toFun := contMDiffOn_chart_symm
      contMDiffOn_invFun := contMDiffOn_chart }
  refine ⟨tr.toPartialDiffeomorph.trans inv, ?_, ?_⟩
  · change z ∈ Set.univ ∧ z + l ∈ e.target
    constructor
    · trivial
    · simpa [l] using e.map_source hx
  · intro y _
    change q y = e.symm (y + l)
    rw [hsymm]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change y - (y + l) ∈ L.lattice
    simpa using L.lattice.neg_mem hl


/-- A compatible quotient descent is a biholomorphism when its representative maps are local complex diffeomorphisms. -/
private theorem normalized_quotient_biholomorph
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    (π : U → S) (hπ : Function.Surjective π)
    (hlπ : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ π)
    (D0 : Biholomorph 2 2 U (ComplexModel 2)) (L : FullComplexLattice 2)
    (hfib : ∀ u v : U, π u = π v ↔
      (QuotientAddGroup.mk (D0 u) : ComplexTorus L) = QuotientAddGroup.mk (D0 v)) :
    ∃ h : Biholomorph 2 2 S (ComplexTorus L),
      ∀ u, h (π u) = QuotientAddGroup.mk (D0 u) := by
  classical
  obtain ⟨h, hrep⟩ := open_quotient_homeomorph_of_fibres π hπ hlπ.contMDiff.continuous
    hlπ.isLocalHomeomorph.isOpenMap D0.toHomeomorph L.lattice.toAddSubgroup hfib
  let q : ComplexModel 2 → ComplexTorus L := QuotientAddGroup.mk
  have hlq := lattice_quotient_local_diffeomorph L
  have hf : ContMDiff (complexModel 2) (complexModel 2) ∞ h := by
    intro x
    obtain ⟨u, rfl⟩ := hπ x
    let inv := (hlπ u).localInverse
    have hc : ContMDiffAt (complexModel 2) (complexModel 2) ∞
        (fun y ↦ q (D0 (inv y))) (π u) :=
      (hlq.contMDiff _).comp _ ((D0.contMDiff_toFun _).comp _
        (hlπ u).localInverse_contMDiffAt)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(hlπ u).localInverse_open_source.mem_nhds
      (hlπ u).localInverse_mem_source] with y hy
    exact ((hrep (inv y)).symm.trans (congrArg h ((hlπ u).localInverse_right_inv hy))).symm
  have hi : ContMDiff (complexModel 2) (complexModel 2) ∞ h.symm := by
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    let inv := (hlq z).localInverse
    have hc : ContMDiffAt (complexModel 2) (complexModel 2) ∞
        (fun y ↦ π (D0.symm (inv y))) (q z) :=
      (hlπ.contMDiff _).comp _ ((D0.symm.contMDiff_toFun _).comp _
        (hlq z).localInverse_contMDiffAt)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(hlq z).localInverse_open_source.mem_nhds
      (hlq z).localInverse_mem_source] with y hy
    apply h.injective
    rw [h.apply_symm_apply, hrep]
    change y = q (D0 (D0.symm (inv y)))
    rw [D0.apply_symm_apply]
    exact ((hlq z).localInverse_right_inv hy).symm
  exact ⟨{ toEquiv := h.toEquiv, contMDiff_toFun := hf, contMDiff_invFun := hi }, hrep⟩


/-- The normalized developing map identifies the surface with the quotient of `ℂ²` by its translation lattice, and identifies the deck group with that lattice. (Ghys, pp. 598–600) -/
private theorem normalized_surface_quotient_tail
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    (π : U → S) (hπ : Function.Surjective π)
    (hlπ : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ π)
    (D0 : Biholomorph 2 2 U (ComplexModel 2)) (L : FullComplexLattice 2)
    (hfib : ∀ u v : U, π u = π v ↔
      (QuotientAddGroup.mk (D0 u) : ComplexTorus L) = QuotientAddGroup.mk (D0 v)) :
    ∃ h : Biholomorph 2 2 S (ComplexTorus L),
      DiscreteTopology L.lattice ∧
      Submodule.span ℝ (L.lattice : Set (ComplexModel 2)) = ⊤ ∧
      Module.finrank ℤ L.lattice = 4 ∧
      IsManifold (complexModel 2) ∞ (ComplexTorus L) ∧
      (∀ u, h (π u) = QuotientAddGroup.mk (D0 u)) ∧
      Function.Surjective (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) ∧
      IsCoveringMap (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) ∧
      SimplyConnectedSpace (ComplexModel 2) ∧
      IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞
        (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L) ∧
      (∀ k : deck (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L),
        ∃! l : L.lattice, ∀ z, k • z = z + (l : ComplexModel 2)) ∧
      (∀ l : L.lattice,
        ∃ k : deck (QuotientAddGroup.mk : ComplexModel 2 → ComplexTorus L),
          ∀ z, k • z = z + (l : ComplexModel 2)) := by
  let : DiscreteTopology L.lattice := L.discrete
  let : IsZLattice ℝ L.lattice := L.full
  obtain ⟨h, hrep⟩ := normalized_quotient_biholomorph π hπ hlπ D0 L hfib
  exact ⟨h, L.discrete, IsZLattice.span_top (K := ℝ) (L := L.lattice),
    Theorem11SupportW02.lattice_rank_four L, complexTorus_isManifold L, hrep,
    (torus_quotient_covering L).surjective, (torus_quotient_covering L).isCoveringMap,
    inferInstance, lattice_quotient_local_diffeomorph L,
    (lattice_quotient_deck_translations L).1, (lattice_quotient_deck_translations L).2⟩


/-- Fibres of the universal cover are precisely the orbits of its deck group; for translation coordinates this is the additive quotient relation. (Hatcher, Prop. 1.39) -/
private theorem normalized_translation_fibres
    {S U : Type*} [TopologicalSpace S] [TopologicalSpace U]
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (π : U → S) (hπ : IsCoveringMap π)
    (D0 : U ≃ₜ ComplexModel 2) (τ : Additive (deck π) →+ ComplexModel 2)
    (hτ : ∀ (g : deck π) (u : U), D0 (g • u) = D0 u + τ (Additive.ofMul g)) :
    ∀ u v, π u = π v ↔
      (QuotientAddGroup.mk (D0 u) : ComplexModel 2 ⧸ τ.range) =
        QuotientAddGroup.mk (D0 v) := by
  intro u v
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Ghys.covering_deck_between_points hπ v u h.symm
    refine ⟨Additive.ofMul g, ?_⟩
    have he := hτ g v
    rw [hg] at he
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he.symm)
  · rintro ⟨g, hg⟩
    have he : g.toMul • v = u := by
      apply D0.injective
      rw [hτ]
      change D0 v + τ g = D0 u
      rw [hg]
      abel
    rw [← he]
    exact deck.proj_smul _ _


/-- Normalized deck translations form the full lattice, and fibres of the original covering are its additive cosets. (Ghys, p. 600; Hatcher, Props. 1.39–1.40) -/
private theorem normalized_translation_full_lattice
    {S U : Type*} [TopologicalSpace S] [CompactSpace S] [TopologicalSpace U]
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (π : U → S) (hπ : IsCoveringMap π) (hπs : Function.Surjective π)
    (D0 : U ≃ₜ ComplexModel 2) (τ : Additive (deck π) →+ ComplexModel 2)
    (hτ : ∀ (g : deck π) (u : U), D0 (g • u) = D0 u + τ (Additive.ofMul g)) :
    ∃ L : FullComplexLattice 2,
      Set.range τ = (L.lattice : Set (ComplexModel 2)) ∧
      ∀ u v, π u = π v ↔
        (QuotientAddGroup.mk (D0 u) : ComplexTorus L) = QuotientAddGroup.mk (D0 v) := by
  have hfib := normalized_translation_fibres π hπ D0 τ hτ
  let : DiscreteTopology τ.range :=
    SurfaceTorusSupport.translation_range_discrete π hπ D0 τ hτ
  let : CompactSpace (ComplexModel 2 ⧸ τ.range) :=
    SurfaceTorusSupport.normalized_quotient_compact π hπ hπs D0 τ.range
      (fun u v h ↦ (hfib u v).mp h)
  let : DiscreteTopology τ.range.toIntSubmodule := by
    change DiscreteTopology τ.range
    infer_instance
  let : CompactSpace (ComplexModel 2 ⧸ τ.range.toIntSubmodule.toAddSubgroup) := by
    change CompactSpace (ComplexModel 2 ⧸ τ.range)
    infer_instance
  let L : FullComplexLattice 2 :=
    { lattice := τ.range.toIntSubmodule
      discrete := inferInstance
      full := ⟨SurfaceTorusSupport.compact_quotient_real_span τ.range.toIntSubmodule⟩ }
  exact ⟨L, rfl, hfib⟩


/-- Evaluating a deck displacement at the normalized origin gives an additive homomorphism, and injectivity of the development makes it injective. (Ghys, p. 600) -/
private theorem normalized_translation_hom
    {S U : Type*} [TopologicalSpace S] [TopologicalSpace U]
    (π : U → S) (D0 : U ≃ₜ ComplexModel 2)
    (htranslation : ∀ g : deck π, ∃ z : ComplexModel 2,
      ∀ u, D0 (g • u) = D0 u + z) :
    ∃ τ : Additive (deck π) →+ ComplexModel 2, Function.Injective τ ∧
      ∀ (g : deck π) (u : U), D0 (g • u) = D0 u + τ (Additive.ofMul g) := by
  let u₀ := D0.symm 0
  let t : Additive (deck π) → ComplexModel 2 := fun g ↦ D0 (g.toMul • u₀)
  have ht (g : deck π) (u : U) : D0 (g • u) = D0 u + t (Additive.ofMul g) := by
    obtain ⟨z, hz⟩ := htranslation g
    have hzero : t (Additive.ofMul g) = z := by simpa [t, u₀] using hz u₀
    rw [hzero]
    exact hz u
  let τ : Additive (deck π) →+ ComplexModel 2 :=
    { toFun := t
      map_zero' := by simp [t, u₀]
      map_add' := by
        intro g h
        change D0 ((g.toMul * h.toMul) • u₀) = t g + t h
        rw [mul_smul, ht]
        change t h + t g = t g + t h
        exact add_comm _ _ }
  refine ⟨τ, ?_, ht⟩
  intro g h heq
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Homeomorph.ext
  intro u
  apply D0.injective
  change D0 (g.toMul • u) = D0 (h.toMul • u)
  rw [ht, ht]
  exact congrArg (fun z ↦ D0 u + z) heq


/-- After normalization, the developing map gives the complete quotient and deck description, including the full lattice and the biholomorphic quotient structure. (Ghys, p. 600) -/
theorem normalized_surface_translation_quotient
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S] [CompactSpace S]
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (π : U → S) (hπ : IsCoveringMap π) (hπs : Function.Surjective π)
    (hlπ : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ π)
    (D0 : Biholomorph 2 2 U (ComplexModel 2))
    (htranslation : ∀ g : deck π, ∃ z : ComplexModel 2,
      ∀ u, D0 (g • u) = D0 u + z) :
    ∃ (τ : Additive (deck π) →+ ComplexModel 2) (L : FullComplexLattice 2)
      (h : Biholomorph 2 2 S (ComplexTorus L)),
      let q : ComplexModel 2 → ComplexTorus L := QuotientAddGroup.mk
      Function.Injective τ ∧
      (∀ (g : deck π) (u : U), D0 (g • u) = D0 u + τ (Additive.ofMul g)) ∧
      Set.range τ = (L.lattice : Set (ComplexModel 2)) ∧
      DiscreteTopology L.lattice ∧
      Submodule.span ℝ (L.lattice : Set (ComplexModel 2)) = ⊤ ∧
      Module.finrank ℤ L.lattice = 4 ∧
      IsManifold (complexModel 2) ∞ (ComplexTorus L) ∧
      (∀ u, h (π u) = q (D0 u)) ∧
      Function.Surjective q ∧ IsCoveringMap q ∧ SimplyConnectedSpace (ComplexModel 2) ∧
      IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ q ∧
      (∀ k : deck q, ∃! l : L.lattice, ∀ z, k • z = z + (l : ComplexModel 2)) ∧
      (∀ l : L.lattice, ∃ k : deck q, ∀ z, k • z = z + (l : ComplexModel 2)) := by
  obtain ⟨τ, hinj, hτ⟩ := normalized_translation_hom π D0.toHomeomorph htranslation
  obtain ⟨L, hL, hfib⟩ := normalized_translation_full_lattice π hπ hπs D0.toHomeomorph τ hτ
  obtain ⟨h, htail⟩ := normalized_surface_quotient_tail π hπs hlπ D0 L hfib
  exact ⟨τ, L, h, hinj, hτ, hL, htail⟩


/-- No nontrivial deck transformation preserves a lifted coordinate leaf. (Ghys, p. 600; Hatcher, Prop. 1.34) -/
private theorem deck_eq_one_of_return_to_lifted_leaf
    {S U B : Type*} [TopologicalSpace S] [TopologicalSpace U] [PreconnectedSpace U]
    (π : U → S) (hπ : IsCoveringMap π) (i : B → S) (hi : Function.Injective i)
    (lift : B → U) (hlift : ∀ b, π (lift b) = i b)
    (γ : deck π) (b₀ b₁ : B) (hreturn : γ • lift b₀ = lift b₁) : γ = 1 := by
  have hb : b₁ = b₀ := hi (by
    rw [← hlift b₁, ← hreturn, deck.proj_smul γ (lift b₀), hlift])
  have hfixed : γ • lift b₀ = lift b₀ := by simpa only [hb] using hreturn
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun (hπ.eq_of_comp_eq (γ : U ≃ₜ U).continuous continuous_id
    γ.property (lift b₀) hfixed)

/-- In the punctured-product case, each complete coordinate leaf has trivial coordinate stabilizer, and its omitted point is the common pole forced by the developing image. (Ghys, pp. 599–600) -/
private theorem punctured_product_deck_coordinate_free
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : Ghys.OrderedProjectiveProductAtlas.{u, v} f a)
    (π : U → S) (dev : Ghys.OrderedProjectiveProductDevelopment A π)
    (hLeaves : Ghys.CompleteLiftedProjectiveLeaves dev)
    (hD : Function.Injective dev.developingMap)
    (poleS poleU : ComplexProjectiveLine)
    (hrange : Set.range dev.developingMap = ({poleS}ᶜ ×ˢ {poleU}ᶜ)) :
    (∀ (γ : deck π) (x : U),
      (dev.developingMap (γ • x)).1 = (dev.developingMap x).1 → γ = 1) ∧
    (∀ (γ : deck π) (x : U),
      (dev.developingMap (γ • x)).2 = (dev.developingMap x).2 → γ = 1) := by
  let := dev.simplyConnected
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  constructor
  · intro γ x hcoord
    obtain ⟨lift, _, _, hproj, hleaf, pole, e, _, _, _, _, _, heRange⟩ := hLeaves.2 x
    have hpole : pole = poleU := by
      by_contra hn
      have hbad : (dev.developingMap x).1 = (dev.developingMap x).1 ∧ poleU ≠ pole :=
        ⟨rfl, Ne.symm hn⟩
      have hm : ((dev.developingMap x).1, poleU) ∈
          Set.range (fun z ↦ dev.developingMap (lift z)) := by rw [heRange]; exact hbad
      obtain ⟨z, hz⟩ := hm
      have hc : ((dev.developingMap x).1, poleU) ∈ Set.range dev.developingMap :=
        ⟨lift z, hz⟩
      rw [hrange] at hc
      exact hc.2 rfl
    have hxleaf : x ∈ Set.range lift := by
      rw [hleaf]
      exact mem_connectedComponentIn rfl
    obtain ⟨z₀, hz₀⟩ := hxleaf
    have hg : dev.developingMap (γ • x) ∈ Set.range (fun z ↦ dev.developingMap (lift z)) := by
      rw [heRange, hpole]
      have hm : dev.developingMap (γ • x) ∈ Set.range dev.developingMap := Set.mem_range_self _
      rw [hrange] at hm
      exact ⟨hcoord, hm.2⟩
    obtain ⟨z₁, hz₁⟩ := hg
    apply deck_eq_one_of_return_to_lifted_leaf π dev.covering Subtype.val
      Subtype.val_injective lift hproj γ z₀ z₁
    rw [hz₀]
    exact (hD hz₁).symm
  · intro γ x hcoord
    obtain ⟨lift, _, _, hproj, hleaf, pole, e, _, _, _, _, _, heRange⟩ := hLeaves.1 x
    have hpole : pole = poleS := by
      by_contra hn
      have hbad : poleS ≠ pole ∧ (dev.developingMap x).2 = (dev.developingMap x).2 :=
        ⟨Ne.symm hn, rfl⟩
      have hm : (poleS, (dev.developingMap x).2) ∈
          Set.range (fun z ↦ dev.developingMap (lift z)) := by rw [heRange]; exact hbad
      obtain ⟨z, hz⟩ := hm
      have hc : (poleS, (dev.developingMap x).2) ∈ Set.range dev.developingMap :=
        ⟨lift z, hz⟩
      rw [hrange] at hc
      exact hc.1 rfl
    have hxleaf : x ∈ Set.range lift := by
      rw [hleaf]
      exact mem_connectedComponentIn rfl
    obtain ⟨z₀, hz₀⟩ := hxleaf
    have hg : dev.developingMap (γ • x) ∈ Set.range (fun z ↦ dev.developingMap (lift z)) := by
      rw [heRange, hpole]
      have hm : dev.developingMap (γ • x) ∈ Set.range dev.developingMap := Set.mem_range_self _
      rw [hrange] at hm
      exact ⟨hm.1, hcoord⟩
    obtain ⟨z₁, hz₁⟩ := hg
    apply deck_eq_one_of_return_to_lifted_leaf π dev.covering Subtype.val
      Subtype.val_injective lift hproj γ z₀ z₁
    rw [hz₀]
    exact (hD hz₁).symm

/-- An affine projective action on a coordinate with no fixed leaf must be a translation. (Ghys, p. 600) -/
private theorem affine_deck_action_is_translation
    {S U : Type*} [TopologicalSpace S] [TopologicalSpace U]
    (π : U → S) (D0 : U ≃ₜ ComplexModel 2)
    (hfree : ∀ (γ : deck π) (j : Fin 2) (u : U),
      D0 (γ • u) j = D0 u j → γ = 1)
    (haff : ∀ γ : deck π, ∃ α β : ComplexModel 2,
      ∀ u j, D0 (γ • u) j = α j * D0 u j + β j) :
    ∀ γ : deck π, ∃ z : ComplexModel 2, ∀ u, D0 (γ • u) = D0 u + z := by
  intro γ
  obtain ⟨α, β, hab⟩ := haff γ
  have hα (j : Fin 2) : α j = 1 := by
    by_contra hn
    have hden : 1 - α j ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
    let z : ComplexModel 2 := fun _ ↦ β j / (1 - α j)
    have hf : D0 (γ • D0.symm z) j = D0 (D0.symm z) j := by
      rw [hab, D0.apply_symm_apply]
      dsimp [z]
      field_simp
      ring
    have hγ := hfree γ j (D0.symm z) hf
    have hb : β j = 0 := by
      have h := hab (D0.symm 0) j
      simpa [hγ] using h.symm
    have h := hab (D0.symm (fun _ ↦ 1)) j
    have : α j = 1 := by simpa [hγ, hb] using h.symm
    exact hn this
  refine ⟨β, fun u ↦ ?_⟩
  ext j
  simpa [hα j] using hab u j



/-- In the punctured-product case, each holonomy component fixes its omitted point. (Ghys, p. 600) -/
private theorem punctured_product_holonomy_fixes_poles
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : Ghys.OrderedProjectiveProductAtlas.{u, v} f a)
    (π : U → S) (dev : Ghys.OrderedProjectiveProductDevelopment A π)
    (x : U) (poleS poleU : ComplexProjectiveLine)
    (hrange : Set.range dev.developingMap = ({poleS}ᶜ ×ˢ {poleU}ᶜ)) :
    ∀ γ : deck π,
      (dev.holonomy γ).1 • poleS = poleS ∧
        (dev.holonomy γ).2 • poleU = poleU := by
  intro γ
  have hx : (dev.developingMap x).1 ≠ poleS ∧
      (dev.developingMap x).2 ≠ poleU := by
    have h : dev.developingMap x ∈ Set.range dev.developingMap := Set.mem_range_self _
    rw [hrange] at h
    exact h
  constructor
  · let g := (dev.holonomy γ).1
    by_contra hfix
    have hs : g⁻¹ • poleS ≠ poleS := by
      intro hs
      have h := congrArg (fun p : ComplexProjectiveLine ↦ g • p) hs
      exact hfix (by simpa [g] using h.symm)
    have hmem : (g⁻¹ • poleS, (dev.developingMap x).2) ∈
        Set.range dev.developingMap := by
      rw [hrange]
      exact ⟨hs, hx.2⟩
    obtain ⟨y, hy⟩ := hmem
    have hfirst : (dev.developingMap (γ • y)).1 = poleS := by
      rw [dev.equivariant]
      have hy1 := congrArg Prod.fst hy
      change (dev.developingMap y).1 = g⁻¹ • poleS at hy1
      simp [g, hy1]
    have h : dev.developingMap (γ • y) ∈ Set.range dev.developingMap :=
      Set.mem_range_self _
    rw [hrange] at h
    exact h.1 hfirst
  · let g := (dev.holonomy γ).2
    by_contra hfix
    have hs : g⁻¹ • poleU ≠ poleU := by
      intro hs
      have h := congrArg (fun p : ComplexProjectiveLine ↦ g • p) hs
      exact hfix (by simpa [g] using h.symm)
    have hmem : ((dev.developingMap x).1, g⁻¹ • poleU) ∈
        Set.range dev.developingMap := by
      rw [hrange]
      exact ⟨hx.1, hs⟩
    obtain ⟨y, hy⟩ := hmem
    have hsecond : (dev.developingMap (γ • y)).2 = poleU := by
      rw [dev.equivariant]
      have hy2 := congrArg Prod.snd hy
      change (dev.developingMap y).2 = g⁻¹ • poleU at hy2
      simp [g, hy2]
    have h : dev.developingMap (γ • y) ∈ Set.range dev.developingMap :=
      Set.mem_range_self _
    rw [hrange] at h
    exact h.2 hsecond




/-- After normalizing the omitted point to infinity, the conjugated holonomy acts affinely on the finite chart. (Ghys, p. 600) -/
private theorem normalized_holonomy_fixes_infinity
    (g m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (pole : ComplexProjectiveLine) (hg : g • pole = pole)
    (hm : m • pole = complexProjectiveLineInfinity) :
    (m * g * m⁻¹) • complexProjectiveLineInfinity =
      complexProjectiveLineInfinity := by
  have hinv : m⁻¹ • complexProjectiveLineInfinity = pole := by
    calc
      m⁻¹ • complexProjectiveLineInfinity = m⁻¹ • (m • pole) := by rw [hm]
      _ = pole := inv_smul_smul m pole
  calc
    (m * g * m⁻¹) • complexProjectiveLineInfinity =
        m • (g • (m⁻¹ • complexProjectiveLineInfinity)) := by rw [mul_smul, mul_smul]
    _ = complexProjectiveLineInfinity := by rw [hinv, hg, hm]


/-- The surface development descends to a biholomorphism from the original surface to the quotient of `ℂ²` by a full translation lattice, with the deck group acting by those translations. (Ghys, Theorem A, pp. 585, 598–600; Hatcher, §1.3) -/
theorem surface_torus_quotient
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : Ghys.OrderedProjectiveProductAtlas.{u, v} f a)
    (π : U → S) (dev : Ghys.OrderedProjectiveProductDevelopment A π) :
    let D := dev.developingMap
    ∃ (a b : ComplexProjectiveLine)
      (ms mu : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
      (D0 : Biholomorph 2 2 U (ComplexModel 2))
      (τ : Additive (deck π) →+ ComplexModel 2) (L : FullComplexLattice 2)
      (h : Biholomorph 2 2 S (ComplexTorus L)),
      let q : ComplexModel 2 → ComplexTorus L := QuotientAddGroup.mk
      Set.range D = ({a}ᶜ ×ˢ {b}ᶜ) ∧
      ms • a = complexProjectiveLineInfinity ∧ mu • b = complexProjectiveLineInfinity ∧
      (∀ u, D0 u 0 = complexProjectiveLineChartFun 1 (ms • (D u).1) 0 ∧
        D0 u 1 = complexProjectiveLineChartFun 1 (mu • (D u).2) 0) ∧
      Function.Injective τ ∧
      (∀ (g : deck π) (u : U), D0 (g • u) = D0 u + τ (Additive.ofMul g)) ∧
      Set.range τ = (L.lattice : Set (ComplexModel 2)) ∧
      DiscreteTopology L.lattice ∧
      Submodule.span ℝ (L.lattice : Set (ComplexModel 2)) = ⊤ ∧
      Module.finrank ℤ L.lattice = 4 ∧
      IsManifold (complexModel 2) ∞ (ComplexTorus L) ∧
      (∀ u, h (π u) = q (D0 u)) ∧
      Function.Surjective q ∧ IsCoveringMap q ∧ SimplyConnectedSpace (ComplexModel 2) ∧
      IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ q ∧
      (∀ k : deck q, ∃! l : L.lattice, ∀ z, k • z = z + (l : ComplexModel 2)) ∧
      (∀ l : L.lattice, ∃ k : deck q, ∀ z, k • z = z + (l : ComplexModel 2)) := by
  classical
  let : SimplyConnectedSpace U := dev.simplyConnected
  let : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace (ComplexModel 2) U
  suffices hnormalized :
      ∃ (poleS poleU : ComplexProjectiveLine)
        (ms mu : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
        (D0 : Biholomorph 2 2 U (ComplexModel 2)),
        Set.range dev.developingMap = ({poleS}ᶜ ×ˢ {poleU}ᶜ) ∧
        ms • poleS = complexProjectiveLineInfinity ∧
        mu • poleU = complexProjectiveLineInfinity ∧
        (∀ u, D0 u 0 = complexProjectiveLineChartFun 1
          (ms • (dev.developingMap u).1) 0 ∧
          D0 u 1 = complexProjectiveLineChartFun 1
          (mu • (dev.developingMap u).2) 0) ∧
        (∀ g : deck π, ∃ z : ComplexModel 2,
          ∀ u, D0 (g • u) = D0 u + z) by
    obtain ⟨poleS, poleU, ms, mu, D0, hrange, hms, hmu, hcoords, htrans⟩ := hnormalized
    obtain ⟨τ, L, h, htail⟩ := normalized_surface_translation_quotient
      π dev.covering dev.surjective dev.cover_holomorphic D0 htrans
    exact ⟨poleS, poleU, ms, mu, D0, τ, L, h, hrange, hms, hmu, hcoords, htail⟩
  suffices hgeometry :
      Ghys.CompleteLiftedProjectiveLeaves dev ∧
      ∃ (poleS poleU : ComplexProjectiveLine)
        (ms mu : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
        (D0 : Biholomorph 2 2 U (ComplexModel 2)),
        Set.range dev.developingMap = ({poleS}ᶜ ×ˢ {poleU}ᶜ) ∧
        ms • poleS = complexProjectiveLineInfinity ∧
        mu • poleU = complexProjectiveLineInfinity ∧
        (∀ u, D0 u 0 = complexProjectiveLineChartFun 1
          (ms • (dev.developingMap u).1) 0 ∧
          D0 u 1 = complexProjectiveLineChartFun 1
          (mu • (dev.developingMap u).2) 0) by
    obtain ⟨hLeaves, poleS, poleU, ms, mu, D0, hrange, hms, hmu, hcoords⟩ := hgeometry
    have hD := (Ghys.surface_domain_dichotomy f a A dev hLeaves).1
    have hfree := punctured_product_deck_coordinate_free f a A π dev hLeaves hD
      poleS poleU hrange
    have havoid (x : U) :
        ms • (dev.developingMap x).1 ≠ complexProjectiveLineInfinity ∧
        mu • (dev.developingMap x).2 ≠ complexProjectiveLineInfinity := by
      have hx : dev.developingMap x ∈ Set.range dev.developingMap := Set.mem_range_self _
      rw [hrange] at hx
      constructor
      · intro h
        exact hx.1 ((MulAction.injective ms) (h.trans hms.symm))
      · intro h
        exact hx.2 ((MulAction.injective mu) (h.trans hmu.symm))
    have hfree' (γ : deck π) (j : Fin 2) (x : U)
        (heq : D0 (γ • x) j = D0 x j) : γ = 1 := by
      fin_cases j
      · change D0 (γ • x) 0 = D0 x 0 at heq
        rw [(hcoords _).1, (hcoords _).1] at heq
        exact hfree.1 γ x ((MulAction.injective ms)
          (projective_finite_chart_injective (havoid _).1 (havoid _).1 heq))
      · change D0 (γ • x) 1 = D0 x 1 at heq
        rw [(hcoords _).2, (hcoords _).2] at heq
        exact hfree.2 γ x ((MulAction.injective mu)
          (projective_finite_chart_injective (havoid _).2 (havoid _).2 heq))
    have haff (γ : deck π) : ∃ α β : ComplexModel 2,
        ∀ x j, D0 (γ • x) j = α j * D0 x j + β j := by
      let x₀ : U := D0.symm 0
      have hp := punctured_product_holonomy_fixes_poles A π dev x₀ poleS poleU hrange γ
      obtain ⟨αs, βs, hs⟩ := projective_fixed_infinity_chart_affine
        (ms * (dev.holonomy γ).1 * ms⁻¹)
        (normalized_holonomy_fixes_infinity _ _ poleS hp.1 hms)
      obtain ⟨αu, βu, hu⟩ := projective_fixed_infinity_chart_affine
        (mu * (dev.holonomy γ).2 * mu⁻¹)
        (normalized_holonomy_fixes_infinity _ _ poleU hp.2 hmu)
      refine ⟨![αs, αu], ![βs, βu], ?_⟩
      intro x j
      fin_cases j
      · change D0 (γ • x) 0 = αs * D0 x 0 + βs
        rw [(hcoords _).1, (hcoords _).1]
        have he := hs (ms • (dev.developingMap x).1) (havoid x).1
        simpa [mul_smul, dev.equivariant] using he
      · change D0 (γ • x) 1 = αu * D0 x 1 + βu
        rw [(hcoords _).2, (hcoords _).2]
        have he := hu (mu • (dev.developingMap x).2) (havoid x).2
        simpa [mul_smul, dev.equivariant] using he
    exact ⟨poleS, poleU, ms, mu, D0, hrange, hms, hmu, hcoords,
      affine_deck_action_is_translation π D0.toHomeomorph hfree' haff⟩
  have hLeaves : Ghys.CompleteLiftedProjectiveLeaves dev :=
    Ghys.ordered_projective_complete_leaves A dev
  obtain ⟨hD, hcase⟩ := Ghys.surface_domain_dichotomy f a A dev hLeaves
  have hgraph := Ghys.surface_graph_domain_excluded f a A dev hLeaves
  obtain ⟨poleS, poleU, hrange⟩ := hcase.elim (fun hA => False.elim (hgraph hA.1)) (fun hB => hB.1)
  obtain ⟨ms, mu, D0, hms, hmu, hcoords⟩ := Ghys.normalized_product_biholomorph_provider_g12
    dev.developingMap hD dev.localBiholomorph hrange
  exact ⟨hLeaves, poleS, poleU, ms, mu, D0, hrange, hms, hmu, hcoords⟩


end HolomorphicAnosov
