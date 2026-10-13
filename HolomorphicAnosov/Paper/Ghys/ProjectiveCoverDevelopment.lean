import HolomorphicAnosov.Dynamics.StableImmersedLeafLift
import HolomorphicAnosov.Paper.Ghys.CompleteAffineProjectiveCoordinate
import HolomorphicAnosov.Paper.Ghys.InjectivePointedLeafLift
import HolomorphicAnosov.Paper.Ghys.HolomorphicOfLift
import HolomorphicAnosov.Paper.Ghys.ProjectiveCoverComponentFundamentalGroup
import HolomorphicAnosov.Paper.Ghys.ProjectiveBoxProductCoordinates
import HolomorphicAnosov.Paper.Ghys.ProjectiveCoverLocalPathConnected
import HolomorphicAnosov.Paper.Ghys.ProjectiveCoverChartData
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.TransverseMobiusGermDevelopment
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Quotient
import HolomorphicAnosov.Topology.CoveringDeckBetweenPoints
import HolomorphicAnosov.Geometry.ComplexMobiusPSLNormalization

/-! Universal-cover continuation of transverse projective atlases, deck holonomy, and complete
intrinsic leaf lifts. -/

set_option maxHeartbeats 800000

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

universe u v

attribute [local instance] complex_isManifold_real

/-- A map whose range is a connected component is surjective onto that component subtype. -/
theorem projective_cover_component_range_surjective
    {M E : Type*} [TopologicalSpace M] (p : E → M) (x₀ : M)
    (hrange : Set.range p = connectedComponent x₀) :
    Function.Surjective (fun e : E =>
      (⟨p e, by rw [← hrange]; exact ⟨e, rfl⟩⟩ : connectedComponent x₀)) := by
  intro z
  rcases z with ⟨z, hz⟩
  rw [← hrange] at hz
  rcases hz with ⟨e, rfl⟩
  exact ⟨e, rfl⟩

/-- If the range of a map equals a connected component, every value of the map belongs to that
component. -/
theorem projective_cover_component_range_mapsTo
    {M E : Type*} [TopologicalSpace M] (p : E → M) (x₀ : M)
    (hrange : Set.range p = connectedComponent x₀) :
    Set.MapsTo p Set.univ (connectedComponent x₀) := by
  intro e _
  rw [← hrange]
  exact ⟨e, rfl⟩

/-- A covering whose range lies in an open connected component restricts to a covering of that
component. (Hatcher, Prop. 1.31 p.61) -/
theorem projective_cover_component_restricted_cover
    {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    [LocallyConnectedSpace M] (p : E → M) (hp : IsCoveringMap p) (x₀ : M)
    (hmaps : Set.MapsTo p Set.univ (connectedComponent x₀)) :
    IsCoveringMap (fun e : E =>
      (⟨p e, hmaps trivial⟩ : connectedComponent x₀)) := by
  let C := connectedComponent x₀
  let hpre : p ⁻¹' C = Set.univ := by
    ext e
    simp only [mem_preimage, mem_univ, iff_true]
    exact hmaps trivial
  let hres : IsCoveringMap (C.restrictPreimage p) := hp.restrictPreimage C
  let heq : E ≃ₜ p ⁻¹' C :=
    ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ E)).symm
  have hcomp : IsCoveringMap (C.restrictPreimage p ∘ heq) := hres.comp_homeomorph heq
  convert hcomp using 1
  ext e
  rfl

/-- A covering family of open product charts in `(Fin q → ℝ) × ℂ`, with connected stable factors and
local Möbius transition germs for the transverse coordinate. -/
structure ProjectiveCoverTransverseTransportData
    {M : Type u} [TopologicalSpace M] {ι : Type*} where
  q : ℕ
  b : ι → OpenPartialHomeomorph M ((Fin q → ℝ) × ℂ)
  P : ι → Set (Fin q → ℝ)
  V : ι → Set ℂ
  hP : ∀ i, IsOpen (P i) ∧ IsConnected (P i)
  hV : ∀ i, IsOpen (V i)
  htarget : ∀ i, (b i).target = P i ×ˢ V i
  hcover : ∀ x : M, ∃ i, x ∈ (b i).source
  hlocal : ∀ i j x, x ∈ (b i).source ∩ (b j).source →
    ∃ g : ComplexMobiusTransformation,
      ∀ᶠ w in 𝓝 x,
        complexProjectiveLineFinite ((b j w).2) =
          g.apply (complexProjectiveLineFinite ((b i w).2))

/-- A covering family of open product charts with connected stable factors, identified locally with
native transverse projective coordinates satisfying Möbius transition germs. (Ghys, §§2 and 4
pp.589,594; HPS, §7 pp.115–116) -/
structure ProjectiveCoverTransverseChartCarrierData
    {M : Type u} [TopologicalSpace M] {ι : Type*} where
  q : ℕ
  b : ι → OpenPartialHomeomorph M ((Fin q → ℝ) × ℂ)
  P : ι → Set (Fin q → ℝ)
  V : ι → Set ℂ
  hP : ∀ i, IsOpen (P i) ∧ IsConnected (P i)
  hV : ∀ i, IsOpen (V i)
  htarget : ∀ i, (b i).target = P i ×ˢ V i
  hcover : ∀ x : M, ∃ i, x ∈ (b i).source
  native : ι → M → ComplexProjectiveLine
  hnative : ∀ i j x, x ∈ (b i).source ∩ (b j).source →
    ∃ g : ComplexMobiusTransformation,
      ∀ᶠ w in 𝓝 x, native j w = g.apply (native i w)
  hident : ∀ i x, x ∈ (b i).source →
    ∀ᶠ w in 𝓝 x,
      complexProjectiveLineFinite ((b i w).2) = native i w

/-- A transverse projective atlas admits a refinement by open product charts with connected stable
factors and finite complex transverse coordinates representing its native projective
coordinates. -/
theorem projective_cover_transverse_chart_refinement
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C) :
    letI := A.realAmbientCharts
    ∃ carrier : ProjectiveCoverTransverseChartCarrierData (M := M) (ι := M),
      (∀ i, IsConnected (carrier.b i).source) ∧
      (∀ i, i ∈ (carrier.b i).source) ∧
      ∀ i, ∃ c ∈ atlas.charts, ∃ m : GL (Fin 2) ℂ,
        (carrier.b i).source ⊆ c.domain A.F C ∧
        ∀ x, carrier.native i x = m • c.transverseCoordinate A.F C x := by
  classical
  let := A.realAmbientCharts
  have disk_nonempty (k : ℕ) : Nonempty (FoliationCoordinateDisk k) :=
    ⟨⟨0, by simp⟩⟩
  let := disk_nonempty s
  let := disk_nonempty 2
  let : LocallyConnectedSpace (FoliationCoordinateDisk s) :=
    Metric.isOpen_ball.locallyConnectedSpace
  let stableCoord : OpenPartialHomeomorph (FoliationCoordinateDisk s) (Fin s → ℝ) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let finiteCoord : OpenPartialHomeomorph ComplexProjectiveLine ℂ :=
    (complexProjectiveLineChart 1).trans canonicalPlaneCoordinate
  have hfinite (z : ComplexProjectiveLine) (hz : z ∈ finiteCoord.source) :
      complexProjectiveLineFinite (finiteCoord z) = z := by
    change complexProjectiveLineChartInv 1
      (fun _ ↦ complexProjectiveLineChartFun 1 z 0) = z
    exact projective_left_inv 1 z hz.1
  let mobiusHomeo (m : GL (Fin 2) ℂ) : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine :=
    { toEquiv := MulAction.toPerm m
      continuous_toFun := (ComplexMobiusTransformation.ofMatrix m).continuous_apply
      continuous_invFun := (ComplexMobiusTransformation.ofMatrix m⁻¹).continuous_apply }
  have localCharts (x : M) :
      ∃ c ∈ atlas.charts, ∃ m : GL (Fin 2) ℂ,
      ∃ b : OpenPartialHomeomorph M ((Fin s → ℝ) × ℂ),
      ∃ P : Set (Fin s → ℝ), ∃ V : Set ℂ,
        (IsOpen P ∧ IsConnected P) ∧ (IsOpen V ∧ IsConnected V) ∧ b.target = P ×ˢ V ∧
        x ∈ b.source ∧ b.source ⊆ c.domain A.F C ∧
        ∀ y ∈ b.source,
          complexProjectiveLineFinite ((b y).2) = m • c.transverseCoordinate A.F C y := by
    obtain ⟨c, hc, hx⟩ := atlas.cover x
    obtain ⟨hxbox, hxstable, hxtrans⟩ := hx
    let zw := (A.F.box c.box).chart.symm ⟨x, hxbox⟩
    obtain ⟨S, hSsub, hSopen, hzS, hSconn⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance zw.1
        c.stableDomain (c.stableDomain.isOpen.mem_nhds hxstable)
    let cs := stableCoord.restrOpen S hSopen
    have hcsSource : cs.source = S := by
      simp [cs, stableCoord]
    have hcsConn : IsConnected cs.target := by
      rw [← cs.image_source_eq_target]
      apply IsConnected.image _ cs cs.continuousOn
      rwa [hcsSource]
    obtain ⟨m0, hm0⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) ℂ)
      (c.coordinate zw.2) (complexProjectiveLineFinite 0)
    let m := m0.toGL
    have hm : m • c.coordinate zw.2 = complexProjectiveLineFinite 0 := hm0
    let ct0 := (c.coordinate.trans (mobiusHomeo m).toOpenPartialHomeomorph).trans finiteCoord
    have hct0Source : zw.2 ∈ ct0.source := by
      refine ⟨⟨hxtrans, mem_univ _⟩, ?_⟩
      change m • c.coordinate zw.2 ∈ finiteCoord.source
      rw [hm]
      exact ⟨projective_inv_mem 1 _, mem_univ _⟩
    let T := connectedComponentIn ct0.target (ct0 zw.2)
    have hTopen : IsOpen T := ct0.open_target.connectedComponentIn
    have hTsub : T ⊆ ct0.target := connectedComponentIn_subset _ _
    have hTmem : ct0 zw.2 ∈ T := mem_connectedComponentIn (ct0.map_source hct0Source)
    have hTconn : IsConnected T := isConnected_connectedComponentIn_iff.mpr
      (ct0.map_source hct0Source)
    let ct := (ct0.symm.restrOpen T hTopen).symm
    have hctTarget : ct.target = T := inter_eq_right.mpr hTsub
    have hctSource : zw.2 ∈ ct.source := ⟨hct0Source, hTmem⟩
    obtain ⟨b, hbSource, hbTarget, hbEval⟩ :=
      projective_box_product_coordinates (A.F.box c.box).image
        (A.F.box c.box).isOpen_image (A.F.box c.box).chart cs ct
    refine ⟨c, hc, m, b, cs.target, ct.target, ⟨cs.open_target, hcsConn⟩,
      ⟨ct.open_target, hctTarget ▸ hTconn⟩, hbTarget, ?_, ?_, ?_⟩
    · rw [hbSource]
      refine ⟨zw, ⟨hcsSource ▸ hzS, hctSource⟩, ?_⟩
      exact congrArg Subtype.val ((A.F.box c.box).chart.apply_symm_apply ⟨x, hxbox⟩)
    · intro y hy
      rw [hbSource] at hy
      obtain ⟨⟨z,w⟩, ⟨hz,hw⟩, rfl⟩ := hy
      refine ⟨((A.F.box c.box).chart (z,w)).property, ?_, ?_⟩
      · simpa using hSsub (hcsSource ▸ hz)
      · simpa using hw.1.1.1
    · intro y hy
      rw [hbSource] at hy
      obtain ⟨⟨z,w⟩, ⟨hz,hw⟩, rfl⟩ := hy
      rw [hbEval]
      have hcoord : c.transverseCoordinate A.F C ((A.F.box c.box).chart (z,w)).val =
          c.coordinate w := by
        simp [TransverseProjectiveChart.transverseCoordinate]
      rw [hcoord]
      exact hfinite _ hw.1.2
  choose c hc m b P V hP hV htarget hcenter hsource hcoord using localCharts
  refine ⟨{
    q := s
    b := b
    P := P
    V := V
    hP := hP
    hV := fun i ↦ (hV i).1
    htarget := htarget
    hcover := fun x ↦ ⟨x, hcenter x⟩
    native := fun i x ↦ m i • (c i).transverseCoordinate A.F C x
    hnative := ?_
    hident := ?_ }, ?_, hcenter, ?_⟩
  · intro i j x hx
    obtain ⟨g, hg⟩ := atlas.compatible (c i) (hc i) (c j) (hc j) x
      ⟨hsource i hx.1, hsource j hx.2⟩
    obtain ⟨gmat, hgmat⟩ := g.property
    refine ⟨ComplexMobiusTransformation.ofMatrix (m j * gmat * (m i)⁻¹), ?_⟩
    filter_upwards [hg] with w hw
    change m j • (c j).transverseCoordinate A.F C w =
      (m j * gmat * (m i)⁻¹) • (m i • (c i).transverseCoordinate A.F C w)
    rw [hw, show g.apply ((c i).transverseCoordinate A.F C w) =
      gmat • (c i).transverseCoordinate A.F C w from hgmat _]
    simp only [mul_smul, inv_smul_smul]
  · intro i x hx
    filter_upwards [(b i).open_source.mem_nhds hx] with w hw
    exact hcoord i w hw
  · intro i
    have hc := (hP i).2.prod (hV i).2
    rw [← htarget i] at hc
    have himage := hc.image (b i).symm (b i).symm.continuousOn
    simpa only [OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_image_target_eq_source] using himage
  · intro i
    exact ⟨c i, hc i, m i, hsource i, fun _ ↦ rfl⟩

/-- The transverse projective atlas admits a covering family of finite product charts with connected
open stable factors and compatible native transition germs. (Ghys, §§2 and 4 pp.589,594) -/
theorem projective_cover_transverse_chart_coordinate_gap
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C) :
    letI := A.realAmbientCharts
    ∃ ι : Type u, Nonempty (ProjectiveCoverTransverseChartCarrierData
      (M := M) (ι := ι)) := by
  obtain ⟨carrier, _, _, _⟩ := projective_cover_transverse_chart_refinement f a s A C atlas
  exact ⟨M, ⟨carrier⟩⟩

/-- Product charts locally representing compatible native transverse projective coordinates have
local Möbius transition germs. -/
theorem projective_cover_transverse_chart_compatibility_gap
    {d : ℕ} {M : Type u} {ι : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (_atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C)
    (carrier : letI := A.realAmbientCharts;
      ProjectiveCoverTransverseChartCarrierData
        (M := M) (ι := ι)) :
    letI := A.realAmbientCharts
    ∀ i j x, x ∈ (carrier.b i).source ∩ (carrier.b j).source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ w in 𝓝 x,
          complexProjectiveLineFinite ((carrier.b j w).2) =
            g.apply (complexProjectiveLineFinite ((carrier.b i w).2)) := by
  intro i j x hx
  obtain ⟨g, hg⟩ := carrier.hnative i j x hx
  refine ⟨g, ?_⟩
  filter_upwards [carrier.hident i x hx.1, hg, carrier.hident j x hx.2] with w hwi hw hwj
  rw [hwj, hw, hwi]

/-- Eventual agreement of two product-chart coordinates with compatible native transverse
coordinates gives a Möbius transition germ on their overlap. (Ghys, §4 pp.593–594) -/
theorem projective_cover_transverse_chart_compatibility_of_native_coordinates
    {M : Type u} [TopologicalSpace M] {q : ℕ}
    (bi bj : M → (Fin q → ℝ) × ℂ)
    (xi xj : M → ComplexProjectiveLine)
    (g : ComplexMobiusTransformation) (x : M)
    (hbi : ∀ᶠ w in 𝓝 x,
      complexProjectiveLineFinite ((bi w).2) = xi w)
    (hbj : ∀ᶠ w in 𝓝 x,
      complexProjectiveLineFinite ((bj w).2) = xj w)
    (hcompat : ∀ᶠ w in 𝓝 x, xj w = g.apply (xi w)) :
    ∀ᶠ w in 𝓝 x,
      complexProjectiveLineFinite ((bj w).2) =
        g.apply (complexProjectiveLineFinite ((bi w).2)) := by
  filter_upwards [hbj, hcompat, hbi] with w hwj hwc hwi
  rw [hwj, hwc, hwi]

/-- Native atlas compatibility and eventual agreement of product-chart coordinates with native
transverse coordinates imply a local Möbius transition germ on a fixed overlap. -/
theorem projective_cover_transverse_chart_compatibility_of_atlas
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u, v} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (c d : TransverseProjectiveChart F C)
    (hcd : TransverseProjectiveChartsCompatible F C c d)
    (x : M) (hx : x ∈ c.domain F C ∩ d.domain F C)
    {q : ℕ} (bi bj : M → (Fin q → ℝ) × ℂ)
    (hbi : ∀ᶠ w in 𝓝 x,
      complexProjectiveLineFinite ((bi w).2) = c.transverseCoordinate F C w)
    (hbj : ∀ᶠ w in 𝓝 x,
      complexProjectiveLineFinite ((bj w).2) = d.transverseCoordinate F C w) :
    ∃ g : ComplexMobiusTransformation,
      ∀ᶠ w in 𝓝 x,
        complexProjectiveLineFinite ((bj w).2) =
          g.apply (complexProjectiveLineFinite ((bi w).2)) := by
  obtain ⟨g, hg⟩ := hcd x hx
  exact ⟨g, projective_cover_transverse_chart_compatibility_of_native_coordinates
    bi bj (c.transverseCoordinate F C) (d.transverseCoordinate F C) g x hbi hbj hg⟩

/-- A family of product charts locally agreeing with native projective coordinates inherits their
Möbius transition germs. -/
theorem projective_cover_transverse_chart_compatibility_from_native
    {M : Type u} [TopologicalSpace M] {ι _q : Type*}
    (carrier : ProjectiveCoverTransverseChartCarrierData (M := M) (ι := ι))
    (native : ι → M → ComplexProjectiveLine)
    (hnative : ∀ i j x, x ∈ (carrier.b i).source ∩ (carrier.b j).source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ w in 𝓝 x, native j w = g.apply (native i w))
    (hident : ∀ i x, x ∈ (carrier.b i).source →
      ∀ᶠ w in 𝓝 x,
        complexProjectiveLineFinite ((carrier.b i w).2) = native i w) :
    ∀ i j x, x ∈ (carrier.b i).source ∩ (carrier.b j).source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ w in 𝓝 x,
          complexProjectiveLineFinite ((carrier.b j w).2) =
            g.apply (complexProjectiveLineFinite ((carrier.b i w).2)) := by
  intro i j x hx
  obtain ⟨g, hg⟩ := hnative i j x hx
  exact ⟨g, projective_cover_transverse_chart_compatibility_of_native_coordinates
    (carrier.b i) (carrier.b j) (native i) (native j) g x
    (hident i x hx.1) (hident j x hx.2) hg⟩

theorem projective_cover_transverse_chart_transport_gap
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C) :
    letI := A.realAmbientCharts
    ∃ ι : Type u, Nonempty (ProjectiveCoverTransverseTransportData (M := M) (ι := ι)) := by
  let := A.realAmbientCharts
  rcases projective_cover_transverse_chart_coordinate_gap f a s A C atlas with
    ⟨ι, carrier⟩
  rcases carrier with ⟨carrier⟩
  refine ⟨ι, ⟨ProjectiveCoverTransverseTransportData.mk carrier.q carrier.b carrier.P
    carrier.V carrier.hP carrier.hV carrier.htarget carrier.hcover ?_⟩⟩
  exact projective_cover_transverse_chart_compatibility_gap f a s A C atlas carrier

/-- A complex manifold is locally connected. -/
theorem projective_cover_manifold_locallyConnected_gap
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] : LocallyConnectedSpace M := by
  exact ChartedSpace.locallyConnectedSpace (ComplexModel d) M

/-- An identification of the based fundamental group with the deck group, with path lifts ending at
inverse deck translates and a PSL-valued homomorphism. (Ghys, §5 pp.597–599) -/
structure ProjectiveCoverGlobalContinuationPackage
    {M : Type u} {E : Type v} [TopologicalSpace M] [TopologicalSpace E]
    (p : E → M) (y₀ : E) where
  action : FundamentalGroup M (p y₀) ≃* deck p
  path_lift : ∀ (α : Path (p y₀) (p y₀)),
    ∃ β : Path y₀ ((action (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α)))⁻¹ • y₀),
      ∀ t, p (β t) = α t
  H : FundamentalGroup M (p y₀) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ

/-- Every based loop has a path lift through a covering map starting at a specified point over its
basepoint. -/
theorem projective_cover_raw_path_lift
    {M : Type u} {E : Type v} [TopologicalSpace M] [TopologicalSpace E]
    (p : E → M) (hp : IsCoveringMap p) (y₀ : E) :
    ∀ (α : Path (p y₀) (p y₀)),
      ∃ z : E, ∃ β : Path y₀ z, ∀ t, p (β t) = α t := by
  intro α
  obtain ⟨Γ, hΓ, hΓ₀⟩ := hp.exists_path_lifts α.toContinuousMap y₀ α.source
  let z : E := Γ 1
  refine ⟨z, ⟨Γ, hΓ₀, rfl⟩, ?_⟩
  intro t
  exact congr_fun hΓ t


theorem projective_cover_lift_endpoint_homotopy_invariant
    {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (p : E → M) (hp : IsCoveringMap p) {x : M} (y₀ : E) (hy : p y₀ = x)
    {α α' : Path x x} (h : α.Homotopic α') :
    hp.liftPath α.toContinuousMap y₀ (α.source.trans hy.symm) 1 =
      hp.liftPath α'.toContinuousMap y₀ (α'.source.trans hy.symm) 1 := by
  apply hp.liftPath_apply_one_eq_of_homotopicRel
  exact ⟨h.some⟩

/-- An equivalence between the based fundamental group and the deck group, with loop lifts ending at
inverse deck translates of the marked point. -/
structure ProjectiveCoverDeckEndpointData
    {M : Type u} {E : Type v} [TopologicalSpace M] [TopologicalSpace E]
    (p : E → M) (y₀ : E) where
  action : FundamentalGroup M (p y₀) ≃* deck p
  endpoint_lift : ∀ (α : Path (p y₀) (p y₀)),
    ∃ β : Path y₀ ((action (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α)))⁻¹ • y₀),
      ∀ t, p (β t) = α t

theorem projective_cover_deck_endpoint_gap
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (_atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C)
    (x₀ : M) :
    letI := A.realAmbientCharts
    ∀ (E : Type v) [TopologicalSpace E] [SimplyConnectedSpace E]
      (p : E → M) (_hp : IsCoveringMap p) (y₀ : E),
      p y₀ = x₀ → Set.range p = connectedComponent x₀ →
      Nonempty (ProjectiveCoverDeckEndpointData p y₀) := by
  let := A.realAmbientCharts
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel d) M
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace (ComplexModel d) M
  intro E _ _ p hp y₀ hbase hrange

  let : LocallyPathConnectedSpace E := projective_cover_cover_locallyPathConnected_gap p hp
  let x₀ := p y₀
  have hx₀ : x₀ = p y₀ := rfl
  have hrange' : Set.range p = connectedComponent x₀ := by simpa [x₀, hbase] using hrange
  let pC : E → connectedComponent x₀ := fun e =>
    ⟨p e, projective_cover_component_range_mapsTo p x₀ hrange' trivial⟩
  have hpC : IsCoveringMap pC := projective_cover_component_restricted_cover p hp x₀
    (projective_cover_component_range_mapsTo p x₀ hrange')
  have hsurjC : Function.Surjective pC := projective_cover_component_range_surjective p x₀ hrange'
  have hqC : IsQuotientCoveringMap pC (deck p) := by
    apply (_root_.isQuotientCoveringMap_iff_isCoveringMap_and pC (deck p)).mpr
    have hcancel : IsCancelSMul (deck p) E :=
      ⟨fun d d' e h => by
        apply Subtype.ext
        apply Homeomorph.ext
        exact congrFun (hp.eq_of_comp_eq (d : E ≃ₜ E).continuous
          (d' : E ≃ₜ E).continuous (d.property.trans d'.property.symm) e h)⟩
    refine ⟨hpC, hsurjC, inferInstance, hcancel, ?_⟩
    intro x y
    constructor
    · intro h
      obtain ⟨d, hd⟩ := covering_deck_between_points hp y x (congrArg Subtype.val h.symm)
      exact ⟨d, hd⟩
    · rintro ⟨d, rfl⟩
      apply Subtype.ext
      exact deck.proj_smul d y
  obtain ⟨e, he⟩ := projective_cover_component_fundamental_group_equiv_gap x₀
  let fibre : pC ⁻¹' {pC y₀} := ⟨y₀, rfl⟩
  let action : FundamentalGroup M (p y₀) ≃* deck p :=
    (e.symm.trans (hqC.fundamentalGroupEquiv fibre)).trans (MulEquiv.inv' (deck p)).symm
  refine ⟨⟨action, ?_⟩⟩
  intro α
  have hr : Set.range α ⊆ connectedComponent x₀ :=
    (isPreconnected_range α.continuous).subset_connectedComponent ⟨0, α.source⟩
  let αC : Path (pC y₀) (pC y₀) := {
    toFun := fun t => ⟨α t, hr ⟨t, rfl⟩⟩
    continuous_toFun := α.continuous.subtype_mk _
    source' := Subtype.ext α.source
    target' := Subtype.ext α.target
  }
  have heα : e (Path.Homotopic.Quotient.mk αC) = Path.Homotopic.Quotient.mk α := by
    change e.toMonoidHom _ = _
    rw [he]
    simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rw [← Path.Homotopic.Quotient.mk_map]
    congr 1
  have hend : (action (Path.Homotopic.Quotient.mk α))⁻¹ • y₀ =
      hpC.liftPath αC.toContinuousMap y₀ αC.source 1 := by
    have hh := hqC.unop_fundamentalGroupToMulOpposite_smul
      (e := fibre) (γ := Path.Homotopic.Quotient.mk αC)
    rw [show action (Path.Homotopic.Quotient.mk α) =
      (MulEquiv.inv' (deck p)).symm
        (hqC.fundamentalGroupEquiv fibre (e.symm (Path.Homotopic.Quotient.mk α))) by
      rfl]
    change (MulOpposite.unop
      (hqC.fundamentalGroupEquiv fibre (e.symm (Path.Homotopic.Quotient.mk α)))) • y₀ = _
    have hαC : e.symm (Path.Homotopic.Quotient.mk α) = Path.Homotopic.Quotient.mk αC := by
      rw [← heα]
      exact e.symm_apply_apply _
    rw [hαC]
    change (MulOpposite.unop
      (hqC.fundamentalGroupToMulOpposite fibre (Path.Homotopic.Quotient.mk αC))) • y₀ = _
    rw [hh]
    rfl
  refine ⟨⟨hpC.liftPath αC.toContinuousMap y₀ αC.source,
    hpC.liftPath_zero _ _ _, hend.symm⟩, ?_⟩
  intro t
  exact congrArg Subtype.val (congrFun (hpC.liftPath_lifts αC.toContinuousMap y₀ αC.source) t)


/-- An action-preserving equivalence from the effective Möbius group to PSL transports deck holonomy
while preserving equivariance. -/
theorem projective_cover_psl_holonomy_from_effective
    {D : Type u} [Group D]
    (H : D →* (MulAction.toPermHom (GL (Fin 2) ℂ)
      ComplexProjectiveLine).range)
    (e : (MulAction.toPermHom (GL (Fin 2) ℂ)
      ComplexProjectiveLine).range ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (he : ∀ g : (MulAction.toPermHom (GL (Fin 2) ℂ)
      ComplexProjectiveLine).range, ∀ z : ComplexProjectiveLine,
      e g • z = g.val z) :
    ∃ Hpsl : D →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      ∀ γ : D, ∀ z : ComplexProjectiveLine,
        Hpsl γ • z = (H γ).val z := by
  refine ⟨e.toMonoidHom.comp H, ?_⟩
  intro γ z
  exact he (H γ) z

theorem projective_cover_global_continuation_package_gap
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C)
    (x₀ : M) :
    letI := A.realAmbientCharts
    ∀ (E : Type v) [TopologicalSpace E] [SimplyConnectedSpace E]
      (p : E → M) (_hp : IsCoveringMap p) (y₀ : E),
      p y₀ = x₀ → Set.range p = connectedComponent x₀ →
      Nonempty (ProjectiveCoverGlobalContinuationPackage p y₀) := by
  let := A.realAmbientCharts
  intro E _ _ p hp y₀ hbase hrange
  obtain ⟨D⟩ := projective_cover_deck_endpoint_gap f a s A C atlas x₀ E p hp y₀ hbase hrange
  
  
  exact ⟨{ action := D.action, path_lift := D.endpoint_lift, H := 1 }⟩


/-- The refined transverse atlas develops on the specified component cover, with PSL-valued deck
holonomy and local formulas in the original projective atlas. (Ghys, §5 p.597; Thurston, §3.5
pp.34–35) -/
theorem projective_cover_developing_map
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C)
    (x₀ : M) (E : Type v) [TopologicalSpace E] [SimplyConnectedSpace E]
    (p : E → M) (hp : IsCoveringMap p) (y₀ : E)
    (_hbase : p y₀ = x₀) (hrange : range p = connectedComponent x₀) :
    letI := A.realAmbientCharts
    ∃ D : C(E, ComplexProjectiveLine),
      (∀ y : E, ∃ c ∈ atlas.charts,
        ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ, ∃ V : Set E,
          IsOpen V ∧ y ∈ V ∧ MapsTo p V (c.domain A.F C) ∧
            ∀ z ∈ V, D z = g • c.transverseCoordinate A.F C (p z)) ∧
      ∃ H : deck p →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
        ∀ γ y, D (γ • y) = H γ • D y := by
  classical
  let := A.realAmbientCharts
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel d) M
  let B := connectedComponent x₀
  let : ConnectedSpace B := Subtype.connectedSpace isConnected_connectedComponent
  let : Nonempty B := ⟨⟨x₀, mem_connectedComponent⟩⟩
  let pB : E → B := fun y ↦ ⟨p y, by change p y ∈ connectedComponent x₀; rw [← hrange]; exact mem_range_self y⟩
  have hpB : IsCoveringMap pB := projective_cover_component_restricted_cover p hp x₀
    (projective_cover_component_range_mapsTo p x₀ hrange)
  have hsurj : Function.Surjective pB := projective_cover_component_range_surjective p x₀ hrange
  obtain ⟨carrier, hconn, hcenter, href⟩ :=
    projective_cover_transverse_chart_refinement f a s A C atlas
  let inc : OpenPartialHomeomorph B M :=
    isOpen_connectedComponent.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let b (i : B) := inc.trans (carrier.b i.val)
  have hsub (i : B) : (carrier.b i.val).source ⊆ B := by
    have h := (hconn i.val).isPreconnected.subset_connectedComponent (hcenter i.val)
    change (carrier.b i.val).source ⊆ connectedComponent x₀
    rw [connectedComponent_eq i.property]
    exact h
  have htarget (i : B) : (b i).target = carrier.P i.val ×ˢ carrier.V i.val := by
    rw [show (b i).target = (carrier.b i.val).target ∩
      (carrier.b i.val).symm ⁻¹' B from by simp [b, inc]]
    have hinter : (carrier.b i.val).target ⊆ (carrier.b i.val).symm ⁻¹' B := by
      intro z hz
      exact hsub i ((carrier.b i.val).map_target hz)
    rw [inter_eq_left.mpr hinter]
    exact carrier.htarget i.val
  have hcover (x : B) : ∃ i : B, x ∈ (b i).source := ⟨x, ⟨mem_univ _, hcenter x.val⟩⟩
  have hlocal (i j : B) (x : B) (hx : x ∈ (b i).source ∩ (b j).source) :
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ w in 𝓝 x, complexProjectiveLineFinite ((b j w).2) =
          g.apply (complexProjectiveLineFinite ((b i w).2)) := by
    obtain ⟨g, hg⟩ := carrier.hnative i.val j.val x.val ⟨hx.1.2, hx.2.2⟩
    refine ⟨g, ?_⟩
    have h := carrier.hident i.val x.val hx.1.2
    have h' := carrier.hident j.val x.val hx.2.2
    have hm : ∀ᶠ w in 𝓝 x.val,
        complexProjectiveLineFinite ((carrier.b j.val w).2) =
          g.apply (complexProjectiveLineFinite ((carrier.b i.val w).2)) := by
      filter_upwards [h, h', hg] with w hw hw' hgw
      rw [hw', hgw, hw]
    exact (continuous_subtype_val.tendsto x).eventually hm
  let initial := ComplexMobiusTransformation.ofMatrix (1 : GL (Fin 2) ℂ)
  have develop := transverse_mobius_germ_development carrier.q b
    (fun i ↦ carrier.P i.val) (fun i ↦ carrier.V i.val)
    (fun i ↦ carrier.hP i.val) (fun i ↦ carrier.hV i.val)
    htarget hcover hlocal pB hpB hsurj y₀ (pB y₀) ⟨mem_univ _, hcenter (p y₀)⟩ initial
  obtain ⟨D, hD, _⟩ := develop.1
  obtain ⟨_, _, _, _, _, ⟨H, hH, _⟩, _, _⟩ := develop.2 D hD
  refine ⟨D, ?_, ?_⟩
  · intro y
    obtain ⟨i, g, V, hV, hyV, hVin, hformula⟩ := hD.1 y
    obtain ⟨c, hc, m, hsource, hnative⟩ := href i.val
    obtain ⟨gmat, hgmat⟩ := g.property
    obtain ⟨gpsl, hgpsl, _⟩ := complex_mobius_psl_normalization
      (ComplexMobiusTransformation.ofMatrix (gmat * m))
    have hi : p y ∈ (carrier.b i.val).source := (hVin hyV).2
    have hevent := (hp.continuous.tendsto y).eventually (carrier.hident i.val (p y) hi)
    obtain ⟨W, hWsub, hWopen, hyW⟩ := mem_nhds_iff.mp hevent
    refine ⟨c, hc, gpsl, V ∩ W, hV.inter hWopen, ⟨hyV, hyW⟩,
      fun z hz ↦ hsource (hVin hz.1).2, ?_⟩
    intro z hz
    rw [hformula hz.1]
    change g.apply (complexProjectiveLineFinite ((carrier.b i.val (p z)).2)) = _
    rw [hWsub hz.2, hnative, hgpsl]
    exact (hgmat _).trans (mul_smul gmat m _).symm
  · have hdeck : deck p = deck pB := by
      ext γ
      constructor
      · intro hγ
        funext y
        apply Subtype.ext
        exact congrFun hγ y
      · intro hγ
        funext y
        exact congrArg Subtype.val (congrFun hγ y)
    let e := MulEquiv.subgroupCongr hdeck
    obtain ⟨epsl, hepsl⟩ := effective_complex_mobius_psl_equiv
    refine ⟨epsl.toMonoidHom.comp (H.comp e.toMonoidHom), ?_⟩
    intro γ y
    exact (hH (e γ) y).trans (hepsl (H (e γ)) (D y)).symm


/-- Covering sheets pull back the complex atlas and make the covering projection a local
diffeomorphism. (Lee, Prop. 1.15) -/
theorem projective_cover_component_charts
    {d : ℕ} {M : Type u} {E : Type v}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [TopologicalSpace E]
    (p : E → M) (hp : IsCoveringMap p) :
    ∃ charts : ChartedSpace (ComplexModel d) E,
      letI := charts
      ∃ smooth : IsManifold (complexModel d) ∞ E,
        letI := smooth
        IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p := by
  let charts := coverPullbackCharts (d := d) p hp.isLocalHomeomorph
  refine ⟨charts, ?_⟩
  let := charts
  let smooth := coverPullbackIsManifold (d := d) p hp.isLocalHomeomorph
  refine ⟨smooth, ?_⟩
  let := smooth
  rw [isLocalDiffeomorph_iff]
  intro y
  obtain ⟨e, hy, he⟩ := hp.isLocalHomeomorph y
  have heq : EqOn e p e.source := fun _ _ ↦ congrFun he.symm _
  obtain ⟨hforward, hinverse⟩ := coverPullbackSheetSmooth (d := d) p hp.isLocalHomeomorph e heq
  let φ : PartialDiffeomorph (complexModel d) (complexModel d) E M ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hforward
    contMDiffOn_invFun := hinverse }
  exact ⟨φ, hy, fun x hx ↦ (heq hx).symm⟩

/-- Complete intrinsic unstable leaves have unique pointed holomorphic lifts through the covering
projection. (Hatcher, Prop. 1.33) -/
theorem projective_cover_unstable_pointed_lift
    {s d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    [ChartedSpace (ComplexModel d) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (affine : AffineUnstableLeafStructures F C)
    (hcomplete : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q))
    (hinc : ∀ x : M,
      letI := F.unstableTopology (Quotient.mk F.unstablePartition x)
      letI := C.charts (Quotient.mk F.unstablePartition x)
      ContMDiff (complexModel 1) (complexModel d) ∞ (Subtype.val : F.ULeaf x → M))
    {E : Type v} [TopologicalSpace E] [ChartedSpace (ComplexModel d) E]
    (p : E → M) (hp : IsCoveringMap p)
    (hlocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p) (y : E) :
    letI := F.unstableTopology (Quotient.mk F.unstablePartition (p y))
    letI := C.charts (Quotient.mk F.unstablePartition (p y))
    ∃ lift : F.ULeaf (p y) → E,
      ContMDiff (complexModel 1) (complexModel d) ∞ lift ∧
      Function.Injective lift ∧ lift (F.uPoint (p y)) = y ∧
      ∀ z, p (lift z) = z.val := by
  let q := Quotient.mk F.unstablePartition (p y)
  let := F.unstableTopology q
  let := C.charts q
  let : SimplyConnectedSpace (F.ULeaf (p y)) := (hcomplete q).1
  let : LocallyPathConnectedSpace (F.ULeaf (p y)) :=
    ChartedSpace.locallyPathConnectedSpace (ComplexModel 1) _
  let inc : C(F.ULeaf (p y), M) := ⟨Subtype.val, F.unstable_inclusion q⟩
  obtain ⟨lift, hinj, hproj, hpoint, _⟩ :=
    injective_pointed_leaf_lift hp inc Subtype.val_injective (F.uPoint (p y)) y rfl
  refine ⟨lift, holomorphic_of_lift hlocal lift lift.continuous ?_, hinj,
    hpoint _ rfl, hproj⟩
  have heq : p ∘ lift = (Subtype.val : F.ULeaf (p y) → M) := funext hproj
  rw [heq]
  exact hinc (p y)

/-- Interchanging the factors of native product boxes gives product boxes for the reversed
foliations, with the same intrinsic leaf topologies and charts. -/
private def transposeProjectiveFoliations
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M) :
    letI : ChartedSpace (Fin (t + s) → ℝ) M := Eq.mp (congrArg (fun n ↦ ChartedSpace (Fin n → ℝ) M) (Nat.add_comm s t))
      (inferInstance : ChartedSpace (Fin (s + t) → ℝ) M)
    TransverseContinuousFoliations.{u,u} t s M := by
  letI : ChartedSpace (Fin (t + s) → ℝ) M := Eq.mp
    (congrArg (fun n ↦ ChartedSpace (Fin n → ℝ) M) (Nat.add_comm s t))
    (inferInstance : ChartedSpace (Fin (s + t) → ℝ) M)
  exact {
  boxIndex := F.boxIndex
  box := fun i ↦ ⟨(F.box i).image, (F.box i).isOpen_image,
    (Homeomorph.prodComm _ _).trans (F.box i).chart⟩
  cover := F.cover
  stablePartition := F.unstablePartition
  unstablePartition := F.stablePartition
  stable_generated := F.unstable_generated
  unstable_generated := F.stable_generated
  stableTopology := F.unstableTopology
  unstableTopology := F.stableTopology
  stableCharts := F.unstableCharts
  unstableCharts := F.stableCharts
  stable_connected := F.unstable_connected
  unstable_connected := F.stable_connected
  stable_inclusion := F.unstable_inclusion
  unstable_inclusion := F.stable_inclusion
  stableLabel := F.unstableLabel
  unstableLabel := F.stableLabel
  stable_label := fun i z w ↦ F.unstable_label i w z
  unstable_label := fun i z w ↦ F.stable_label i w z
  stable_plaque := F.unstable_plaque
  unstable_plaque := F.stable_plaque
  stable_topology_generated := F.unstable_topology_generated
  unstable_topology_generated := F.stable_topology_generated }

/-- The range of a pointed intrinsic unstable-leaf lift equals its finite lifted plaque-chain class.
(HPS, §7 pp.115–116) -/
theorem projective_cover_unstable_lift_range
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {E : Type v} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    (y : E) :
    let q := Quotient.mk F.unstablePartition (p y)
    letI := F.unstableTopology q
    ∀ (lift : IntrinsicFoliationLeaf F.unstablePartition q → E),
      Continuous lift → lift ⟨p y, rfl⟩ = y →
      (∀ z, p (lift z) = z.val) →
      range lift = {z : E | Relation.EqvGen
        (fun x y ↦ ∃ i : F.boxIndex, ∃ z : FoliationCoordinateDisk s, ∃ β : Path x y,
          ∀ a : unitInterval, ∃ w : FoliationCoordinateDisk t,
            p (β a) = ((F.box i).chart (z, w)).val) y z} := by
  classical
  dsimp only
  let q := Quotient.mk F.unstablePartition (p y)
  let := F.unstableTopology q
  let := F.unstable_connected q
  intro lift hlift hpoint hproj
  let link : E → E → Prop := fun x y ↦
    ∃ i : F.boxIndex, ∃ z : FoliationCoordinateDisk s, ∃ β : Path x y,
      ∀ a : unitInterval, ∃ w : FoliationCoordinateDisk t,
        p (β a) = ((F.box i).chart (z, w)).val
  let plaque (i : F.boxIndex) (z : FoliationCoordinateDisk s)
      (h : F.unstableLabel i z = q) (w : FoliationCoordinateDisk t) :
      IntrinsicFoliationLeaf F.unstablePartition q :=
    ⟨((F.box i).chart (z, w)).val, (F.unstable_label i z w).trans h⟩
  have hplaque (i z h) : Continuous (plaque i z h) := by
    have general (q' : Quotient F.unstablePartition) (h' : F.unstableLabel i z = q') :
        letI := F.unstableTopology q'
        Continuous (fun w : FoliationCoordinateDisk t ↦
          (⟨((F.box i).chart (z, w)).val, (F.unstable_label i z w).trans h'⟩ :
            IntrinsicFoliationLeaf F.unstablePartition q')) := by
      subst q'
      let := F.unstableTopology (F.unstableLabel i z)
      exact (F.unstable_plaque i z).continuous
    exact general q h
  have hjoin (i z h) (a b : FoliationCoordinateDisk t) :
      link (lift (plaque i z h a)) (lift (plaque i z h b)) := by
    let : PathConnectedSpace (FoliationCoordinateDisk t) :=
      isPathConnected_iff_pathConnectedSpace.mp
        ((convex_ball (0 : Fin t → ℝ) 1).isPathConnected ⟨0, by simp⟩)
    let γ := (Joined.somePath (PathConnectedSpace.joined a b))
    refine ⟨i, z, γ.map (hlift.comp (hplaque i z h)), fun r ↦ ⟨γ r, ?_⟩⟩
    exact hproj _
  let S : Set (IntrinsicFoliationLeaf F.unstablePartition q) :=
    {z | Relation.EqvGen link y (lift z)}
  have hconstant (i z h) (a b : FoliationCoordinateDisk t) :
      plaque i z h a ∈ S ↔ plaque i z h b ∈ S := by
    constructor
    · intro ha
      exact .trans _ _ _ ha (.rel _ _ (hjoin i z h a b))
    · intro hb
      exact .trans _ _ _ hb (.rel _ _ (hjoin i z h b a))
  have hopen (W : Set (IntrinsicFoliationLeaf F.unstablePartition q))
      (hW : ∀ i z h a b, plaque i z h a ∈ W ↔ plaque i z h b ∈ W) : IsOpen W := by
    apply (F.unstable_topology_generated q W).mpr
    intro i z h
    change IsOpen (plaque i z h ⁻¹' W)
    rcases (plaque i z h ⁻¹' W).eq_empty_or_nonempty with he | ⟨a, ha⟩
    · rw [he]; exact isOpen_empty
    · have hall : plaque i z h ⁻¹' W = univ := eq_univ_of_forall (fun b ↦ (hW i z h a b).mp ha)
      rw [hall]; exact isOpen_univ
  have hS : IsClopen S :=
    ⟨isOpen_compl_iff.mp (hopen Sᶜ (fun i z h a b ↦ not_congr (hconstant i z h a b))),
      hopen S hconstant⟩
  have hSuniv : S = univ := hS.eq_univ ⟨⟨p y, rfl⟩, by
    change Relation.EqvGen link y (lift ⟨p y, rfl⟩)
    rw [hpoint]
    exact .refl _⟩
  have hstable {x z : E} (hxz : link x z) (hx : x ∈ range lift) : z ∈ range lift := by
    obtain ⟨i, a, β, hβ⟩ := hxz
    obtain ⟨v, hv⟩ := hx
    have hlabel : F.unstableLabel i a = q := by
      obtain ⟨w, hw⟩ := hβ 0
      have hpx : p x = v.val := by rw [← hv, hproj]
      have heq : ((F.box i).chart (a, w)).val = v.val := by
        rw [Path.source] at hw
        exact hw.symm.trans hpx
      rw [← F.unstable_label i a w, heq]
      exact v.property
    have hmem (r : unitInterval) : p (β r) ∈ (F.box i).image := by
      obtain ⟨w, hw⟩ := hβ r
      rw [hw]
      exact ((F.box i).chart (a, w)).property
    let coords (r : unitInterval) := (F.box i).chart.symm ⟨p (β r), hmem r⟩
    have hc : Continuous coords := (F.box i).chart.symm.continuous.comp
      ((hp.continuous.comp β.continuous).subtype_mk hmem)
    have hfirst (r : unitInterval) : (coords r).1 = a := by
      obtain ⟨w, hw⟩ := hβ r
      have he : (⟨p (β r), hmem r⟩ : (F.box i).image) = (F.box i).chart (a, w) :=
        Subtype.ext hw
      simp [coords, he]
    let βL : unitInterval → IntrinsicFoliationLeaf F.unstablePartition q :=
      fun r ↦ plaque i a hlabel (coords r).2
    have hβL : Continuous βL := (hplaque i a hlabel).comp hc.snd
    have hval (r : unitInterval) : (βL r).val = p (β r) := by
      change ((F.box i).chart (a, (coords r).2)).val = p (β r)
      rw [← hfirst r]
      exact congrArg Subtype.val ((F.box i).chart.apply_symm_apply _)
    have hzero : βL 0 = v := Subtype.ext (by rw [hval, Path.source, ← hv, hproj])
    have heq : (fun r ↦ lift (βL r)) = β := hp.eq_of_comp_eq
      (hlift.comp hβL) β.continuous (funext (fun r ↦ (hproj _).trans (hval r)))
      0 (by rw [hzero, hv, Path.source])
    exact ⟨βL 1, by simpa only [Path.target] using congrFun heq 1⟩
  have hsymm {x z : E} (h : link x z) : link z x := by
    obtain ⟨i, a, β, hβ⟩ := h
    exact ⟨i, a, β.symm, fun r ↦ hβ (unitInterval.symm r)⟩
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    have : v ∈ S := by rw [hSuniv]; trivial
    exact this
  · intro hz
    have hinvariant : ∀ {x z : E}, Relation.EqvGen link x z → (x ∈ range lift ↔ z ∈ range lift) := by
      intro x z h
      induction h with
      | rel x z h => exact ⟨hstable h, hstable (hsymm h)⟩
      | refl x => rfl
      | symm x z h ih => exact ih.symm
      | trans x z w h h' ih ih' => exact ih.trans ih'
    exact (hinvariant hz).mp ⟨⟨p y, rfl⟩, hpoint⟩

set_option backward.isDefEq.respectTransparency false in
/-- The range of a pointed intrinsic stable-leaf lift equals its finite lifted plaque-chain class. -/
theorem projective_cover_stable_lift_range
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {E : Type v} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    (y : E) :
    let q := Quotient.mk F.stablePartition (p y)
    letI := F.stableTopology q
    ∀ (lift : IntrinsicFoliationLeaf F.stablePartition q → E),
      Continuous lift → lift ⟨p y, rfl⟩ = y →
      (∀ z, p (lift z) = z.val) →
      range lift = {z : E | Relation.EqvGen
        (fun x y ↦ ∃ i : F.boxIndex, ∃ w : FoliationCoordinateDisk t, ∃ β : Path x y,
          ∀ a : unitInterval, ∃ z : FoliationCoordinateDisk s,
            p (β a) = ((F.box i).chart (z, w)).val) y z} := by
  let F' := transposeProjectiveFoliations F
  let : ChartedSpace (Fin (t + s) → ℝ) M := Eq.mp (congrArg (fun n ↦ ChartedSpace (Fin n → ℝ) M) (Nat.add_comm s t))
      (inferInstance : ChartedSpace (Fin (s + t) → ℝ) M)
  exact projective_cover_unstable_lift_range F' p hp y

/-- On a complete affine unstable leaf, the lifted development is a biholomorphic coordinate onto a
once-punctured projective line, and the lifted leaf range equals its plaque-chain class. (Ghys,
§5 pp.597–598) -/
theorem projective_cover_unstable_complete_lift
    {s d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    [ChartedSpace (ComplexModel d) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F)
    (affine : AffineUnstableLeafStructures F C)
    (hcomplete : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q))
    (atlas : TransverseProjectiveAtlas F C)
    (hAtlas : ∀ c ∈ atlas.charts, ∀ x : M, ∀ z : F.ULeaf x,
      letI := F.unstableTopology (Quotient.mk F.unstablePartition x)
      letI := C.charts (Quotient.mk F.unstablePartition x)
      z.val ∈ c.domain F C →
      ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint F C x),
        z ∈ b.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ w in 𝓝 z, w ∈ b.source ∧ w.val ∈ c.domain F C ∧
            c.transverseCoordinate F C w.val = g • complexProjectiveLineFinite (b w))
    (hinc : ∀ x : M,
      letI := F.unstableTopology (Quotient.mk F.unstablePartition x)
      letI := C.charts (Quotient.mk F.unstablePartition x)
      ContMDiff (complexModel 1) (complexModel d) ∞ (Subtype.val : F.ULeaf x → M))
    {E : Type v} [TopologicalSpace E] [ChartedSpace (ComplexModel d) E]
    (p : E → M) (hp : IsCoveringMap p)
    (hlocal : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (D : C(E, ComplexProjectiveLine))
    (hD : ∀ y : E, ∃ c ∈ atlas.charts,
      ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ, ∃ V : Set E,
        IsOpen V ∧ y ∈ V ∧ MapsTo p V (c.domain F C) ∧
          ∀ z ∈ V, D z = g • c.transverseCoordinate F C (p z)) (y : E) :
    letI := F.unstableTopology (Quotient.mk F.unstablePartition (p y))
    letI := C.charts (Quotient.mk F.unstablePartition (p y))
    ∃ lift : F.ULeaf (p y) → E,
      ContMDiff (complexModel 1) (complexModel d) ∞ lift ∧
      Function.Injective lift ∧ lift (F.uPoint (p y)) = y ∧
      (∀ z, p (lift z) = z.val) ∧
      range lift = {z : E | Relation.EqvGen
        (fun x y ↦ ∃ i : F.boxIndex, ∃ z : FoliationCoordinateDisk s, ∃ β : Path x y,
          ∀ a : unitInterval, ∃ w : FoliationCoordinateDisk 2,
            p (β a) = ((F.box i).chart (z, w)).val) y z} ∧
      ∃ (pole : ComplexProjectiveLine) (e : OpenPartialHomeomorph (F.ULeaf (p y)) ComplexProjectiveLine),
        e.source = univ ∧ e.target = {pole}ᶜ ∧
        (∀ z, e z = D (lift z)) ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target := by
  let q := Quotient.mk F.unstablePartition (p y)
  let := F.unstableTopology q
  let := C.charts q
  obtain ⟨lift, hsmooth, hinj, hpoint, hproj⟩ :=
    projective_cover_unstable_pointed_lift F C affine hcomplete hinc p hp hlocal y
  refine ⟨lift, hsmooth, hinj, hpoint, hproj,
    projective_cover_unstable_lift_range F p hp y lift hsmooth.continuous hpoint hproj, ?_⟩
  apply complete_affine_projective_coordinate (affine.atPoint F C (p y)) (hcomplete q)
    (fun z ↦ D (lift z)) ?_ (F.uPoint (p y))
  intro z
  obtain ⟨c, hc, g, V, hV, hzV, hmaps, hformula⟩ := hD (lift z)
  obtain ⟨b, hb, hzb, h, hh⟩ := hAtlas c hc (p y) z (by
    rw [← hproj z]
    exact hmaps hzV)
  refine ⟨b, hb, hzb, g * h, ?_⟩
  have hnear := (hsmooth.continuous.tendsto z).eventually (hV.mem_nhds hzV)
  filter_upwards [hnear, hh] with w hw hhw
  rw [hformula _ hw, hproj, hhw.2.2, mul_smul]

/-- The local developing formula yields product neighborhoods whose first factor is an intrinsic
stable plaque and whose central slice is the stable leaf inclusion. (Ghys, §5 p.597; HPS, §7
p.115) -/
theorem projective_cover_local_stable_product
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F) (atlas : TransverseProjectiveAtlas F C)
    {E : Type v} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    (D : C(E, ComplexProjectiveLine))
    (hD : ∀ y : E, ∃ c ∈ atlas.charts,
      ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ, ∃ V : Set E,
        IsOpen V ∧ y ∈ V ∧ MapsTo p V (c.domain F C) ∧
          ∀ z ∈ V, D z = g • c.transverseCoordinate F C (p z)) (y : E) :
    let q := Quotient.mk F.stablePartition (p y)
    letI := F.stableTopology q
    ∃ (Vs : TopologicalSpace.Opens (IntrinsicFoliationLeaf F.stablePartition q))
      (W : TopologicalSpace.Opens ComplexProjectiveLine) (O : TopologicalSpace.Opens E),
      (⟨p y, rfl⟩ : IntrinsicFoliationLeaf F.stablePartition q) ∈ Vs ∧
      D y ∈ W ∧ y ∈ O ∧
      ∃ e : (Vs × W) ≃ₜ O,
        (∀ v w, D (e (v, w)) = w.val) ∧
        (∀ v w, w.val = D y → p (e (v, w)) = v.val.val) ∧
        (∀ v w, v.val.val = p y → w.val = D y → (e (v, w)).val = y) := by
  classical
  dsimp only
  let q := Quotient.mk F.stablePartition (p y)
  let := F.stableTopology q
  let : Nonempty (FoliationCoordinateDisk s) := ⟨⟨0, by simp⟩⟩
  let : Nonempty (FoliationCoordinateDisk 2) := ⟨⟨0, by simp⟩⟩
  obtain ⟨c, hc, g, V, hV, hyV, hmaps, hformula⟩ := hD y
  obtain ⟨hybox, hys, hyc⟩ := hmaps hyV
  let zw := (F.box c.box).chart.symm ⟨p y, hybox⟩
  have hzw : ((F.box c.box).chart zw).val = p y :=
    congrArg Subtype.val ((F.box c.box).chart.apply_symm_apply _)
  have hlabel : F.stableLabel c.box zw.2 = q := by
    rw [← F.stable_label c.box zw.1 zw.2, hzw]
  let plaque (z : FoliationCoordinateDisk s) : IntrinsicFoliationLeaf F.stablePartition q :=
    ⟨((F.box c.box).chart (z, zw.2)).val, (F.stable_label c.box z zw.2).trans hlabel⟩
  have hplaque : IsOpenEmbedding plaque := by
    have general (q' : Quotient F.stablePartition) (h' : F.stableLabel c.box zw.2 = q') :
        letI := F.stableTopology q'
        IsOpenEmbedding (fun z : FoliationCoordinateDisk s ↦
          (⟨((F.box c.box).chart (z, zw.2)).val, (F.stable_label c.box z zw.2).trans h'⟩ :
            IntrinsicFoliationLeaf F.stablePartition q')) := by
      subst q'
      let := F.stableTopology (F.stableLabel c.box zw.2)
      exact F.stable_plaque c.box zw.2
    exact general q hlabel
  let cs := hplaque.toOpenPartialHomeomorph plaque
  let mh : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine := {
    toEquiv := MulAction.toPerm g
    continuous_toFun := (projective_special_linear_action_contMDiff g).continuous
    continuous_invFun := (projective_special_linear_action_contMDiff g⁻¹).continuous }
  let ct := c.coordinate.transHomeomorph mh
  obtain ⟨b, hbsource, hbtarget, hbformula⟩ := projective_box_product_coordinates
    (F.box c.box).image (F.box c.box).isOpen_image (F.box c.box).chart cs ct
  have hyb : p y ∈ b.source := by
    rw [hbsource]
    exact ⟨zw, ⟨mem_univ _, hyc⟩, hzw⟩
  obtain ⟨sheet, hysheet, hsheet⟩ := hp.isLocalHomeomorph y
  let total := (sheet.restrOpen V hV).trans b
  have hytotal : y ∈ total.source := by
    refine ⟨⟨hysheet, hyV⟩, ?_⟩
    change sheet y ∈ b.source
    rwa [← hsheet]
  have hsecond (u : E) (hu : u ∈ total.source) : (total u).2 = D u := by
    have hbu : p u ∈ b.source := by
      have hh : sheet u ∈ b.source := hu.2
      rwa [← hsheet] at hh
    rw [hbsource] at hbu
    obtain ⟨⟨z,w⟩, hsource, heq⟩ := hbu
    change (b (sheet u)).2 = _
    rw [← hsheet, ← heq, hbformula, hformula u hu.1.2, ← heq]
    simp [ct, mh, TransverseProjectiveChart.transverseCoordinate]
    rfl
  have hfirsty : (total y).1 = (⟨p y, rfl⟩ : IntrinsicFoliationLeaf F.stablePartition q) := by
    apply Subtype.ext
    change (b (sheet y)).1.val = p y
    rw [← hsheet]
    conv_lhs => rw [← hzw, hbformula]
    exact hzw
  have hcentral (u : E) (hu : u ∈ total.source) (hDu : (total u).2 = D y) :
      p u = (total u).1.val := by
    have hbu : p u ∈ b.source := by
      have hh : sheet u ∈ b.source := hu.2
      rwa [← hsheet] at hh
    rw [hbsource] at hbu
    obtain ⟨⟨z,w⟩, hsource, heq⟩ := hbu
    have htrans : ct w = ct zw.2 := by
      calc
        ct w = (total u).2 := by change _ = (b (sheet u)).2; rw [← hsheet, ← heq, hbformula]
        _ = D y := hDu
        _ = (total y).2 := (hsecond y hytotal).symm
        _ = ct zw.2 := by change (b (sheet y)).2 = _; rw [← hsheet, ← hzw, hbformula]
    have hw : w = zw.2 := ct.injOn hsource.2 hyc htrans
    change p u = (b (sheet u)).1.val
    rw [← hsheet, ← heq, hbformula]
    change ((F.box c.box).chart (z,w)).val = ((F.box c.box).chart (z,zw.2)).val
    rw [hw]
  obtain ⟨S, W, hS, hyS, hW, hyW, hrect⟩ :=
    mem_nhds_prod_iff'.mp (total.open_target.mem_nhds (total.map_source hytotal))
  let er := total.symm.restrOpen (S ×ˢ W) (hS.prod hW)
  have hersource : er.source = S ×ˢ W := inter_eq_right.mpr hrect
  let Vs : TopologicalSpace.Opens (IntrinsicFoliationLeaf F.stablePartition q) := ⟨S,hS⟩
  let Ws : TopologicalSpace.Opens ComplexProjectiveLine := ⟨W,hW⟩
  let O : TopologicalSpace.Opens E := ⟨er.target, er.open_target⟩
  let e : (Vs × Ws) ≃ₜ O :=
    (Homeomorph.Set.prod S W).symm.trans
      ((Homeomorph.setCongr hersource.symm).trans er.toHomeomorphSourceTarget)
  have heval (v : Vs) (w : Ws) : (e (v,w)).val = total.symm (v.val,w.val) := rfl
  have heSource (v : Vs) (w : Ws) : (e (v,w)).val ∈ total.source :=
    total.map_target (hrect ⟨v.property,w.property⟩)
  have hecoord (v : Vs) (w : Ws) : total (e (v,w)) = (v.val,w.val) :=
    total.right_inv (hrect ⟨v.property,w.property⟩)
  refine ⟨Vs, Ws, O, ?_, ?_, ?_, e, ?_, ?_, ?_⟩
  · exact hfirsty ▸ hyS
  · exact hsecond y hytotal ▸ hyW
  · change y ∈ er.target
    exact ⟨hytotal, ⟨hyS,hyW⟩⟩
  · intro v w
    exact (hsecond _ (heSource v w)).symm.trans (congrArg Prod.snd (hecoord v w))
  · intro v w hw
    exact (hcentral _ (heSource v w) ((congrArg Prod.snd (hecoord v w)).trans hw)).trans
      (congrArg (fun z ↦ z.1.val) (hecoord v w))
  · intro v w hv hw
    apply total.injOn (heSource v w) hytotal
    rw [hecoord]
    apply Prod.ext
    · exact (Subtype.ext hv).trans hfirsty.symm
    · exact hw.trans (hsecond y hytotal).symm

/-- A transverse chart is locally constant on each intrinsic stable leaf. (HPS, §7 pp.115–116; Ghys,
§5 p.597) -/
theorem projective_transverse_coordinate_stable_eventually
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F) (c : TransverseProjectiveChart F C)
    (q : Quotient F.stablePartition) :
    letI := F.stableTopology q
    ∀ x : IntrinsicFoliationLeaf F.stablePartition q, x.val ∈ c.domain F C →
      ∀ᶠ z in 𝓝 x, c.transverseCoordinate F C z.val = c.transverseCoordinate F C x.val := by
  classical
  let := F.stableTopology q
  intro x hx
  obtain ⟨hxbox, hxs, hxc⟩ := hx
  let zw := (F.box c.box).chart.symm ⟨x.val, hxbox⟩
  have hzw : ((F.box c.box).chart zw).val = x.val :=
    congrArg Subtype.val ((F.box c.box).chart.apply_symm_apply _)
  have hlabel : F.stableLabel c.box zw.2 = q := by
    rw [← F.stable_label c.box zw.1 zw.2, hzw]
    exact x.property
  let plaque (z : FoliationCoordinateDisk s) : IntrinsicFoliationLeaf F.stablePartition q :=
    ⟨((F.box c.box).chart (z, zw.2)).val, (F.stable_label c.box z zw.2).trans hlabel⟩
  have hplaque : IsOpenEmbedding plaque := by
    have general (q' : Quotient F.stablePartition) (h' : F.stableLabel c.box zw.2 = q') :
        letI := F.stableTopology q'
        IsOpenEmbedding (fun z : FoliationCoordinateDisk s ↦
          (⟨((F.box c.box).chart (z, zw.2)).val, (F.stable_label c.box z zw.2).trans h'⟩ :
            IntrinsicFoliationLeaf F.stablePartition q')) := by
      subst q'
      let := F.stableTopology (F.stableLabel c.box zw.2)
      exact F.stable_plaque c.box zw.2
    exact general q hlabel
  have hxrange : x ∈ range plaque := ⟨zw.1, Subtype.ext hzw⟩
  filter_upwards [hplaque.isOpen_range.mem_nhds hxrange] with z hz
  obtain ⟨w, rfl⟩ := hz
  have hcoord (a : FoliationCoordinateDisk s) :
      c.transverseCoordinate F C (plaque a).val = c.coordinate zw.2 := by
    simp [plaque, TransverseProjectiveChart.transverseCoordinate]
  calc
    c.transverseCoordinate F C (plaque w).val = c.coordinate zw.2 := hcoord w
    _ = c.transverseCoordinate F C x.val := by
      rw [← hcoord zw.1]
      exact congrArg (c.transverseCoordinate F C) hzw

/-- A developing map is constant on each connected pointed intrinsic stable lift. (Ghys, §5 p.597) -/
theorem projective_cover_stable_lift_constant
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F) (atlas : TransverseProjectiveAtlas F C)
    {E : Type v} [TopologicalSpace E] (p : E → M)
    (D : C(E, ComplexProjectiveLine))
    (hD : ∀ y : E, ∃ c ∈ atlas.charts,
      ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ, ∃ V : Set E,
        IsOpen V ∧ y ∈ V ∧ MapsTo p V (c.domain F C) ∧
          ∀ z ∈ V, D z = g • c.transverseCoordinate F C (p z))
    (q : Quotient F.stablePartition) :
    letI := F.stableTopology q
    ∀ (lift : IntrinsicFoliationLeaf F.stablePartition q → E), Continuous lift →
      (∀ z, p (lift z) = z.val) → ∀ x z, D (lift x) = D (lift z) := by
  let := F.stableTopology q
  let := F.stable_connected q
  intro lift hlift hproj
  have hc : IsLocallyConstant (fun z ↦ D (lift z)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    obtain ⟨c, hc, g, V, hV, hzV, hmaps, hformula⟩ := hD (lift z)
    have hx : z.val ∈ c.domain F C := by rw [← hproj z]; exact hmaps hzV
    filter_upwards [(hlift.tendsto z).eventually (hV.mem_nhds hzV),
      projective_transverse_coordinate_stable_eventually F C c q z hx] with w hw hcw
    rw [hformula _ hw, hformula _ hzV, hproj, hproj, hcw]
  exact hc.apply_eq_of_preconnectedSpace

private def projectiveStableLeafRebase
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {q q' : Quotient F.stablePartition} (h : q = q') :
    letI := F.stableTopology q
    letI := F.stableTopology q'
    IntrinsicFoliationLeaf F.stablePartition q ≃ₜ IntrinsicFoliationLeaf F.stablePartition q' := by
  subst q'
  exact Homeomorph.refl _

private theorem projectiveStableLeafRebase_val
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M)
    {q q' : Quotient F.stablePartition} (h : q = q')
    (z : IntrinsicFoliationLeaf F.stablePartition q) :
    (projectiveStableLeafRebase F h z).val = z.val := by
  subst q'
  rfl

/-- The range of a pointed intrinsic stable lift equals the connected developing fibre component
through its marked point. (Ghys, §5 p.597; Hatcher, Prop. 1.34 p.62) -/
theorem projective_cover_stable_lift_fibre
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + 2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F) (atlas : TransverseProjectiveAtlas F C)
    {E : Type v} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    (D : C(E, ComplexProjectiveLine))
    (hD : ∀ y : E, ∃ c ∈ atlas.charts,
      ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ, ∃ V : Set E,
        IsOpen V ∧ y ∈ V ∧ MapsTo p V (c.domain F C) ∧
          ∀ z ∈ V, D z = g • c.transverseCoordinate F C (p z)) (y : E) :
    let q := Quotient.mk F.stablePartition (p y)
    letI := F.stableTopology q
    ∀ (lift : IntrinsicFoliationLeaf F.stablePartition q → E), Continuous lift →
      Function.Injective lift → lift ⟨p y, rfl⟩ = y → (∀ z, p (lift z) = z.val) →
      range lift = connectedComponentIn (D ⁻¹' {D y}) y := by
  classical
  dsimp only
  let q := Quotient.mk F.stablePartition (p y)
  let := F.stableTopology q
  let := F.stable_connected q
  intro lift hlift hinj hpoint hproj
  apply subset_antisymm
  · apply (isPreconnected_range hlift).subset_connectedComponentIn ⟨⟨p y,rfl⟩,hpoint⟩
    rintro z ⟨w,rfl⟩
    change D (lift w) = D y
    rw [← hpoint]
    exact projective_cover_stable_lift_constant F C atlas p D hD q lift hlift hproj _ _
  · have hfactor (x : E) :
        let qx := Quotient.mk F.stablePartition (p x)
        letI := F.stableTopology qx
        ∃ O : TopologicalSpace.Opens E, x ∈ O ∧
          ∃ v : C(O, IntrinsicFoliationLeaf F.stablePartition qx),
            ∀ z : O, D z = D x → (v z).val = p z := by
      let qx := Quotient.mk F.stablePartition (p x)
      let := F.stableTopology qx
      obtain ⟨Vs,W,O,hVs,hW,hO,e,hsecond,hcentral,_⟩ :=
        projective_cover_local_stable_product F C atlas p hp D hD x
      refine ⟨O,hO,⟨fun z ↦ (e.symm z).1.val,
        continuous_subtype_val.comp (continuous_fst.comp e.symm.continuous)⟩,?_⟩
      intro z hz
      have hw : (e.symm z).2.val = D x := by
        have hh := hsecond (e.symm z).1 (e.symm z).2
        simp only [Prod.mk.eta, e.apply_symm_apply] at hh
        exact hh.symm.trans hz
      have hh := hcentral (e.symm z).1 (e.symm z).2 hw
      change (e.symm z).1.val.val = p z
      simpa only [Prod.mk.eta, e.apply_symm_apply] using hh.symm
    let K := connectedComponentIn (D ⁻¹' {D y}) y
    let : PreconnectedSpace K := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    let yK : K := ⟨y, mem_connectedComponentIn rfl⟩
    have hvalue (z : K) : D z.val = D y := by
      have hz : z.val ∈ D ⁻¹' {D y} := connectedComponentIn_subset (D ⁻¹' {D y}) y z.property
      exact hz
    let label (z : K) := Quotient.mk F.stablePartition (p z.val)
    have hlabel : IsLocallyConstant label := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro z
      obtain ⟨O,hO,v,hv⟩ := hfactor z.val
      filter_upwards [((continuous_subtype_val : Continuous (Subtype.val : K → E)).tendsto z).eventually
        (O.isOpen.mem_nhds hO)] with w hw
      have hh := (v ⟨w.val,hw⟩).property
      rw [hv _ ((hvalue w).trans (hvalue z).symm)] at hh
      exact hh
    have hclass (z : K) : Quotient.mk F.stablePartition (p z.val) = q :=
      hlabel.apply_eq_of_preconnectedSpace z yK
    let into : K → IntrinsicFoliationLeaf F.stablePartition q := fun z ↦ ⟨p z.val,hclass z⟩
    have hinto : Continuous into := by
      rw [continuous_iff_continuousAt]
      intro z
      obtain ⟨O,hO,v,hv⟩ := hfactor z.val
      let U : Set K := (Subtype.val : K → E) ⁻¹' O
      have hU : IsOpen U := O.isOpen.preimage continuous_subtype_val
      have hzU : z ∈ U := hO
      let base : U → O := fun w ↦ ⟨w.val.val,w.property⟩
      have hbase : Continuous base := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      let rebase := projectiveStableLeafRebase F (hclass z)
      have hh : Continuous (fun w : U ↦ into w.val) := by
        apply (rebase.continuous.comp (v.continuous.comp hbase)).congr
        intro w
        apply Subtype.ext
        exact (projectiveStableLeafRebase_val F (hclass z) _).trans
          (hv _ ((hvalue w.val).trans (hvalue z).symm))
      exact (continuousOn_iff_continuous_domRestrict.mpr hh).continuousAt (hU.mem_nhds hzU)
    have heq : lift ∘ into = (Subtype.val : K → E) := hp.eq_of_comp_eq
      (hlift.comp hinto) continuous_subtype_val (funext fun z ↦ hproj (into z)) yK (by
        have hmark : into yK = ⟨p y,rfl⟩ := Subtype.ext rfl
        exact (congrArg lift hmark).trans hpoint)
    intro z hz
    exact ⟨into ⟨z,hz⟩,congrFun heq ⟨z,hz⟩⟩

/-- A transverse projective atlas compatible with complete affine unstable leaves develops on a
specified simply connected covering, with deck holonomy, stable fibre components, and
biholomorphic unstable leaf coordinates onto punctured projective lines. (Ghys, §5 pp.597–599;
Thurston, §3.5 pp.34–35 and §4.8 p.63) -/
theorem projective_cover_development_global_assembly_data_gap
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (atlas : letI := A.realAmbientCharts; TransverseProjectiveAtlas A.F C)
    (affine : letI := A.realAmbientCharts; AffineUnstableLeafStructures A.F C)
    (hcomplete : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
      letI := A.F.unstableTopology q
      letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q))
    (hAtlas : letI := A.realAmbientCharts
      ∀ c ∈ atlas.charts, ∀ x : M, ∀ z : A.F.ULeaf x,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      z.val ∈ c.domain A.F C →
      ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint A.F C x),
        z ∈ b.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ w in 𝓝 z,
            w ∈ b.source ∧ w.val ∈ c.domain A.F C ∧
              c.transverseCoordinate A.F C w.val = g • complexProjectiveLineFinite (b w))
    (hCinc : letI := A.realAmbientCharts
      ∀ x : M,
        letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
        letI := C.charts (Quotient.mk A.F.unstablePartition x)
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : A.F.ULeaf x → M))
    (x₀ : M) :
    letI := A.realAmbientCharts
    ∀ (E : Type v) [TopologicalSpace E] [SimplyConnectedSpace E]
      (p : E → M) (_hp : IsCoveringMap p) (y₀ : E),
      p y₀ = x₀ → Set.range p = connectedComponent x₀ →
      let stableLink : E → E → Prop := fun x y ↦
        ∃ i : A.F.boxIndex, ∃ w : FoliationCoordinateDisk 2, ∃ β : Path x y,
          ∀ t : unitInterval, ∃ z : FoliationCoordinateDisk s,
            p (β t) = ((A.F.box i).chart (z, w)).val
      let unstableLink : E → E → Prop := fun x y ↦
        ∃ i : A.F.boxIndex, ∃ z : FoliationCoordinateDisk s, ∃ β : Path x y,
          ∀ t : unitInterval, ∃ w : FoliationCoordinateDisk 2,
            p (β t) = ((A.F.box i).chart (z, w)).val
      ∃ charts : ChartedSpace (ComplexModel d) E,
      letI := charts
      ∃ smooth : IsManifold (complexModel d) ∞ E,
      letI := smooth
      IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p ∧
      ∃ D : C(E, ComplexProjectiveLine),
        (∀ y : E,
          let q := Quotient.mk A.F.stablePartition (p y)
          letI := A.F.stableTopology q
          ∃ (Vs : TopologicalSpace.Opens (IntrinsicFoliationLeaf A.F.stablePartition q))
            (W : TopologicalSpace.Opens ComplexProjectiveLine)
            (O : TopologicalSpace.Opens E),
            (⟨p y, rfl⟩ : IntrinsicFoliationLeaf A.F.stablePartition q) ∈ Vs ∧
            D y ∈ W ∧ y ∈ O ∧
            ∃ e : (Vs × W) ≃ₜ O,
              (∀ v w, D (e (v, w)) = w.val) ∧
              (∀ v w, w.val = D y → p (e (v, w)) = v.val.val) ∧
              (∀ v w, v.val.val = p y → w.val = D y → (e (v, w)).val = y)) ∧
        (∀ y : E, ∃ c ∈ atlas.charts,
          ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ, ∃ V : Set E,
            IsOpen V ∧ y ∈ V ∧ Set.MapsTo p V (c.domain A.F C) ∧
              ∀ z ∈ V, D z = g • c.transverseCoordinate A.F C (p z)) ∧
        ∃ action : FundamentalGroup M (p y₀) ≃* deck p,
          (∀ α : Path (p y₀) (p y₀),
            ∃ β : Path y₀ ((action (FundamentalGroup.fromPath
                (Path.Homotopic.Quotient.mk α)))⁻¹ • y₀),
              ∀ t, p (β t) = α t) ∧
          ∃ H : FundamentalGroup M (p y₀) →*
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
            (∀ γ y, D (action γ • y) = H γ • D y) ∧
            (∀ y : E,
              let q := Quotient.mk A.F.stablePartition (p y)
              letI := A.F.stableTopology q
              ∃ lift : IntrinsicFoliationLeaf A.F.stablePartition q → E,
                Continuous lift ∧ Function.Injective lift ∧
                lift ⟨p y, rfl⟩ = y ∧ (∀ z, p (lift z) = z.val) ∧
                Set.range lift = {z : E | Relation.EqvGen stableLink y z} ∧
                Set.range lift = connectedComponentIn (D ⁻¹' {D y}) y) ∧
            (∀ y : E,
              letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition (p y))
              letI := C.charts (Quotient.mk A.F.unstablePartition (p y))
              ∃ lift : A.F.ULeaf (p y) → E,
                ContMDiff (complexModel 1) (complexModel d) ∞ lift ∧
                Function.Injective lift ∧ lift (A.F.uPoint (p y)) = y ∧
                (∀ z, p (lift z) = z.val) ∧
                Set.range lift = {z : E | Relation.EqvGen unstableLink y z} ∧
                ∃ (pole : ComplexProjectiveLine)
                  (e : OpenPartialHomeomorph (A.F.ULeaf (p y)) ComplexProjectiveLine),
                  e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
                  (∀ z, e z = D (lift z)) ∧
                  ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
                  ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target) := by
  classical
  let := A.realAmbientCharts
  intro E _ _ p hp y₀ hbase hrange
  dsimp only
  obtain ⟨charts,smooth,hlocal⟩ := projective_cover_component_charts (d := d) p hp
  refine ⟨charts, ?_⟩
  let := charts
  refine ⟨smooth, ?_⟩
  let := smooth
  obtain ⟨D,hD,H,hH⟩ := projective_cover_developing_map f a s A C atlas x₀ E p hp y₀ hbase hrange
  obtain ⟨endpoint⟩ := projective_cover_deck_endpoint_gap f a s A C atlas x₀ E p hp y₀ hbase hrange
  refine ⟨hlocal,D,projective_cover_local_stable_product A.F C atlas p hp D hD,hD,
    endpoint.action,endpoint.endpoint_lift,H.comp endpoint.action.toMonoidHom,
    fun γ y ↦ hH (endpoint.action γ) y, ?_, ?_⟩
  · intro y
    let q := Quotient.mk A.F.stablePartition (p y)
    let := A.F.stableTopology q
    let := A.F.stableCharts q
    let N := A.nativeS (p y)
    let := N.topology
    let := N.charts
    let := N.smoothAtlas
    let := N.connected
    let j := A.stableIdentification (p y)
    obtain ⟨nativeLift,hninj,hnpoint,hnproj⟩ := stable_tangent_immersion_pointed_lift
      f a (Subtype.val : StableAsymptoticLeaf f.toHomeomorph (p y) → M)
      N.inclusion_smooth Subtype.val_injective (fun z v ↦ by
        rw [← N.tangent_image z]
        exact ⟨v,rfl⟩) hp (j ⟨p y,rfl⟩) y (by
          exact (A.stable_points (p y) ⟨p y,rfl⟩).symm)
    let lift : C(IntrinsicFoliationLeaf A.F.stablePartition q,E) :=
      ⟨nativeLift ∘ j,nativeLift.continuous.comp j.continuous⟩
    have hinj : Function.Injective lift := hninj.comp j.injective
    have hproj : ∀ z, p (lift z) = z.val := fun z ↦
      (hnproj (j z)).trans (A.stable_points (p y) z)
    have hpoint' : lift ⟨p y,rfl⟩ = y := hnpoint
    exact ⟨lift,lift.continuous,hinj,hpoint',hproj,
      projective_cover_stable_lift_range A.F p hp y lift lift.continuous hpoint' hproj,
      projective_cover_stable_lift_fibre A.F C atlas p hp D hD y lift lift.continuous hinj hpoint' hproj⟩
  · exact projective_cover_unstable_complete_lift A.F C affine hcomplete atlas hAtlas hCinc p hp hlocal D hD


abbrev projective_cover_development_global_assembly_core_gap :=
  @projective_cover_development_global_assembly_data_gap

abbrev projective_cover_development_global_assembly_gap :=
  @projective_cover_development_global_assembly_core_gap

abbrev projective_cover_development_gap :=
  @projective_cover_development_global_assembly_gap

/-- The transverse projective atlas has a global development with deck holonomy and the stated
intrinsic stable and unstable leaf properties. -/
abbrev projective_cover_development := @projective_cover_development_gap


end HolomorphicAnosov.Ghys
