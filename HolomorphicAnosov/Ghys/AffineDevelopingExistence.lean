import HolomorphicAnosov.Ghys.AffineChartChangeCocycle
import HolomorphicAnosov.Topology.DiscreteBundleSection
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.UnitInterval
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import HolomorphicAnosov.Topology.OpenCoverPathSubdivision
import HolomorphicAnosov.Ghys.AffineProjectiveStructure



open Set Filter _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov.Ghys

universe u


theorem affine_developing_exists
    (L : Type u) [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [IsManifold (complexModel 1) ∞ L] [T2Space L] [SecondCountableTopology L]
    [ConnectedSpace L] [SimplyConnectedSpace L] (A : ComplexAffineAtlas L) :
    ∃ D : L → ℂ, ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = a.apply (c y) := by
  classical
  let : TopologicalSpace ComplexAffineTransformation := ⊥
  let : DiscreteTopology ComplexAffineTransformation := ⟨rfl⟩
  obtain ⟨κ, hspec, hself, hcomp, hconst⟩ := affine_chart_change_cocycle A
  let Z : FiberBundleCore A.charts L ComplexAffineTransformation :=
    { baseSet := fun c ↦ c.val.source
      isOpen_baseSet := fun c ↦ c.val.open_source
      indexAt := fun x ↦ ⟨(A.cover x).choose, (A.cover x).choose_spec.1⟩
      mem_baseSet_at := fun x ↦ (A.cover x).choose_spec.2
      coordChange := κ
      coordChange_self := hself
      coordChange_comp := hcomp
      continuousOn_coordChange := by
        intro c d p hp
        apply ContinuousAt.continuousWithinAt
        rw [continuousAt_prod_of_discrete_right]
        exact continuousAt_const.congr_of_eventuallyEq (hconst c d p.1 hp.1 p.2) }
  have : Nonempty ComplexAffineTransformation :=
    ⟨{ slope := 1, slope_ne_zero := one_ne_zero, translation := 0 }⟩
  have : LocallyPathConnectedSpace L := ChartedSpace.locallyPathConnectedSpace (ComplexModel 1) L
  obtain ⟨s, hproj, hcoords⟩ := discrete_bundleCore_section Z
  let D : L → ℂ := fun x ↦ (s x).snd.apply ((Z.indexAt (s x).proj).val x)
  refine ⟨D, ?_⟩
  intro c hc x hx
  let i : A.charts := ⟨c, hc⟩
  let t := Z.localTriv i
  have hconstant : ∀ᶠ y in 𝓝 x, (t (s y)).2 = (t (s x)).2 := hcoords i x hx
  refine ⟨(t (s x)).2, ?_⟩
  have hformula (y : L) (hy : y ∈ c.source) :
      D y = (t (s y)).2.apply (c y) := by
    have hcy : (s y).proj ∈ c.source := by simpa only [hproj y] using hy
    have h := (hspec (Z.indexAt (s y).proj) i (s y).proj
      ⟨Z.mem_baseSet_at _, hcy⟩ (s y).snd).self_of_nhds
    change (s y).snd.apply ((Z.indexAt (s y).proj).val y) =
      (κ (Z.indexAt (s y).proj) i (s y).proj (s y).snd).apply (c y)
    simpa only [hproj y] using h
  filter_upwards [hconstant, c.open_source.mem_nhds hx] with y hy hcy
  rw [hformula y hcy, hy]

end HolomorphicAnosov.Ghys

