import HolomorphicAnosov.Topology.CoveringDeckBetweenPoints
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic
import HolomorphicAnosov.Paper.Ghys.SurfaceDomainDichotomy
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphExclusionLeafProjection
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.SurfaceMobiusFixedPoint
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveProduct
import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.Clopen

/-!
Exclusion of the homeomorphism graph complement as the developed domain of a compact
holomorphic Anosov surface. (Ghys, Theorem A, p. 600, case (i); Hatcher,
Props. 1.33–1.34, pp. 61–63, pp. 70–71)
-/

open Set _root_.Topology
open scoped ContDiff




namespace HolomorphicAnosov.Ghys

universe u v w

/-- For a compact holomorphic Anosov surface with complete lifted projective leaves and a
Hausdorff connected nontrivial projective line, the developing range cannot be the
complement of a projective-line homeomorphism graph.
(Ghys, p. 600, case (i); Hatcher, pp. 61–63, 70–71) -/
theorem surface_graph_domain_excluded_of_native_topology
    [T2Space ComplexProjectiveLine] [ConnectedSpace ComplexProjectiveLine]
    [Nontrivial ComplexProjectiveLine]
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {X : Type w} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
    [IsManifold (complexModel 2) ∞ X] {p : X → S}
    (D : OrderedProjectiveProductDevelopment A p)
    (hLeaves : CompleteLiftedProjectiveLeaves D) :
    ¬ ∃ h : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine,
      Set.range D.developingMap = {z | z.2 ≠ h z.1} := by
  classical
  let := D.simplyConnected
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace
    (H := ComplexModel 2) (M := X)
  intro hex
  obtain ⟨h, hRange⟩ := hex
  have hD := (surface_domain_dichotomy f a A D hLeaves).1
  have hp : ¬ Function.Injective p := by
    intro hinj
    let e := D.covering.isLocalHomeomorph.toHomeomorphOfBijective ⟨hinj, D.surjective⟩
    let : CompactSpace X := e.symm.surjective.compactSpace e.symm.continuous
    have hc : IsClopen (Set.range D.developingMap) :=
      ⟨(isCompact_range D.localBiholomorph.isLocalHomeomorph.continuous).isClosed,
        by simpa only [Set.image_univ] using
          D.localBiholomorph.isLocalHomeomorph.isOpenMap Set.univ isOpen_univ⟩
    have hall := hc.eq_univ (Set.range_nonempty D.developingMap)
    let s : ComplexProjectiveLine := Classical.arbitrary _
    have hbad : (s, h s) ∈ Set.range D.developingMap := hall.symm ▸ Set.mem_univ _
    rw [hRange] at hbad
    exact hbad rfl
  obtain ⟨x₀, x₁, hproj, hne⟩ := Function.not_injective_iff.mp hp
  obtain ⟨γ, hγ⟩ := covering_deck_between_points D.covering x₀ x₁ hproj
  have hγne : γ ≠ 1 := by
    intro he
    have : x₀ = x₁ := by simpa only [he, one_smul] using hγ
    exact hne this
  let g := (D.holonomy γ).1
  obtain ⟨s, hs⟩ := surface_mobius_fixed_point g
  obtain ⟨t, ht⟩ := exists_ne (h s)
  have hm : (s, t) ∈ Set.range D.developingMap := by rw [hRange]; exact ht
  obtain ⟨x, hx⟩ := hm
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  obtain ⟨lift, _, _, hlproj, hlrange, pole, e, _, _, _, _, _, heRange⟩ := hLeaves.2 x
  have hpole : pole = h s := by
    by_contra hn
    have hb : (s, h s) ∈ Set.range (fun z ↦ D.developingMap (lift z)) := by
      rw [heRange]
      exact ⟨(congrArg Prod.fst hx).symm, Ne.symm hn⟩
    obtain ⟨z, hz⟩ := hb
    have : (s, h s) ∈ Set.range D.developingMap := ⟨lift z, hz⟩
    rw [hRange] at this
    exact this rfl
  have hxleaf : x ∈ Set.range lift := by
    rw [hlrange]
    exact mem_connectedComponentIn rfl
  obtain ⟨z₀, hz₀⟩ := hxleaf
  have hγfirst : (D.developingMap (γ • x)).1 = s := by
    rw [D.equivariant, hx]
    exact hs
  have hγsecond : (D.developingMap (γ • x)).2 ≠ pole := by
    rw [hpole]
    have hmγ : D.developingMap (γ • x) ∈ Set.range D.developingMap := Set.mem_range_self _
    rw [hRange] at hmγ
    change (D.developingMap (γ • x)).2 ≠ h (D.developingMap (γ • x)).1 at hmγ
    simpa only [hγfirst] using hmγ
  have hγleaf : D.developingMap (γ • x) ∈
      Set.range (fun z ↦ D.developingMap (lift z)) := by
    rw [heRange]
    exact ⟨hγfirst.trans (congrArg Prod.fst hx).symm, hγsecond⟩
  obtain ⟨z₁, hz₁⟩ := hγleaf
  have hlγ : lift z₁ = γ • x := hD hz₁
  have hzval : z₁.val = z₀.val := by
    calc
      z₁.val = p (lift z₁) := (hlproj z₁).symm
      _ = p (γ • x) := congrArg p hlγ
      _ = p x := deck.proj_smul γ x
      _ = p (lift z₀) := congrArg p hz₀.symm
      _ = z₀.val := hlproj z₀
  have hz : z₁ = z₀ := Subtype.ext hzval
  have hfixed : γ • x = x := by rw [← hlγ, hz, hz₀]
  have hid : (γ : X ≃ₜ X) = Homeomorph.refl X := by
    apply Homeomorph.ext
    exact congrFun (D.covering.eq_of_comp_eq
      (γ : X ≃ₜ X).continuous continuous_id γ.property x hfixed)
  apply hγne
  exact Subtype.ext hid


/-- The developing range of a compact holomorphic Anosov surface with complete lifted
projective leaves cannot be the complement of a projective-line homeomorphism graph.
(Ghys, p. 600, case (i)) -/
theorem surface_graph_domain_excluded
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {X : Type w} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
    [IsManifold (complexModel 2) ∞ X] {p : X → S}
    (D : OrderedProjectiveProductDevelopment A p)
    (hLeaves : CompleteLiftedProjectiveLeaves D) :
    ¬ ∃ h : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine,
      Set.range D.developingMap = {z | z.2 ≠ h z.1} := by
  let : Nontrivial ComplexProjectiveLine :=
    NativeProjectiveTopology.nontrivial_native_projective_line
  let : ConnectedSpace ComplexProjectiveLine :=
    NativeProjectiveTopology.connected_native_projective_line
  let : T2Space ComplexProjectiveLine := NativeProjectiveTopology.t2_native_projective_line
  exact surface_graph_domain_excluded_of_native_topology f a A D hLeaves


end HolomorphicAnosov.Ghys
