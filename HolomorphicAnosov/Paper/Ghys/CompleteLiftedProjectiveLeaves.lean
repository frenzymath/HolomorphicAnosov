import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import Mathlib.Topology.Connected.Basic

/-! This file defines lifted stable and unstable developing leaves, their saturation, and
completeness of their projective coordinates. (Ghys, Lemma 5.2, pp. 598–599) -/

noncomputable section
open Set Topology _root_.Topology
open scoped ContDiff

namespace HolomorphicAnosov.Ghys

universe u v w

attribute [local instance] complex_isManifold_real

variable {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
  [IsManifold (complexModel 2) ∞ S] {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
  {A : OrderedProjectiveProductAtlas.{u, v} f a}
  {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
  [IsManifold (complexModel 2) ∞ U] {p : U → S}

/-- The stable developing leaf through `x` is the connected component of its second-coordinate
fibre. (Ghys, pp. 598–599) -/
def stableDevelopingLeaf (D : OrderedProjectiveProductDevelopment A p) (x : U) : Set U :=
  connectedComponentIn {y | (D.developingMap y).2 = (D.developingMap x).2} x

/-- The unstable developing leaf through `x` is the connected component of its first-coordinate
fibre. (Ghys, pp. 598–599) -/
def unstableDevelopingLeaf (D : OrderedProjectiveProductDevelopment A p) (x : U) : Set U :=
  connectedComponentIn {y | (D.developingMap y).1 = (D.developingMap x).1} x

/-- The union of the unstable developing leaves meeting the stable developing leaf through `x`.
(Ghys, Lemma 5.2, p. 599) -/
def unstableSaturation (D : OrderedProjectiveProductDevelopment A p) (x : U) : Set U :=
  {z | ∃ y ∈ stableDevelopingLeaf D x, z ∈ unstableDevelopingLeaf D y}

/-- Each intrinsic stable and unstable leaf has an injective holomorphic lift whose range is the
corresponding developing fibre component and whose varying coordinate is a biholomorphism onto a
punctured projective line. (Ghys, Lemma 5.2, pp. 598–599; Prop. 3.1, p. 590) -/
def CompleteLiftedProjectiveLeaves (D : OrderedProjectiveProductDevelopment A p) : Prop :=
  letI : MetricSpace S := A.metric.replaceTopology A.metric_topology
  (∀ u : U,
    let L := A.stableLeaf (p u)
    letI := L.native.topology
    letI := L.complexCharts
    ∃ lift : StableAsymptoticLeaf f.toHomeomorph (p u) → U,
      ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
      Function.Injective lift ∧
      (∀ z, p (lift z) = z.val) ∧
      Set.range lift = stableDevelopingLeaf D u ∧
      ∃ (pole : ComplexProjectiveLine)
        (e : OpenPartialHomeomorph
          (StableAsymptoticLeaf f.toHomeomorph (p u)) ComplexProjectiveLine),
        e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
        (∀ z, e z = (D.developingMap (lift z)).1) ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target ∧
        Set.range (fun z ↦ D.developingMap (lift z)) =
          {q | q.1 ≠ pole ∧ q.2 = (D.developingMap u).2}) ∧
  (∀ u : U,
    let L := A.unstableLeaf (p u)
    letI := L.native.topology
    letI := L.complexCharts
    ∃ lift : UnstableAsymptoticLeaf f.toHomeomorph (p u) → U,
      ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
      Function.Injective lift ∧
      (∀ z, p (lift z) = z.val) ∧
      Set.range lift = unstableDevelopingLeaf D u ∧
      ∃ (pole : ComplexProjectiveLine)
        (e : OpenPartialHomeomorph
          (UnstableAsymptoticLeaf f.toHomeomorph (p u)) ComplexProjectiveLine),
        e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
        (∀ z, e z = (D.developingMap (lift z)).2) ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
        ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target ∧
        Set.range (fun z ↦ D.developingMap (lift z)) =
          {q | q.1 = (D.developingMap u).1 ∧ q.2 ≠ pole})

end HolomorphicAnosov.Ghys
