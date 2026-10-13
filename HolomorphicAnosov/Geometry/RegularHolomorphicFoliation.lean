import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Regular holomorphic foliations have product charts with transverse transition coordinates
depending only on transverse coordinates. Their leaves are plaque-equivalence classes with
intrinsic complex manifold structures. (Nisoli, Defs. 1.1.1–1.1.3, pp.9–10) -/

namespace HolomorphicAnosov

noncomputable section

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v

set_option autoImplicit false

/-- The open unit ball in `ComplexModel r`. (Nisoli, Def. 1.1.1, p.9) -/
def complexFoliationDisk (r : ℕ) : Opens (ComplexModel r) :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- A regular holomorphic foliation consists of holomorphic product charts with transverse overlap
laws and plaque-generated leaves. Each leaf has an intrinsic complex manifold structure for
which its plaques are holomorphic charts and its inclusion is a holomorphic immersion. (Nisoli,
Defs. 1.1.1–1.1.3, pp.9–10) -/
structure RegularHolomorphicFoliation (d r c : ℕ) (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] where
  dimension : d = r + c
  boxIndex : Type v
  box : boxIndex → OpenPartialHomeomorph M (ComplexModel r × ComplexModel c)
  box_target : ∀ i, (box i).target =
    (complexFoliationDisk r : Set (ComplexModel r)) ×ˢ
      (complexFoliationDisk c : Set (ComplexModel c))
  cover : ∀ x : M, ∃ i, x ∈ (box i).source
  box_holomorphic : ∀ i,
    ContMDiffOn (complexModel d) ((complexModel r).prod (complexModel c)) ∞
      (box i) (box i).source
  box_inverse_holomorphic : ∀ i,
    ContMDiffOn ((complexModel r).prod (complexModel c)) (complexModel d) ∞
      (box i).symm (box i).target
  transverse_overlap : ∀ i j z,
    z ∈ (box i).target → (box i).symm z ∈ (box j).source →
    ∃ W : Set (ComplexModel r × ComplexModel c), IsOpen W ∧ z ∈ W ∧
      W ⊆ (box i).target ∩ (box i).symm ⁻¹' (box j).source ∧
      ∀ a ∈ W, ∀ b ∈ W, a.2 = b.2 →
        ((box j) ((box i).symm a)).2 = ((box j) ((box i).symm b)).2
  partition : Setoid M
  partition_generated : ∀ x y : M, partition x y ↔ Relation.EqvGen
    (fun a b ↦ ∃ i : boxIndex, ∃ w : complexFoliationDisk c,
      ∃ z z' : complexFoliationDisk r,
        (box i).symm (z.val, w.val) = a ∧
        (box i).symm (z'.val, w.val) = b) x y
  leafTopology : ∀ q : Quotient partition,
    TopologicalSpace (IntrinsicFoliationLeaf partition q)
  leafCharts : ∀ q : Quotient partition,
    letI := leafTopology q
    ChartedSpace (ComplexModel r) (IntrinsicFoliationLeaf partition q)
  leafManifold : ∀ q : Quotient partition,
    letI := leafTopology q
    letI := leafCharts q
    IsManifold (complexModel r) ∞ (IntrinsicFoliationLeaf partition q)
  leafConnected : ∀ q : Quotient partition,
    letI := leafTopology q
    ConnectedSpace (IntrinsicFoliationLeaf partition q)
  leafHausdorff : ∀ q : Quotient partition,
    letI := leafTopology q
    T2Space (IntrinsicFoliationLeaf partition q)
  leafCountable : ∀ q : Quotient partition,
    letI := leafTopology q
    SecondCountableTopology (IntrinsicFoliationLeaf partition q)
  label : ∀ _i : boxIndex, complexFoliationDisk c → Quotient partition
  label_eq : ∀ i (a : complexFoliationDisk r) (b : complexFoliationDisk c),
    Quotient.mk partition ((box i).symm (a.val, b.val)) = label i b
  plaque : ∀ i (b : complexFoliationDisk c),
    letI := leafTopology (label i b)
    Opens (IntrinsicFoliationLeaf partition (label i b))
  plaqueChart : ∀ i (b : complexFoliationDisk c),
    letI := leafTopology (label i b)
    letI := leafCharts (label i b)
    Diffeomorph (complexModel r) (complexModel r)
      (complexFoliationDisk r) (plaque i b) ∞
  plaqueChart_eq : ∀ i (a : complexFoliationDisk r) (b : complexFoliationDisk c),
    ((plaqueChart i b a).val).val = (box i).symm (a.val, b.val)
  topology_generated : ∀ q (W : Set (IntrinsicFoliationLeaf partition q)),
    letI := leafTopology q
    IsOpen W ↔ ∀ i (b : complexFoliationDisk c) (h : label i b = q),
      IsOpen ((fun a : complexFoliationDisk r ↦
        (⟨(box i).symm (a.val, b.val), (label_eq i a b).trans h⟩ :
          IntrinsicFoliationLeaf partition q)) ⁻¹' W)
  inclusion_holomorphic : ∀ q : Quotient partition,
    letI := leafTopology q
    letI := leafCharts q
    ContMDiff (complexModel r) (complexModel d) ∞
      (fun x : IntrinsicFoliationLeaf partition q ↦ x.val)
  inclusion_immersion : ∀ q : Quotient partition,
    letI := leafTopology q
    letI := leafCharts q
    ∀ x : IntrinsicFoliationLeaf partition q,
      Function.Injective (mfderiv (complexModel r) (complexModel d)
        (fun y : IntrinsicFoliationLeaf partition q ↦ y.val) x)

namespace RegularHolomorphicFoliation

variable {d r c : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

/-- The leaf of `F` through `x`. (Nisoli, Def. 1.1.3, p.10) -/
abbrev Leaf (F : RegularHolomorphicFoliation.{u, v} d r c M) (x : M) :=
  IntrinsicFoliationLeaf F.partition (Quotient.mk F.partition x)

/-- The intrinsic topology of the leaf through `x`. (Nisoli, pp.9–10) -/
instance leafTopologicalSpace (F : RegularHolomorphicFoliation.{u, v} d r c M) (x : M) :
    TopologicalSpace (F.Leaf x) := F.leafTopology (Quotient.mk F.partition x)

/-- The intrinsic complex atlas of the leaf through `x`. (Nisoli, pp.9–10) -/
instance leafChartedSpace (F : RegularHolomorphicFoliation.{u, v} d r c M) (x : M) :
    ChartedSpace (ComplexModel r) (F.Leaf x) := F.leafCharts (Quotient.mk F.partition x)

/-- The plaque-generated leaf atlas defines a complex manifold. (Nisoli, pp.9–10) -/
instance leafIsManifold (F : RegularHolomorphicFoliation.{u, v} d r c M) (x : M) :
    IsManifold (complexModel r) ∞ (F.Leaf x) := F.leafManifold (Quotient.mk F.partition x)

/-- The tangent subspace of the foliation at `x` is the range of the derivative of the leaf
inclusion. (Nisoli, Def. 1.1.1, pp.9–10) -/
def tangent (F : RegularHolomorphicFoliation.{u, v} d r c M) (x : M) :
    Submodule ℂ (TangentSpace (complexModel d) x) :=
  (mfderiv (complexModel r) (complexModel d)
    (fun y : F.Leaf x ↦ y.val) ⟨x, rfl⟩).range

end RegularHolomorphicFoliation

end

end HolomorphicAnosov
