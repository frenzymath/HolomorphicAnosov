import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import Mathlib.Topology.Subpath
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

/-! This file defines global unstable holonomy of an Anosov map on entire native stable leaves,
using the exchanged foliations of the inverse map. Its holonomy data include whole-leaf
biholomorphisms and their compatibility with local holonomy, concatenation, restriction, and
reversal. (Zhang, Prop. 2.9 and Lemma 2.10, p. 10; Ghys, p. 594 and Lemma 5.1, pp. 597–598; HPS,
pp. 114–116) -/

noncomputable section

namespace HolomorphicAnosov

open Filter Set _root_.Topology
open scoped ContDiff Manifold

universe u

section Native

variable {d s t : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
  (B : NativeTransverseAsymptoticIdentification.{u, u} f Ps Pu s t)

/-- A biholomorphism between entire native receiving leaves with their specified complex atlases.
(Zhang, p. 10) -/
abbrev NativeReceivingLeafBiholomorph (x y : M) :=
  letI := B.unstableTopology x
  letI := B.unstableCharts x
  letI := B.unstableTopology y
  letI := B.unstableCharts y
  letI := (B.complexU1 x).charts
  letI := (B.complexU1 y).charts
  Biholomorph 1 1 (UnstableAsymptoticLeaf f x) (UnstableAsymptoticLeaf f y)

/-- The marked ambient point viewed in its native receiving leaf. (HPS, p. 116) -/
def nativeReceivingPoint (x : M) : UnstableAsymptoticLeaf f x :=
  letI := B.realAmbientCharts
  B.unstableClassHomeomorph x (B.F.uPoint x)

/-- Transport of a native receiving-leaf point along an equality of basepoints. (Zhang, p. 10) -/
def castNativeReceivingLeaf {x y : M} (h : x = y)
    (z : UnstableAsymptoticLeaf f x) : UnstableAsymptoticLeaf f y := h ▸ z

/-- The inverse biholomorphism between the native receiving leaves. (Zhang, p. 10; Ghys, pp.
597–598) -/
def inverseNativeReceivingLeafBiholomorph {x y : M}
    (e : NativeReceivingLeafBiholomorph B x y) :
    NativeReceivingLeafBiholomorph B y x :=
  letI := B.unstableTopology x
  letI := B.unstableCharts x
  letI := B.unstableTopology y
  letI := B.unstableCharts y
  letI := (B.complexU1 x).charts
  letI := (B.complexU1 y).charts
  e.symm

/-- Global path holonomy by whole native receiving-leaf biholomorphisms agreeing locally with
product-box plaque transports and compatible with restriction, concatenation, and reversal.
(Zhang, Prop. 2.9 and Lemma 2.10, p. 10; Ghys, pp. 594, 597–598) -/
structure NativeGlobalSHolonomyData where
  localContinuation :
    letI := B.realAmbientCharts
    ∀ {q : Quotient B.F.stablePartition}
    {x y : IntrinsicFoliationLeaf B.F.stablePartition q} (γ : Path x y),
    LocalHolonomyContinuation B.F γ
  transport :
    letI := B.realAmbientCharts
    ∀ {q : Quotient B.F.stablePartition}
    {x y : IntrinsicFoliationLeaf B.F.stablePartition q},
    Path x y → NativeReceivingLeafBiholomorph B x.val y.val
  extends_local :
    letI := B.realAmbientCharts
    ∀ {q : Quotient B.F.stablePartition}
    {x y : IntrinsicFoliationLeaf B.F.stablePartition q} (γ : Path x y),
    letI := B.unstableTopology x.val
    letI := B.unstableTopology y.val
    (Filter.Germ.ofFun (fun z : UnstableAsymptoticLeaf f x.val ↦ transport γ z) :
      Filter.Germ (𝓝 (nativeReceivingPoint B x.val)) (UnstableAsymptoticLeaf f y.val)) =
      Filter.Germ.ofFun (fun z : UnstableAsymptoticLeaf f x.val ↦
        castNativeReceivingLeaf (congrArg Subtype.val γ.target)
          (B.transportUnstableLocalMap (γ 0).val (γ 1).val
            ((localContinuation γ).representative 0 1 (by simp)).map
            (castNativeReceivingLeaf (congrArg Subtype.val γ.source).symm z)))
  restriction :
    letI := B.realAmbientCharts
    ∀ {q : Quotient B.F.stablePartition}
    {x y : IntrinsicFoliationLeaf B.F.stablePartition q} (γ : Path x y)
    (a b c : unitInterval), a ≤ b → b ≤ c →
    ∀ z : UnstableAsymptoticLeaf f (γ a).val,
      transport (γ.subpath a c) z =
        transport (γ.subpath b c) (transport (γ.subpath a b) z)
  concatenation :
    letI := B.realAmbientCharts
    ∀ {q : Quotient B.F.stablePartition}
    {x y z : IntrinsicFoliationLeaf B.F.stablePartition q}
    (γ : Path x y) (η : Path y z) (w : UnstableAsymptoticLeaf f x.val),
    transport (γ.trans η) w = transport η (transport γ w)
  reversal :
    letI := B.realAmbientCharts
    ∀ {q : Quotient B.F.stablePartition}
    {x y : IntrinsicFoliationLeaf B.F.stablePartition q} (γ : Path x y)
    (z : UnstableAsymptoticLeaf f y.val),
    transport γ.symm z = inverseNativeReceivingLeafBiholomorph B (transport γ) z

end Native

attribute [local instance] complex_isManifold_real

/-- The property that the original Anosov map has global unstable holonomy on entire native stable
leaves, expressed using native identifications for the inverse map. (Zhang, Prop. 2.9 and Lemma
2.10, p. 10) -/
def HasOriginalAnosovGlobalUnstableHolonomy
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X] {f : Biholomorph d d X X} (a : AnosovDatum f) : Prop :=
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  ∃ B : NativeTransverseAsymptoticIdentification.{u, u} f.toHomeomorph.symm
      a.splitting.unstable.toDistribution a.splitting.stable.toDistribution (2 * (d - 1)) 2,
    Nonempty (NativeGlobalSHolonomyData B)

end HolomorphicAnosov
