import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.Topology.Subpath

/-! Global stable holonomy consists of whole-leaf biholomorphisms extending local plaque-chain germs
and coherent under restrictions, concatenation, and reversal of intrinsic stable-leaf paths.
(Ghys, p.594 and Lemma 5.1, pp.597–598; Zhang, Prop. 2.9 and Lemma 2.10, p.10; Hirsch–Pugh–Shub,
§7, pp.115–116) -/

noncomputable section

namespace HolomorphicAnosov

open Filter Set _root_.Topology

universe u v

set_option autoImplicit false

variable {s t : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (Fin (s + t) → ℝ) M]
variable (F : TransverseContinuousFoliations.{u, v} s t M)
variable (C : IntrinsicComplexUnstableLeaves F)

/-- Biholomorphisms between entire unstable leaves with their intrinsic complex structures. (Ghys,
pp.594, 597–598) -/
abbrev IntrinsicLeafBiholomorph (x y : M) :=
  letI := C.charts (Quotient.mk F.unstablePartition x)
  letI := C.charts (Quotient.mk F.unstablePartition y)
  Biholomorph 1 1 (F.ULeaf x) (F.ULeaf y)

/-- The inverse of an intrinsic whole-leaf biholomorphism. (Ghys, pp.597–598; Zhang, p.10) -/
def inverseIntrinsicLeafBiholomorph {x y : M}
    (e : IntrinsicLeafBiholomorph F C x y) : IntrinsicLeafBiholomorph F C y x :=
  letI := C.charts (Quotient.mk F.unstablePartition x)
  letI := C.charts (Quotient.mk F.unstablePartition y)
  e.symm

/-- Transport of an intrinsic unstable-leaf point along equality of its basepoints. (Ghys, p.594) -/
def castIntrinsicULeaf {x y : M} (h : x = y) (z : F.ULeaf x) : F.ULeaf y :=
  h ▸ z

/-- Whole-leaf biholomorphic stable transports extending local plaque-chain germs and satisfying
restriction, concatenation, and reversal laws. (Ghys, p.594 and Lemma 5.1, pp.597–598; Zhang,
p.10) -/
structure GlobalSHolonomyData where
  localContinuation : ∀ {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y),
    LocalHolonomyContinuation F γ
  transport : ∀ {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q},
    Path x y → IntrinsicLeafBiholomorph F C x.val y.val
  extends_local : ∀ {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y),
    (Filter.Germ.ofFun (fun z : F.ULeaf x.val ↦ transport γ z) :
      Filter.Germ (𝓝 (F.uPoint x.val)) (F.ULeaf y.val)) =
      Filter.Germ.ofFun (fun z : F.ULeaf x.val ↦
        castIntrinsicULeaf F (congrArg Subtype.val γ.target)
          ((localContinuation γ).representative 0 1 (by simp) |>.map
            (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm z)))
  restriction : ∀ {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b c : unitInterval), a ≤ b → b ≤ c →
    ∀ z : F.ULeaf (γ a).val,
      transport (γ.subpath a c) z =
        transport (γ.subpath b c) (transport (γ.subpath a b) z)
  concatenation : ∀ {q : Quotient F.stablePartition}
    {x y z : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path y z) (w : F.ULeaf x.val),
    transport (γ.trans η) w = transport η (transport γ w)
  reversal : ∀ {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (z : F.ULeaf y.val), transport γ.symm z = inverseIntrinsicLeafBiholomorph F C (transport γ) z

/-- The existence of coherent whole-leaf biholomorphic extensions of local stable holonomy. (Ghys,
Lemma 5.1, pp.597–598; Zhang, Prop. 2.9 and Lemma 2.10, p.10) -/
def HasGlobalSHolonomy : Prop := Nonempty (GlobalSHolonomyData F C)

/-- The whole-leaf biholomorphism along an intrinsic stable path selected from global
stable-holonomy data. (Ghys, pp.597–598) -/
def globalSHolonomy (H : HasGlobalSHolonomy F C)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    IntrinsicLeafBiholomorph F C x.val y.val :=
  (Classical.choice H).transport γ

end HolomorphicAnosov
