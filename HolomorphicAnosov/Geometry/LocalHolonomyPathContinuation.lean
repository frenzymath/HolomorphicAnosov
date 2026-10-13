import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Topology.Path

/-! Local plaque transports and their path-continuation germs. -/

namespace HolomorphicAnosov

open Filter Set Topology _root_.Topology

universe u v

set_option autoImplicit false

variable {s t : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (Fin (s + t) → ℝ) M]

namespace TransverseContinuousFoliations

/-- The actual unstable partition class through a point, with its intrinsic topology (HPS §7, pp.115–116, as used for the transversals in Ghys p.594).-/
abbrev ULeaf (F : TransverseContinuousFoliations.{u, v} s t M) (x : M) :=
  IntrinsicFoliationLeaf F.unstablePartition (Quotient.mk F.unstablePartition x)

/-- The supplied unstable topology, not the ambient subtype topology (HPS p.116; the transverse-foliation datum).-/
instance uLeafTopology (F : TransverseContinuousFoliations.{u, v} s t M) (x : M) :
    TopologicalSpace (F.ULeaf x) :=
  F.unstableTopology (Quotient.mk F.unstablePartition x)

/-- The original point in its own unstable partition class (Ghys p.594).-/
def uPoint (F : TransverseContinuousFoliations.{u, v} s t M) (x : M) : F.ULeaf x :=
  ⟨x, rfl⟩

/-- The supplied stable topology for an intrinsic path (HPS p.116).-/
instance sLeafTopology (F : TransverseContinuousFoliations.{u, v} s t M)
    (q : Quotient F.stablePartition) :
    TopologicalSpace (IntrinsicFoliationLeaf F.stablePartition q) :=
  F.stableTopology q

end TransverseContinuousFoliations

variable (F : TransverseContinuousFoliations.{u, v} s t M)

/-- A local homeomorphism between specified U leaves, taking the displayed point to the other displayed point (the neighborhood representatives in Ghys p.594).-/
structure PointedLeafHomeomorph (x y : M) where
  map : OpenPartialHomeomorph (F.ULeaf x) (F.ULeaf y)
  source_point : F.uPoint x ∈ map.source
  map_point : map (F.uPoint x) = F.uPoint y

/-- S-plaque transport in one original common product box, restricted to open neighborhoods (Ghys p.594 and the continuous transverse-foliation datum).-/
structure LocalPlaqueTransport (x y : M) extends PointedLeafHomeomorph F x y where
  box : F.boxIndex
  first : FoliationCoordinateDisk s
  second : FoliationCoordinateDisk s
  transverse : FoliationCoordinateDisk t
  first_point : ((F.box box).chart (first, transverse)).val = x
  second_point : ((F.box box).chart (second, transverse)).val = y
  source_in_plaque : ∀ z ∈ map.source,
    ∃ w : FoliationCoordinateDisk t, ((F.box box).chart (first, w)).val = z.val
  coordinate_map : ∀ (z : F.ULeaf x) (w : FoliationCoordinateDisk t),
    z ∈ map.source → ((F.box box).chart (first, w)).val = z.val →
      (map z).val = ((F.box box).chart (second, w)).val

/-- Germs of pointed local homeomorphisms between the same source and target leaves (Ghys p.594).-/
def LocalLeafHomeomorphGerm (x y : M) :=
  {g : Filter.Germ (𝓝 (F.uPoint x)) (F.ULeaf y) //
    ∃ e : PointedLeafHomeomorph F x y, Filter.Germ.ofFun e.map = g}

/-- Germs of the stated one-box plaque transports, not arbitrary local homeomorphisms (Ghys p.594).-/
def LocalPlaqueTransportGerm (x y : M) :=
  {g : Filter.Germ (𝓝 (F.uPoint x)) (F.ULeaf y) //
    ∃ e : LocalPlaqueTransport F x y, Filter.Germ.ofFun e.map = g}

/-- Finite plaque chains along a parameter subinterval of one intrinsic S path (Ghys Lemma 5.1, pp.597–598, and Zhang Proposition 2.9/Lemma 2.10, p.10).-/
inductive PlaqueChainAlong {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    (a b : unitInterval) →
      OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val) → Prop where
  | single (a b : unitInterval) (hab : a ≤ b)
      (e : LocalPlaqueTransport F (γ a).val (γ b).val)
      (segment : ∀ r : unitInterval, a ≤ r → r ≤ b →
        ∃ z : FoliationCoordinateDisk s,
          ((F.box e.box).chart (z, e.transverse)).val = (γ r).val) :
      PlaqueChainAlong γ a b e.map
  | compose {a b c : unitInterval}
      {e : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
      {e' : OpenPartialHomeomorph (F.ULeaf (γ b).val) (F.ULeaf (γ c).val)}
      (hab : a ≤ b) (hbc : b ≤ c)
      (left : PlaqueChainAlong γ a b e) (right : PlaqueChainAlong γ b c e') :
      PlaqueChainAlong γ a c (e.trans e')

/-- A finite local representative for a subpath, with its actual endpoint neighborhoods (Ghys pp.594,597–598 and Zhang p.10).-/
structure PathHolonomyRepresentative {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) extends PointedLeafHomeomorph F (γ a).val (γ b).val where
  chain : PlaqueChainAlong F γ a b map

/-- Germs with an actual finite plaque-chain representative along the displayed subpath (Ghys pp.594,597–598 and Zhang p.10).-/
def PathHolonomyGerm {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) :=
  {g : Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ b).val) //
    ∃ e : PathHolonomyRepresentative F γ a b, Filter.Germ.ofFun e.map = g}

/-- Compatible local continuation along one intrinsic S path (Ghys Lemma 5.1, pp.597–598, and Zhang Lemma 2.10, p.10).-/
structure LocalHolonomyContinuation {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) where
  representative : ∀ a b : unitInterval, a ≤ b → PathHolonomyRepresentative F γ a b
  refinement : ∀ (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c),
    Filter.Germ.ofFun ((representative b c hbc).map ∘ (representative a b hab).map) =
      (Filter.Germ.ofFun (representative a c (hab.trans hbc)).map :
        Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ c).val))

/-- Chronological local-map composition, with its actual open switch domain (Zhang Proposition 2.9 and Lemma 2.10, p.10).-/
def composeLocalHolonomy {x y z : M}
    (e : OpenPartialHomeomorph (F.ULeaf x) (F.ULeaf y))
    (e' : OpenPartialHomeomorph (F.ULeaf y) (F.ULeaf z)) :=
  e.trans e'

/-- Reversal of a local map uses its actual inverse on the open target neighborhood (the reversed plaque-chain convention in Zhang p.10).-/
def reverseLocalHolonomy {x y : M}
    (e : OpenPartialHomeomorph (F.ULeaf x) (F.ULeaf y)) :=
  e.symm

end HolomorphicAnosov
