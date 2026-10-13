import HolomorphicAnosov.Geometry.IdealDiskTriangle
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Chain
import Mathlib.Logic.Relation
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.Basic

/-! This file defines the disk, ideal triangles, side reflections, and their geometric reflection orbit. (Epstein–Petronio, Def. 2.1) -/

noncomputable section

open scoped ComplexConjugate

namespace HolomorphicAnosov.IdealDiskTriangle

/-- The literal open unit disk, with the ambient complex topology. (Epstein–Petronio, Def. 2.1) -/
def disk : Set ℂ := {z | ‖z‖ < 1}

/-- An unordered triple of distinct ideal vertices on the unit circle. (Epstein–Petronio, Def. 2.1) -/
def VertexTriple := {V : Finset ℂ // V.card = 3 ∧ ∀ p ∈ V, ‖p‖ = 1}

/-- The center of the circle orthogonal to the unit circle through `p,q`, when `p+q≠0`. (Epstein–Petronio, Def. 2.1) -/
def orthogonalCenter (p q : ℂ) : ℂ := 2 * p * q / (p + q)

/-- A signed side equation. (Epstein–Petronio, Def. 2.1) -/
def sideEquation (p q z : ℂ) : ℝ :=
  if p + q = 0 then (z / p).im
  else ‖z - orthogonalCenter p q‖ ^ 2 - (‖orthogonalCenter p q‖ ^ 2 - 1)

/-- The complete geodesic between two distinct unit-circle endpoints, excluding both ideal endpoints because the carrier lies in the open disk. (Epstein–Petronio, Def. 2.1) -/
def openSide (p q : ℂ) : Set ℂ := {z | z ∈ disk ∧ sideEquation p q z = 0}

/-- The closed half-disk bounded by the side through `p,q` and containing `r`. (Epstein–Petronio, Def. 2.1) -/
def sideHalfDisk (p q r : ℂ) : Set ℂ :=
  {z | z ∈ disk ∧ 0 ≤ sideEquation p q z * sideEquation p q r}

/-- The ideal triangle includes all three open sides, but excludes its ideal vertices. (Epstein–Petronio, Def. 2.1) -/
def triangle (V : Finset ℂ) : Set ℂ :=
  {z | z ∈ disk ∧ ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V,
    p ≠ q → q ≠ r → r ≠ p → 0 ≤ sideEquation p q z * sideEquation p q r}

/-- The literal topological interior of the explicitly defined ideal triangle. (Epstein–Petronio, Def. 2.1) -/
def openTriangle (V : Finset ℂ) : Set ℂ := interior (triangle V)

/-- Reflect the actual ideal vertex set in its side through `p,q`. (Epstein–Petronio, Def. 4.2) -/
def reflectedVertices (V : Finset ℂ) (p q : ℂ) : Finset ℂ :=
  V.image (idealDiskSideReflection p q)

/-- One reflection of an actual ideal triangle across one of its sides. (Epstein–Petronio, Def. 4.2) -/
def reflectionStep (V W : Finset ℂ) : Prop :=
  ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ W = reflectedVertices V p q

/-- The finite reflection orbit of an initial actual triple, as finite reflexive transitive reachability. (Epstein–Petronio, Def. 4.2) -/
def reachable (V W : Finset ℂ) : Prop := Relation.ReflTransGen reflectionStep V W

/-- Distinct physical triangles reached from the given triangle, indexed by their unordered ideal vertex triples rather than by words that may repeat a triangle. (Epstein–Petronio, Def. 4.5) -/
def ReachedTriangle (V : VertexTriple) := {W : VertexTriple // reachable V.val W.val}

/-- The initial physical triangle is reached by the empty reflection word. (Epstein–Petronio, Def. 4.5) -/
def initialTriangle (V : VertexTriple) : ReachedTriangle V :=
  ⟨V, Relation.ReflTransGen.refl⟩

/-- The actual open sides of a triangle, indexed by endpoint pairs. (Epstein–Petronio, Def. 4.5) -/
def hasSide (V : Finset ℂ) (S : Set ℂ) : Prop :=
  ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ S = openSide p q

/-- Geometric dual adjacency means that distinct physical triangles share a whole open geodesic side. (Epstein–Petronio, Def. 4.5) -/
def adjacent (V W : Finset ℂ) : Prop :=
  V ≠ W ∧ ∃ S : Set ℂ, hasSide V S ∧ hasSide W S

/-- The geometric dual graph of the reflection orbit. (Epstein–Petronio, Def. 4.5) -/
def dualGraph (V : VertexTriple) : SimpleGraph (ReachedTriangle V) where
  Adj A B := adjacent A.val.val B.val.val
  symm := ⟨by
    rintro A B ⟨h, S, hA, hB⟩
    exact ⟨h.symm, S, hB, hA⟩⟩
  loopless := ⟨by
    intro A h
    exact h.1 rfl⟩

/-- The distinct physical open sides appearing in the actual reflection orbit. (Epstein–Petronio, Def. 4.5) -/
def ReachedSide (V : VertexTriple) :=
  {S : Set ℂ // ∃ W : ReachedTriangle V, hasSide W.val.val S}

/-- The triangle family in the disk subtype. (Epstein–Petronio, Def. 4.5) -/
def reachedTriangleFamily (V : VertexTriple) (W : ReachedTriangle V) : Set disk :=
  {z | z.val ∈ triangle W.val.val}

/-- The side family in the disk subtype, excluding its ideal endpoints. (Epstein–Petronio, Def. 4.5) -/
def reachedSideFamily (V : VertexTriple) (S : ReachedSide V) : Set disk :=
  {z | z.val ∈ S.val}

/-- A finite itinerary is an actual list of consecutive geometric side reflections. (Epstein–Petronio, Def. 4.5) -/
def isItinerary (V W : Finset ℂ) (L : List (Finset ℂ)) : Prop :=
  L ≠ [] ∧ L.head? = some V ∧ L.getLast? = some W ∧ L.IsChain reflectionStep

/-- A simple physical itinerary does not repeat its triangle vertex set. (Epstein–Petronio, Def. 4.5) -/
def isSimpleItinerary (V W : Finset ℂ) (L : List (Finset ℂ)) : Prop :=
  isItinerary V W L ∧ L.Nodup

/-- A single deletion of an immediate physical backtrack `A,B,A`. (Epstein–Petronio, Def. 4.5) -/
def deletesBacktrack (L K : List (Finset ℂ)) : Prop :=
  ∃ P Q : List (Finset ℂ), ∃ A B : Finset ℂ,
    L = P ++ [A, B, A] ++ Q ∧ K = P ++ [A] ++ Q

/-- A finite deletion-only reduction of an itinerary. (Epstein–Petronio, Def. 4.5) -/
def reducesItinerary (L K : List (Finset ℂ)) : Prop :=
  Relation.ReflTransGen deletesBacktrack L K

end HolomorphicAnosov.IdealDiskTriangle
