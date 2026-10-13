import HolomorphicAnosov.Topology.Homology.SingularChainCompactSupport
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# A finite relative triangle realization of a singular two-chain

Source: Hatcher, *Algebraic Topology*, pp.103–104, 108–109 and the proof of
Theorem 2A.1, p.167; Appendix pp.519–522. The coefficient signs are labels of
the chain, not reversals of face parameters. The quotient below identifies
only the paired, equally parametrized faces, even if other points have the
same image in the arbitrary target space.
-/

noncomputable section

namespace HolomorphicAnosov

open CategoryTheory _root_.Topology
open scoped Simplicial

universe u

namespace RelativeTriangleRealization

/-- The ordered topological simplex used by Mathlib's singular set; source:
Hatcher pp.103–104 and `TopCat.toSSetObjEquiv`. -/
abbrev Simplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

/-- The original order-preserving face of an ordered triangle; source:
Hatcher's alternating boundary formula, pp.108–109 and 167. -/
def face (j : Fin 3) : C(Simplex 1, Simplex 2) :=
  ⟨Convexity.StdSimplex.map j.succAbove,
    Convexity.StdSimplex.continuous_map ℝ j.succAbove⟩

/-- A continuous simplex as its basis element in the existing ordinary integral
singular chain module. Source: Hatcher pp.108–109 and Mathlib's actual summand
inclusion `SSet.ιChainComplex`; `ULift` changes the coefficient universe only. -/
def generator (X : TopCat.{u}) (n : ℕ) (σ : C(Simplex n, X)) :
    IntegralSingularChain X n :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)).symm σ)).hom (ULift.up (1 : ℤ))

/-- An occurrence is a triangle label and one of its three ordered faces.
Source: Hatcher p.167; repeated maps retain distinct occurrence labels. -/
abbrev Occurrence (m : ℕ) := Fin m × Fin 3

/-- The literal matching relation on triangle points: the same ordered
parameter on paired faces. Source: Hatcher p.167. A fixed distinguished
occurrence merely contributes reflexive relations. -/
def pointRelation {m : ℕ} (pair : Occurrence m → Occurrence m)
    (x y : Fin m × Simplex 2) : Prop :=
  ∃ o : Occurrence m, ∃ t : Simplex 1,
    x = (o.1, face o.2 t) ∧ y = ((pair o).1, face (pair o).2 t)

/-- The actual finite-triangle quotient with its native quotient topology.
Source: Hatcher pp.104, 108–109 and 167. The equivalence relation is generated
by the matching, so all and only its forced endpoint identifications occur. -/
abbrev Space {m : ℕ} (pair : Occurrence m → Occurrence m) :=
  Quotient (Relation.EqvGen.setoid (pointRelation pair))

/-- The original characteristic triangle, before proving the CW assertion.
Source: Hatcher p.167; continuity is native quotient-map continuity. -/
def triangle {m : ℕ} (pair : Occurrence m → Occurrence m) (i : Fin m) :
    C(Simplex 2, Space pair) :=
  ⟨fun t ↦ Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)) (i, t),
    (@continuous_quotient_mk' _ _ (Relation.EqvGen.setoid (pointRelation pair))).comp (continuous_const.prodMk continuous_id)⟩

/-- The characteristic edge belonging to an occurrence, with its unchanged
ordered parameter. Source: Hatcher p.167. -/
def edge {m : ℕ} (pair : Occurrence m → Occurrence m) (o : Occurrence m) :
    C(Simplex 1, Space pair) :=
  (triangle pair o.1).comp (face o.2)

/-- The finite classes of paired occurrences, with the distinguished occurrence
a singleton. Source: the matching in Hatcher p.167. -/
abbrev EdgeClass {m : ℕ} (pair : Occurrence m → Occurrence m) :=
  Quotient (Relation.EqvGen.setoid (fun o o' : Occurrence m ↦ o' = pair o))

/-- The class of an edge occurrence. Source: Hatcher p.167. -/
def edgeClass {m : ℕ} (pair : Occurrence m → Occurrence m) (o : Occurrence m) :
    EdgeClass pair := Quotient.mk (Relation.EqvGen.setoid (fun o o' : Occurrence m ↦ o' = pair o)) o

/-- The actual image of a labeled triangle vertex in the quotient.
Source: Hatcher pp.104 and 167. -/
def vertex {m : ℕ} (pair : Occurrence m → Occurrence m) (v : Fin m × Fin 3) :
    Space pair := triangle pair v.1 (Convexity.StdSimplex.single v.2)

/-- Vertex classes as actual quotient points, rather than classes of their
possibly coincident images in the target. Source: Hatcher pp.104 and 167. -/
abbrev VertexClass {m : ℕ} (pair : Occurrence m → Occurrence m) :=
  Set.range (vertex pair)

/-- Strictly positive barycentric coordinates describe the open simplex.
Source: Hatcher pp.103–104; this is the interior in the simplex's affine span. -/
def interior (n : ℕ) : Set (Simplex n) := {t | ∀ j, 0 < t.weights j}

/-- Exact CW compatibility of the original triangle quotient. Source:
Hatcher's disk attachments and subcomplexes, Appendix pp.519–522.

The two displayed disk homeomorphisms identify simplex interiors with the
native CW open balls. Equality on the whole closed simplex makes the given
triangle and edge maps genuine characteristic maps, not merely maps with the
same images. All cell index equivalences are onto, excluding extra cells.
The model `Fin n → ℝ` is exactly the normed model of native classical CW cells;
no Euclidean/max-norm equality is asserted. -/
def HasCWStructure {m : ℕ} (pair : Occurrence m → Occurrence m)
    (distinguished : Occurrence m) : Prop :=
  ∃ (_ : T2Space (Space pair)),
  ∃ cw : _root_.Topology.CWComplex (Set.univ : Set (Space pair)),
    letI := cw
    _root_.Topology.RelCWComplex.Finite (Set.univ : Set (Space pair)) ∧
    (∀ n : ℕ, 2 < n → IsEmpty (_root_.Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) n)) ∧
    ∃ disk1 : Simplex 1 ≃ₜ Metric.closedBall (0 : Fin 1 → ℝ) 1,
    ∃ disk2 : Simplex 2 ≃ₜ Metric.closedBall (0 : Fin 2 → ℝ) 1,
    (∀ t, (disk1 t).val ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ↔ t ∈ interior 1) ∧
    (∀ t, (disk2 t).val ∈ Metric.ball (0 : Fin 2 → ℝ) 1 ↔ t ∈ interior 2) ∧
    ∃ index2 : Fin m ≃ _root_.Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) 2,
    ∃ index1 : EdgeClass pair ≃ _root_.Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) 1,
    ∃ index0 : VertexClass pair ≃ _root_.Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) 0,
    (∀ i t, triangle pair i t = _root_.Topology.RelCWComplex.map 2 (index2 i) (disk2 t).val) ∧
    (∀ o t, edge pair o t = _root_.Topology.RelCWComplex.map 1 (index1 (edgeClass pair o)) (disk1 t).val) ∧
    (∀ v, _root_.Topology.RelCWComplex.openCell 0 (index0 v) = ({v.val} : Set (Space pair))) ∧
    ∃ B : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set (Space pair)),
      (B : Set (Space pair)) =
        (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set (Space pair)) 0 : Set (Space pair)) ∪
          Set.range (edge pair distinguished)

end RelativeTriangleRealization

end HolomorphicAnosov
