import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.UnitInterval

/-!
# Attached-cell and finite-polyhedral deformation data

Source: Hatcher, Algebraic Topology, Lemma 4.10 and its application in
Theorem 4.8, printed pp.350–351. DAG node:
`topo.def_attached_cell_polyhedral_deformation_data_g4`.

The attachment data below retains the original characteristic disk and quotient
presentation. Polyhedra are finite unions of compact intersections of finitely
many affine halfspaces, as in Hatcher's definition on p.350. No deformation, existence assertion or postponed proof is included in these
definitions. The relative deformation theorem imports this data separately.
-/

namespace HolomorphicAnosov.HatcherAttachedCell

noncomputable section

open scoped BigOperators
open Set

universe u

/-- The original source cube I^n, including the singleton cube at n=0.
Source: Hatcher Lemma4.10, p.350. -/
abbrev Cube (n : ℕ) := Fin n → unitInterval

/-- The ambient real coordinates of the original source cube.
Source: Hatcher's finite cubical subdivision, pp.350–351. -/
def cubeCoordinates {n : ℕ} (x : Cube n) : Fin n → ℝ := fun i ↦ (x i : ℝ)

/-- The original Euclidean closed characteristic disk of a k-cell.
Source: Hatcher's cell attachment convention, §0 and Lemma4.10, p.350. -/
abbrev CellDisk (k : ℕ) := ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)

/-- The characteristic boundary; it is empty in dimension zero.
Source: Hatcher's cell attachment convention. -/
abbrev CellSphere (k : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)

/-- The canonical inclusion of the sphere into the closed disk. -/
def boundaryInclusion {k : ℕ} (x : CellSphere k) : CellDisk k :=
  ⟨x.val, Metric.mem_closedBall.mpr (Metric.mem_sphere.mp x.property).le⟩

/-- The canonical inclusion of the open characteristic disk into the closed disk. -/
def interiorInclusion {k : ℕ}
    (x : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1)) : CellDisk k :=
  ⟨x.val, Metric.mem_closedBall.mpr (Metric.mem_ball.mp x.property).le⟩

/-- A single cell attached to an original subspace, with its characteristic quotient
and the chosen identification of its open cell with R^k.

Source: Hatcher, §0 cell attachments and Lemma4.10, pp.350–351.
`quotient` gives exactly the original quotient topology, using the original
subspace topology on `oldSpace`. `boundary_eq` records the attaching identifications;
`characteristic_interior` identifies the open disk bijectively with the complement.
The complement is open. `coordinates` is the chosen real-coordinate homeomorphism
of this same cell, not an assumed deformation or a new topology. No regular-cell
or injective-boundary assumption is imposed.
-/
structure Attachment (Z : Type u) [TopologicalSpace Z] (k : ℕ) where
  oldSpace : Set Z
  characteristic : C(CellDisk k, Z)
  attaching : C(CellSphere k, oldSpace)
  boundary_eq : ∀ x : CellSphere k,
    characteristic (boundaryInclusion x) = (attaching x : Z)
  quotient : Topology.IsQuotientMap
    (Sum.elim (fun x : oldSpace ↦ (x : Z)) characteristic : oldSpace ⊕ CellDisk k → Z)
  cell_open : IsOpen (oldSpaceᶜ)
  interior : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≃ₜ ↥(oldSpaceᶜ)
  characteristic_interior : ∀ x : ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1),
    characteristic (interiorInclusion x) = (interior x : Z)
  coordinates : EuclideanSpace ℝ (Fin k) ≃ₜ ↥(oldSpaceᶜ)

/-- An intersection of finitely many affine halfspaces in the original real coordinates.
Source: Hatcher's definition of convex polyhedron, p.350. -/
def halfspaceIntersection {n m : ℕ}
    (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, ∑ j, a i j * x j ≤ b i}

/-- A compact convex polyhedron given by its actual finite affine inequalities.
The compactness field is a proof about this literal set, not unspecified data.
Source: Hatcher p.350. -/
structure CompactPolyhedron (n : ℕ) where
  constraintCount : ℕ
  coefficients : Fin constraintCount → Fin n → ℝ
  bounds : Fin constraintCount → ℝ
  compact : IsCompact (halfspaceIntersection coefficients bounds)

/-- The literal halfspace carrier of the supplied polyhedron.
Source: Hatcher p.350. -/
def CompactPolyhedron.carrier {n : ℕ} (P : CompactPolyhedron n) : Set (Fin n → ℝ) :=
  halfspaceIntersection P.coefficients P.bounds

/-- A finite polyhedron in the original cube: a finite union of compact convex
polyhedra, all lying inside that cube in its original coordinates.
Empty unions are allowed. Source: Hatcher p.350. -/
def IsFinitePolyhedron {n : ℕ} (K : Set (Cube n)) : Prop :=
  ∃ (m : ℕ) (P : Fin m → CompactPolyhedron n),
    (∀ i, (P i).carrier ⊆ range (cubeCoordinates : Cube n → Fin n → ℝ)) ∧
    (∀ x : Cube n, x ∈ K ↔ ∃ i, cubeCoordinates x ∈ (P i).carrier)

/-- Piecewise affine on a finite polyhedron means agreement with actual affine maps
on every member of a finite convex-polyhedral decomposition. Here 'linear' is the
source's PL convention, which allows affine simplex interpolation. No smoothness
of the original map is part of this predicate. Source: Hatcher p.350.
-/
def PiecewiseAffineOn {n k : ℕ} (g : Cube n → EuclideanSpace ℝ (Fin k))
    (K : Set (Cube n)) : Prop :=
  ∃ (m : ℕ) (P : Fin m → CompactPolyhedron n)
    (A : Fin m → ((Fin n → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin k))),
    (∀ i, (P i).carrier ⊆ range (cubeCoordinates : Cube n → Fin n → ℝ)) ∧
    (∀ x : Cube n, x ∈ K ↔ ∃ i, cubeCoordinates x ∈ (P i).carrier) ∧
    (∀ i (x : Cube n), cubeCoordinates x ∈ (P i).carrier →
      g x = A i (cubeCoordinates x))

/-- The explicit affine collar mixture used in the source homotopy on K2.
Source: Hatcher p.351, formula (1−tφ)f+(tφ)g. Its continuity and pasting are
conclusions established in the theorem, not assumed in the data definitions. -/
def collarMixture {k : ℕ} (t φ : ℝ) (u v : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  (1 - t * φ) • u + (t * φ) • v

end

end HolomorphicAnosov.HatcherAttachedCell
