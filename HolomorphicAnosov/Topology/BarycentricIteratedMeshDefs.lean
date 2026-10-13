import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Barycentric mesh definitions

The indexed prefix barycenters, iterated tuples, and transported affine convex hull used by
Hatcher's barycentric mesh contraction (Proposition 2.21, pp.119–121).
-/

noncomputable section

namespace HolomorphicAnosov.BarycentricMesh

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- The indexed prefix barycenters in Hatcher's coning subdivision, pp.119–120.
The finite set consists of indices, so repeated ambient vertices retain multiplicity.
Each prefix contains exactly `k.val + 1` indices and is nonempty. -/
def childVertices {n : ℕ} (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))) :
    Fin (n + 1) → E :=
  fun k ↦ (Finset.univ.filter (fun j ↦ j ≤ k)).centroid ℝ (v ∘ σ)

/-- Iterating Hatcher's prefix children, pp.120–121, in the order of the finite path.
The empty path is the original tuple. -/
def iteratedVertices {n : ℕ} (v : Fin (n + 1) → E) :
    List (Equiv.Perm (Fin (n + 1))) → (Fin (n + 1) → E)
  | [] => v
  | σ :: p => iteratedVertices (childVertices v σ) p

/-- The genuine real affine convex hull of a nonempty indexed vertex tuple.
Mathlib's `convexHull` is taken in vector coordinates based at `w 0`, then transported
back by the affine bijection `z ↦ z +ᵥ w 0`. Normalized affine combinations show that
this set is independent of the chosen origin. This is the hull used in Hatcher,
Proposition 2.21, pp.119–121; it is defined for arbitrary normed affine spaces. -/
def hull {n : ℕ} (w : Fin (n + 1) → E) : Set E :=
  (fun z : V ↦ z +ᵥ w 0) '' convexHull ℝ (Set.range (fun i ↦ w i -ᵥ w 0))

end HolomorphicAnosov.BarycentricMesh
