import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Topology.ContinuousMap.Basic

/-!
# The ordered positive Euclidean simplex

Source: Hatcher, *Algebraic Topology*, p. 269, identifies the orientation of an affine
simplex with its ordered edge basis, and bases differing by a positive determinant.
The vertices used here are an explicit coordinate choice for that convention, rather
than a claim that Hatcher prints this particular formula. The definition constructs the
continuous simplex itself; it assumes no homological generator or orientation theorem.
DAG node: `topo.euclidean_positive_local_simplex_g10`.
-/

noncomputable section

namespace HolomorphicAnosov

/-- The ordered affine simplex with vertices `(-1,…,-1), e₁,…,eₙ`, given in barycentric
coordinates by `σ(t)ⱼ = tⱼ₊₁ − t₀`. Source: Hatcher, p. 269, the ordered edge-basis
orientation convention. Its edge matrix is `I + 11ᵀ`, of determinant `n+1 > 0`, and
uniform barycentric weights map to zero. These observations explain the coordinate
choice; no homology-class certificate is part of the definition. In dimension zero,
this is the unique point map from the zero-simplex to zero-dimensional Euclidean space.
The source and target carry the actual Mathlib simplex and Euclidean topologies. -/
def euclideanPositiveSimplex (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), EuclideanSpace ℝ (Fin n)) :=
  ⟨fun t ↦ WithLp.toLp 2 (fun j ↦ t.weights j.succ - t.weights 0), by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi (fun j ↦
      (Convexity.StdSimplex.continuous_weights_apply ℝ j.succ).sub
        (Convexity.StdSimplex.continuous_weights_apply ℝ 0))⟩

end HolomorphicAnosov
