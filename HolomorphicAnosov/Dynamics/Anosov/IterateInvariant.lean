import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution

/-!
# Iterated invariance of a real tangent distribution

Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*, p.1, supplies the
one-step derivative invariance used here. The induction below is the agent-written
construction documented in DAG node `dynamics.real_distribution_iterate_invariant`.
-/

namespace HolomorphicAnosov

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- One-step derivative invariance of a real tangent distribution implies invariance
under every natural iterate.

Source: Zhang, supplied PDF p.1, invariant Anosov splitting. The following is the
agent-written expansion in DAG node `dynamics.real_distribution_iterate_invariant`;
it is not presented as a separately printed result of Zhang. The function iterate
in the conclusion is definitionally the forward map of `realIterate I g n`.

Proof:
1. Every iterate of `g` is smooth by `ContMDiff.iterate` applied to
   `g.contMDiff_toFun`. Since the smoothness order is infinity and hence nonzero,
   `g` and every iterate are manifold differentiable at every point. Thus every
   application of the chain rule below meets its differentiability hypotheses.
2. Induct on `n`, proving the assertion simultaneously at every base point `x`.
   When `n = 0`, `Function.iterate_zero` identifies the iterate with the identity.
   Its derivative is the identity continuous linear map by `mfderiv_id`.
   `Submodule.map_id` makes its image of `P x` equal to `P x`, as required.
3. Suppose the assertion holds for `n` at every point. By `Function.iterate_succ`,
   the next iterate is `g^[n]` composed with `g`. The chain rule `mfderiv_comp`
   identifies its derivative at `x` with the derivative of `g^[n]` at `g x`
   composed with the derivative of `g` at `x`. After forgetting continuity,
   `Submodule.map_comp` expresses the image of `P x` as its image first under
   the derivative of `g` and then under the derivative of `g^[n]` at `g x`.
4. The hypothesis `hP x` identifies the inner image with `P (g x)`. Apply the
   induction hypothesis at `g x` to identify the outer image with
   `P ((g^[n]) (g x))`. The same successor identity identifies this fibre with
   `P ((g^[n + 1]) x)`. Induction proves the assertion for every `n` and `x`.

No local triviality, rank, metric, contraction, compactness, or complex structure
is used. The zero distribution and the zeroth iterate are included. -/
theorem real_distribution_iterate_invariant
    (g : Diffeomorph I I X X ∞) (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I g x).toLinearMap = P (g x))
    (n : ℕ) (x : X) :
    (P x).map (mfderiv I I ((g : X → X)^[n]) x).toLinearMap =
      P (((g : X → X)^[n]) x) := by
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, mfderiv_id, ContinuousLinearMap.coe_id]
    exact Submodule.map_id (P x)
  | succ n ih =>
    rw [Function.iterate_succ, mfderiv_comp x
      ((g.contMDiff.iterate n).mdifferentiableAt (by simp))
      (g.contMDiff.mdifferentiableAt (by simp)),
      ContinuousLinearMap.toLinearMap_comp, Submodule.map_comp, hP x]
    exact ih (g x)

end HolomorphicAnosov
