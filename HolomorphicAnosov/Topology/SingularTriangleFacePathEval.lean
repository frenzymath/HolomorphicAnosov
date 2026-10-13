import HolomorphicAnosov.Topology.StdSimplexEdgePath
import HolomorphicAnosov.Topology.PathSingularSimplex
import Mathlib.Tactic.FinCases

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Convexity
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- An ordered face equality identifies the actual mapped affine edge path
pointwise, with its original interval parametrization. Source: Hatcher,
Algebraic Topology, ordered faces pp.103–104 and Theorem 2A.1 proof p.167.
Evaluate the continuous-map image of the face equality at the inverse
interval-simplex coordinate. The ordered face map sends the two vertices to
`j.succAbove 0` and `j.succAbove 1`, giving exactly the displayed edge path. -/
theorem singularTriangle_face_path_eval {X : Type u} [TopologicalSpace X]
    {x y : X} (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌)
    (j : Fin 3) (α : Path x y)
    (hj : (TopCat.toSSet.obj (TopCat.of X)).δ j s = pathSingularSimplex α)
    (t : unitInterval) :
    TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋2⦌) s
      (stdSimplexEdgePath (j.succAbove 0) (j.succAbove 1) t) = α t := by
  have h := congrArg (fun σ ↦
    TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋1⦌) σ
      (StdSimplex.homeomorphI.symm t)) hj
  change TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋2⦌) s
      ((StdSimplex.homeomorphI.symm t).map j.succAbove) =
    α (StdSimplex.homeomorphI (StdSimplex.homeomorphI.symm t)) at h
  rw [show j.succAbove = ![j.succAbove 0, j.succAbove 1] by
    ext i; fin_cases i <;> rfl] at h
  simpa [stdSimplexEdgePath] using h

end HolomorphicAnosov.Topology
