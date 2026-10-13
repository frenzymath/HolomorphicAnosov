import HolomorphicAnosov.Topology.StdSimplexEdgePath
import HolomorphicAnosov.Topology.StdSimplexMappedTriangleHomotopic
import HolomorphicAnosov.Topology.PathSingularSimplex
import HolomorphicAnosov.Topology.SingularTriangleFacePathEval

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Convexity
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The based paths on the ordered faces of an actual singular triangle
satisfy the triangle composition homotopy. Source: Hatcher, Algebraic
Topology, Theorem 2A.1 proof p.167. The standard edges 01, 12 and 02 are
parametrized by the interval-simplex homeomorphism. Face equalities identify
their images with the given based paths, including their endpoints. Apply
the explicit convex-simplex path homotopy, then map and cast its endpoints.
The face ordering is delta-zero=12, delta-one=02, delta-two=01. -/
theorem singularTriangle_paths_homotopic {X : Type u} [TopologicalSpace X]
    {x : X} (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌)
    (α β γ : Path x x)
    (h0 : (TopCat.toSSet.obj (TopCat.of X)).δ 0 s = pathSingularSimplex β)
    (h1 : (TopCat.toSSet.obj (TopCat.of X)).δ 1 s = pathSingularSimplex γ)
    (h2 : (TopCat.toSSet.obj (TopCat.of X)).δ 2 s = pathSingularSimplex α) :
    (α.trans β).Homotopic γ := by
  let f := TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋2⦌) s
  let p := stdSimplexEdgePath (0 : Fin 3) 1
  let q := stdSimplexEdgePath (1 : Fin 3) 2
  let r := stdSimplexEdgePath (0 : Fin 3) 2
  have hp : ∀ t, f (p t) = α t := singularTriangle_face_path_eval s 2 α h2
  have hq : ∀ t, f (q t) = β t := singularTriangle_face_path_eval s 0 β h0
  have hr : ∀ t, f (r t) = γ t := singularTriangle_face_path_eval s 1 γ h1
  have ha : x = f (StdSimplex.single (0 : Fin 3)) := by simpa using (hp 0).symm
  have hb : x = f (StdSimplex.single (1 : Fin 3)) := by simpa using (hq 0).symm
  have hc : x = f (StdSimplex.single (2 : Fin 3)) := by simpa using (hq 1).symm
  have h := stdSimplex_mapped_triangle_homotopic p q r f x ha hb hc
  have hα : (p.map f.continuous).cast ha hb = α := by ext t; exact hp t
  have hβ : (q.map f.continuous).cast hb hc = β := by ext t; exact hq t
  have hγ : (r.map f.continuous).cast ha hc = γ := by ext t; exact hr t
  simpa only [hα, hβ, hγ] using h

end HolomorphicAnosov.Topology
