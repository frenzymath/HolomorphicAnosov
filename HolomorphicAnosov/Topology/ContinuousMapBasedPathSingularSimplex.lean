import HolomorphicAnosov.Topology.BasedPathSingularSimplex
import HolomorphicAnosov.Topology.PathSingularSimplex
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

noncomputable section
open CategoryTheory Convexity
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- A continuous map on the ordered one-simplex whose endpoints are a common
point is represented by the corresponding based singular loop. Source:
Hatcher, Algebraic Topology, p.166 and Theorem 2A.1 p.167. Transport the map
through Mathlib's singular one-simplex equivalence, then apply the endpoint
criterion for `basedPathSingularSimplex_exists`; the resulting path preserves
the original simplex parametrization. -/
theorem continuousMap_basedPathSingularSimplex_exists {X : Type u}
    [TopologicalSpace X] (x : X)
    (e : C(Convexity.StdSimplex ℝ (Fin 2), X))
    (hzero : e (Convexity.StdSimplex.single 0) = x)
    (hone : e (Convexity.StdSimplex.single 1) = x) :
    ∃ α : Path x x,
      pathSingularSimplex α =
        (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋1⦌)).symm e := by
  let σ := (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋1⦌)).symm e
  have hσzero : TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) = x := by
    have hh := TopCat.toSSetObj₁Equiv_apply_zero σ
    have he : (TopCat.toSSetObj₁Equiv σ) 0 = e (Convexity.StdSimplex.single 0) := by
      simp only [TopCat.toSSetObj₁Equiv, Equiv.trans_apply, Equiv.apply_symm_apply, σ]
      change e (StdSimplex.homeomorphI.symm 0) = e (StdSimplex.single 0)
      rw [StdSimplex.homeomorphI_symm_zero]
    rw [he] at hh
    exact hh.symm.trans hzero
  have hσone : TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) = x := by
    have hh := TopCat.toSSetObj₁Equiv_apply_one σ
    have he : (TopCat.toSSetObj₁Equiv σ) 1 = e (Convexity.StdSimplex.single 1) := by
      simp only [TopCat.toSSetObj₁Equiv, Equiv.trans_apply, Equiv.apply_symm_apply, σ]
      change e (StdSimplex.homeomorphI.symm 1) = e (StdSimplex.single 1)
      rw [StdSimplex.homeomorphI_symm_one]
    rw [he] at hh
    exact hh.symm.trans hone
  obtain ⟨α, hα⟩ := basedPathSingularSimplex_exists x σ hσzero hσone
  exact ⟨α, hα⟩

end HolomorphicAnosov.Topology
