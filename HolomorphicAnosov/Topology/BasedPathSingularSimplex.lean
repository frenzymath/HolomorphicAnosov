import HolomorphicAnosov.Topology.PathSingularSimplex

noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- A singular edge whose two vertex faces are the same specified point is
the singular simplex of a based loop at that point. Source: Hatcher, Algebraic
Topology, Theorem 2A.1 proof p.167, after moving the triangle vertices to the
basepoint. Convert the simplex through Mathlib's interval equivalence; the
endpoint-face identities give the exact based endpoint conditions. This
preserves the original edge parametrization and uses no choice of homotopy. -/
theorem basedPathSingularSimplex_exists {X : Type u} [TopologicalSpace X]
    (x : X) (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌)
    (hzero : TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) = x)
    (hone : TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) = x) :
    ∃ α : Path x x, pathSingularSimplex α = σ := by
  let f := (TopCat.of X).toSSetObj₁Equiv σ
  let p : (TopCat.of X).Path x x := ⟨f,
    ((TopCat.of X).toSSetObj₁Equiv_apply_zero σ).trans hzero,
    ((TopCat.of X).toSSetObj₁Equiv_apply_one σ).trans hone⟩
  refine ⟨TopCat.pathEquiv p, ?_⟩
  simp [pathSingularSimplex, p, f]

end HolomorphicAnosov.Topology
