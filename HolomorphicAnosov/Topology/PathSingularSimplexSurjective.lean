import HolomorphicAnosov.Topology.PathSingularSimplex

noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- Every singular one-simplex is the original singular simplex of a path
between its endpoint values. Source: Hatcher, Algebraic Topology, p.166,
identification of singular one-simplices with paths. Use the interval-simplex
homeomorphism and equip the resulting interval map with its actual endpoints. -/
theorem pathSingularSimplex_surjective {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋1⦌) :
    ∃ (x y : X) (α : Path x y), pathSingularSimplex α = σ := by
  let f := (TopCat.of X).toSSetObj₁Equiv σ
  let p : (TopCat.of X).Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  refine ⟨f 0, f 1, TopCat.pathEquiv p, ?_⟩
  simp [pathSingularSimplex, p, f]
end HolomorphicAnosov.Topology
