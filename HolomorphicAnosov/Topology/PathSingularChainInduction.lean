import HolomorphicAnosov.Topology.SingularChainInduction
import HolomorphicAnosov.Topology.PathSingularSimplexSurjective
import HolomorphicAnosov.Topology.PathSingularChain

noncomputable section
open CategoryTheory
universe u
namespace HolomorphicAnosov.Topology

/-- Every native singular one-chain can be handled by zero, addition and
integer multiples of path chains. Source: Hatcher, Algebraic Topology, pp.108
and 166–167. Native chain induction reduces to a simplex with lifted integer
coefficient; identify the simplex with a path and move its integer coefficient
through the linear summand map. -/
theorem pathSingularChain_induction {X : Type u} [TopologicalSpace X]
    (P : (integralSingularChains X).X 1 → Prop)
    (hz : P 0) (ha : ∀ a b, P a → P b → P (a + b))
    (hp : ∀ {x y : X} (α : Path x y) (z : ℤ), P (z • pathSingularChain α))
    (c : (integralSingularChains X).X 1) : P c := by
  apply singularChain_induction (TopCat.of X) 1 P hz ha
  intro σ a
  obtain ⟨x, y, α, rfl⟩ := pathSingularSimplex_surjective σ
  have hc : a = a.down • (1 : ULift.{u} ℤ) := by
    apply ULift.ext
    simp
  rw [hc, map_zsmul]
  exact hp α a.down
end HolomorphicAnosov.Topology
