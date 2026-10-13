import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Topology.ContinuousMap.Sigma

open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov

/-! A singular simplex in a topological disjoint union lies in one summand.
This is the degreewise generator decomposition used by the finite-sum
cohomology clause of the relative pair theorem (Hatcher, p. 202). -/

/-- The singular simplices of a disjoint union split by their unique summand.
Source: Hatcher, *Algebraic Topology*, p.202; DAG
`topo.singular_sum_simplex_bijection_g13`.

Identify singular simplices with continuous maps from the standard simplex.
Its connectedness gives a factorization through a summand; injectivity of
postcomposition with the summand inclusions makes that factorization unique.
Transporting through the continuous-map equivalences gives this bijection. -/
theorem singular_sum_simplex_bijective {ι : Type u} (X : ι → TopCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (fun s : Σ j, (TopCat.toSSet.obj (X j)).obj n =>
      (TopCat.toSSet.map
        (TopCat.ofHom ⟨(fun x : X s.1 => (⟨s.1, x⟩ : Σ j, X j)), by
          change Continuous (@Sigma.mk ι (fun k => (X k : Type u)) s.1)
          exact continuous_sigmaMk⟩)).app n s.2) := by
  let e := TopCat.toSSetObjEquiv (TopCat.of (Σ j, X j)) n
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ hab
    have hc := congrArg (TopCat.toSSetObjEquiv (TopCat.of (Σ j, X j)) n) hab
    have he : (⟨i, TopCat.toSSetObjEquiv (X i) n a⟩ :
        Σ k, C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), X k)) =
        ⟨j, TopCat.toSSetObjEquiv (X j) n b⟩ :=
      ContinuousMap.isEmbedding_sigmaMk_comp.injective hc
    have hij : i = j := congrArg Sigma.fst he
    subst j
    have hab' : a = b := (TopCat.toSSetObjEquiv (X i) n).injective
      (eq_of_heq (Sigma.mk.inj he).2)
    subst b
    rfl
  · intro σ
    obtain ⟨j, g, hg⟩ := (e σ).exists_lift_sigma
    refine ⟨⟨j, (TopCat.toSSetObjEquiv (X j) n).symm g⟩, ?_⟩
    apply e.injective
    rw [hg]
    rfl

end HolomorphicAnosov
