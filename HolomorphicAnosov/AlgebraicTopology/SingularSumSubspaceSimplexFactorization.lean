import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import Mathlib.Topology.ContinuousMap.Sigma
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- Every singular simplex in the union subspace factors through a subspace summand.
Source: Hatcher, *Algebraic Topology*, p.202; DAG
`topo.singular_sum_subspace_simplex_factorization_g13`.

Forget the subspace membership and factor the map from the connected standard
simplex through one ambient summand. The original membership proof shows that
the factor lands in its subspace. Subtype continuity and the singular-simplex
equivalence then give the asserted factorization. -/
theorem singular_sum_subspace_simplex_factorization {ι : Type u} (X : ι → TopCat.{u}) (A : ∀ j, Set (X j)) (n : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of {x : (Σ j, X j) // x.2 ∈ A x.1})).obj (op ⦋n⦌)) :
    ∃ (j : ι) (τ : (TopCat.toSSet.obj (TopCat.of (A j))).obj (op ⦋n⦌)),
      σ = (TopCat.toSSet.map (pairSubspaceMap (X := X j) (Y := TopCat.of (Σ k, X k)) (A := A j) (B := (fun x : (Σ j, X j) => x.2 ∈ A x.1))
        (TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => (X j : Type u)) j)) (fun _ hx => hx))).app (op ⦋n⦌) τ := by
  let e := TopCat.toSSetObjEquiv (TopCat.of {x : (Σ j, X j) // x.2 ∈ A x.1}) (op ⦋n⦌)
  let f := (subspaceInclusion (TopCat.of (Σ j, X j)) ((fun x : (Σ j, X j) => x.2 ∈ A x.1))).hom.comp (e σ)
  obtain ⟨j, g, hg⟩ := f.exists_lift_sigma
  have hA (t) : g t ∈ A j := by
    have hfg : (e σ t).val = ⟨j, g t⟩ := congrArg (fun k => k t) hg
    have ht := (e σ t).property
    change (e σ t).val.2 ∈ A (e σ t).val.1 at ht
    rw [hfg] at ht
    exact ht
  let gA : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A j) :=
    ⟨fun t => ⟨g t, hA t⟩, g.continuous.subtype_mk _⟩
  refine ⟨j, (TopCat.toSSetObjEquiv (TopCat.of (A j)) (op ⦋n⦌)).symm gA, ?_⟩
  apply e.injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact congrArg (fun k => k t) hg
end HolomorphicAnosov.SingularCochain
