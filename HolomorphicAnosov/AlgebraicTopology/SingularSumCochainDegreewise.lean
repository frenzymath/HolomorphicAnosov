import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularSumSimplexBijection

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov
set_option backward.isDefEq.respectTransparency false

/-! Degreewise cochain splitting for a topological disjoint union. -/

/-- Restricting singular cochains to summands is a degreewise bijection.
Source: Hatcher, *Algebraic Topology*, p.202; DAG
`algebra.singular_sum_cochain_degreewise_g13`.

The simplex bijection identifies the generators of the union chain module with
the summand generators. Equality of cochains can therefore be tested after every
restriction. Conversely, assign each generator the value prescribed by its
unique summand and extend using the coproduct universal property `Sigma.desc`.
Its restriction recovers the prescribed family. This works for arbitrary index
families and commutative coefficient rings. -/
theorem singular_sum_cochain_restriction_bijective (R : Type u) [CommRing R]
    {ι : Type u} (X : ι → TopCat.{u}) (n : ℕ) :
    Function.Bijective (fun c : SingularCochain.cochains R (TopCat.of (Σ j, X j)) n =>
      fun j => ((SingularCochain.cochainFunctor R).map
        (op (TopCat.ofHom ⟨(fun x : X j => (⟨j, x⟩ : Σ k, X k)), by
          change Continuous (@Sigma.mk ι (fun k => (X k : Type u)) j)
          exact continuous_sigmaMk⟩))).f n c) := by
  let e := Equiv.ofBijective _ (singular_sum_simplex_bijective X (op ⦋n⦌))
  constructor
  · intro a b hab
    apply SSet.chainComplex_hom_ext
    intro σ
    obtain ⟨⟨j, τ⟩, hτ⟩ := (singular_sum_simplex_bijective X (op ⦋n⦌)).surjective σ
    subst σ
    have hj := congrFun hab j
    change ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨
      (fun x : X j => (⟨j, x⟩ : Σ k, X k)), by
        change Continuous (@Sigma.mk ι (fun k => (X k : Type u)) j)
        exact continuous_sigmaMk⟩)) (ModuleCat.of R R)).f n) ≫ a =
      ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨
        (fun x : X j => (⟨j, x⟩ : Σ k, X k)), by
          change Continuous (@Sigma.mk ι (fun k => (X k : Type u)) j)
          exact continuous_sigmaMk⟩)) (ModuleCat.of R R)).f n) ≫ b at hj
    have hh := congrArg (fun f =>
      (TopCat.toSSet.obj (X j)).ιChainComplex τ ≫ f) hj
    simp only [SSet.ι_chainComplexMap_f_assoc] at hh
    exact hh
  · intro cs
    let c : SingularCochain.cochains R (TopCat.of (Σ j, X j)) n := Sigma.desc (fun σ =>
      (TopCat.toSSet.obj (X (e.symm σ).1)).ιChainComplex (e.symm σ).2 ≫ cs (e.symm σ).1)
    refine ⟨c, ?_⟩
    funext j
    apply SSet.chainComplex_hom_ext
    intro τ
    change (TopCat.toSSet.obj (X j)).ιChainComplex τ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨
          (fun x : X j => (⟨j, x⟩ : Σ k, X k)), by
            change Continuous (@Sigma.mk ι (fun k => (X k : Type u)) j)
            exact continuous_sigmaMk⟩)) (ModuleCat.of R R)).f n ≫ c =
      (TopCat.toSSet.obj (X j)).ιChainComplex τ ≫ cs j
    rw [SSet.ι_chainComplexMap_f_assoc]
    change Sigma.ι _ (e ⟨j, τ⟩) ≫ c = _
    dsimp only [c]
    rw [Sigma.ι_comp_desc]
    exact congrArg (fun s : Σ j, (TopCat.toSSet.obj (X j)).obj (op ⦋n⦌) =>
      (TopCat.toSSet.obj (X s.1)).ιChainComplex s.2 ≫ cs s.1)
      (e.symm_apply_apply ⟨j, τ⟩)

end HolomorphicAnosov
