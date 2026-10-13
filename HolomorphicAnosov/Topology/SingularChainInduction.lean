import HolomorphicAnosov.Topology.SingularChainGeneratorIso
import HolomorphicAnosov.Topology.SingularChainGenerator

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
namespace HolomorphicAnosov

/-- Induction on a native integral singular chain by zero, addition, and
single-simplex summands with arbitrary integer coefficients.
Source: Hatcher, Algebraic Topology, p.108, finite formal sums of singular
simplices. Use the canonical finite-coefficient isomorphism, induct on its
finite support, and identify each single coordinate with its native generator. -/
theorem singularChain_induction (X : TopCat.{u}) (n : ℕ)
    (P : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n → Prop)
    (hz : P 0)
    (ha : ∀ a b, P a → P b → P (a + b))
    (hg : ∀ (σ : (TopCat.toSSet.obj X) _⦋n⦌) (a : ULift.{u} ℤ),
      P (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) a))
    (c : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).X n) : P c := by
  let e := singularChainGeneratorIso X n
  have h : ∀ f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) →₀ ULift.{u} ℤ,
      P (e.inv f) := by
    intro f
    induction f using Finsupp.induction with
    | zero => simpa using hz
    | @single_add σ a f hs hn ih =>
      rw [map_add]
      apply ha
      · have he := singularChainGeneratorIso_hom_generator X n
          ((X.toSSetObjEquiv _).symm σ) a
        rw [Equiv.apply_symm_apply] at he
        have hi := congrArg e.inv he
        change e.inv (e.hom _) = _ at hi
        simp only [Iso.hom_inv_id_apply] at hi
        rw [← hi]
        exact hg ((X.toSSetObjEquiv _).symm σ) a
      · exact ih
  simpa using h (e.hom c)
end HolomorphicAnosov
