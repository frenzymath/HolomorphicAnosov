import HolomorphicAnosov.Topology.Homology.SingularChainCoefficientsGenerator
import HolomorphicAnosov.Algebra.IntegerFinsuppSignedExpansion

/-!
# Signed unit expansions of native integral singular chains

Source: Hatcher, *Algebraic Topology*, pp.108–109 and the proof of
Theorem 2A.1, p.167. Transport the finite signed-copy coefficient expansion
through the canonical coproduct coefficient equivalence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial BigOperators

namespace HolomorphicAnosov

universe u

/-- Every native integral singular chain is a finite sum of signed unit simplices.
Source: Hatcher, Algebraic Topology, pp.108–109 and proof of Theorem 2A.1, p.167.

Proof: Take the canonical finitely supported coefficients and lower their integer
universe lifts. Expand this integer function into signed copies of its generators.
The canonical coproduct isomorphism sends each native simplex summand to the
corresponding single function. Its injectivity therefore transports the finite
signed sum back to the original chain. Repeated simplices retain their labels;
the zero chain may use the empty sum. No assumption on the space or degree is needed. -/
theorem integralSingularChainSignedExpansion (X : TopCat.{u}) (n : ℕ)
    (c : IntegralSingularChain X n) :
    ∃ (m : ℕ) (σ : Fin m → (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))
      (ε : Fin m → ℤ), (∀ i, ε i = -1 ∨ ε i = 1) ∧
      c = ∑ i, ε i •
        ((TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ (ULift.{u} ℤ)) (σ i)).hom (ULift.up (1 : ℤ)) := by
  let e := (integralSingularChainCoefficients X n).trans
    (Finsupp.lcongr (Equiv.refl _) (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ))
  obtain ⟨m, σ, ε, hε, hc⟩ := integerFinsuppSignedExpansion (e c)
  refine ⟨m, σ, ε, hε, e.injective ?_⟩
  rw [hc, map_sum]
  congr 1
  funext i
  rw [map_zsmul]
  congr 1
  dsimp only [e, LinearEquiv.trans_apply]
  rw [integralSingularChainCoefficients_ι, Finsupp.lcongr_single]
  rfl


end HolomorphicAnosov
