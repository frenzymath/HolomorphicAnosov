import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Algebra.Homology.HomologySequence
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
/-- The connecting map of a short exact cochain sequence, on the literal
cocycle/coboundary quotients. Source: Hatcher, *Algebraic Topology*, pp.199–200;
Mathlib's `ShortComplex.ShortExact.δ` supplies the snake-lemma connecting map.
The canonical module homology isomorphisms only change its presentation. -/
def quotientConnecting (R : Type u) [CommRing R]
    {S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (hS : S.ShortExact) (n : ℕ) : quotient R S.X₃ n ⟶ quotient R S.X₁ (n + 1) :=
  (S.X₃.sc n).moduleCatHomologyIso.inv ≫ hS.δ n (n + 1) rfl ≫
    (S.X₁.sc (n + 1)).moduleCatHomologyIso.hom
end HolomorphicAnosov.SingularCochain
