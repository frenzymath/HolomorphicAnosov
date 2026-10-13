import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Relative homology comparison from absolute homology comparisons

Source: Hatcher, Algebraic Topology, the long exact sequence of a pair and
the five-lemma comparison used in Lemma 3.27, step (3), p.237.
-/

open CategoryTheory

namespace HolomorphicAnosov

universe u

/-- A map of singular simplicial pairs that is an isomorphism on absolute
homology of both spaces induces an isomorphism on relative homology in every
degree, including degree zero. Source: Hatcher, Lemma 3.27, step (3), p.237,
and the long exact sequence of a pair.

Proof: the pair map gives a morphism between the canonical short exact
sequences of subspace, ambient, and relative singular chain complexes. The
first square commutes by functoriality and the second by naturality of the
relative quotient projection. The first two chain maps are quasi-isomorphisms
by the supplied degreewise hypotheses. The homology-sequence five lemma gives
a quasi-isomorphism on the third chain map, which is the actual relative map.
-/
theorem relative_homologyMap_isIso_of_absolute
    {P Q : SSetPair.{u}} (f : P ⟶ Q) (R : ModuleCat.{u} ℤ)
    (hleft : ∀ n, IsIso (SSet.homologyMap f.hom.left R n))
    (hright : ∀ n, IsIso (SSet.homologyMap f.hom.right R n)) (n : ℕ) :
    IsIso (SSetPair.homologyMap f R n) := by
  let φ : P.chainComplexShortComplex R ⟶ Q.chainComplexShortComplex R := {
    τ₁ := SSet.chainComplexMap f.hom.left R
    τ₂ := SSet.chainComplexMap f.hom.right R
    τ₃ := SSetPair.chainComplexMap f R
    comm₁₂ := ((SSetPair.chainComplexFunctorLeftToRight (ModuleCat.{u} ℤ)).app R).naturality f
    comm₂₃ := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality f }
  have h₁ : QuasiIso φ.τ₁ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hleft i
  have h₂ : QuasiIso φ.τ₂ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hright i
  have h₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (P.shortExact_chainComplexShortComplex R) (Q.shortExact_chainComplexShortComplex R) h₁ h₂
  exact (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ n).mp
    ((quasiIso_iff φ.τ₃).mp h₃ n)

end HolomorphicAnosov
