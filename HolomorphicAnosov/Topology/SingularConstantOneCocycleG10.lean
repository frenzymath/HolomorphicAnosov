import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

/-!
# The constant-one singular zero-cocycle

Source: Hatcher, *Algebraic Topology*, pp. 197–198 and 207.
The literal constant-one cochain annihilates the alternating boundary of each
singular one-simplex, and its value on every zero-simplex is one. The proof uses
Mathlib's chain coproduct and boundary formula, including for an empty space
or the zero ring, with no connectedness or nontriviality hypothesis.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false in
/-- The literal constant-one singular cochain is a normalized zero-cocycle.
Source: Hatcher, Algebraic Topology, pp.197–198 and 207. On each singular
one-simplex, the alternating boundary has two endpoints with opposite signs;
the constant-one cochain therefore kills it. Coproduct extensionality proves
the whole composite zero. The coproduct inclusion/descent identity gives value
one on each zero-simplex. Empty spaces and the zero ring are allowed. -/
theorem exists_constantOne_cocycle (R : Type u) [CommRing R] (X : TopCat.{u}) :
    ∃ u : cycles R (complex R X) 0,
      u.val = oneCochain R X ∧
      ∀ σ : (TopCat.toSSet.obj X) _⦋0⦌, simplexValue R X u.val σ = 1 := by
  have hd : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d 1 0 ≫
      oneCochain R X = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [Fin.sum_univ_two, Preadditive.add_comp, oneCochain, SSet.ιChainComplex]
  have hu : oneCochain R X ∈ cycles R (complex R X) 0 := by
    change ((complex R X).d 0 ((ComplexShape.up ℕ).next 0)).hom
      (oneCochain R X) = 0
    rw [(ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk 0 1 rfl)]
    exact hd
  refine ⟨⟨oneCochain R X, hu⟩, rfl, ?_⟩
  intro σ
  have hi : (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ ≫
      oneCochain R X = 𝟙 (ModuleCat.of R R) := by
    simp [oneCochain, SSet.ιChainComplex]
  exact congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R ↦ f 1) hi

end HolomorphicAnosov.SingularCochain
