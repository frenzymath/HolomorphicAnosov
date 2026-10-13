import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Lifting a relative class from an ambient representative

Source: Hatcher, Algebraic Topology, relative chains pp.115–117 and the
support-enlargement argument of Lemma 3.27 step (4), pp.237–238.
-/

open CategoryTheory
namespace HolomorphicAnosov
universe u

/-- An ambient representative whose boundary comes from the source subspace
lifts a target relative homology class along the actual map of pairs.
Source: Hatcher, relative chains pp.115–117 and Lemma 3.27 step (4), pp.237–238.

Proof: project the ambient chain to the source relative quotient. Its boundary
vanishes because the ambient boundary is the image of a subspace chain and the
relative quotient annihilates that image. This defines a native source cycle.
Naturality of the relative quotient identifies its image with the chosen target
cycle. Injectivity of the target cycle inclusion and naturality of the homology
projection show that the resulting source class maps to the given target class.
No positivity of degree or injectivity of the ambient pair map is required. -/
theorem relative_homology_lift_of_ambient_boundary
    {P Q : SSetPair.{u}} (f : P ⟶ Q) (R : ModuleCat.{u} ℤ) (i : ℕ)
    (c : ((Q.chainComplex R).cycles i : ModuleCat.{u} ℤ))
    (z : ((P.right.chainComplex R).X i : ModuleCat.{u} ℤ))
    (hb : ∃ b : ((P.left.chainComplex R).X ((ComplexShape.down ℕ).next i) :
        ModuleCat.{u} ℤ),
      (SSet.chainComplexMap P.hom R).f ((ComplexShape.down ℕ).next i) b =
        (P.right.chainComplex R).d i ((ComplexShape.down ℕ).next i) z)
    (hc : (Q.chainComplexπ R).f i ((SSet.chainComplexMap f.hom.right R).f i z) =
      (Q.chainComplex R).iCycles i c) :
    ∃ a : (P.homology R i : ModuleCat.{u} ℤ),
      SSetPair.homologyMap f R i a = (Q.chainComplex R).homologyπ i c := by
  let A := P.chainComplex R
  let B := Q.chainComplex R
  let φ := SSetPair.chainComplexMap f R
  let w := (P.chainComplexπ R).f i z
  have hw : A.d i ((ComplexShape.down ℕ).next i) w = 0 := by
    obtain ⟨b, hb⟩ := hb
    have he := congrArg (fun m ↦ m z)
      ((P.chainComplexπ R).comm i ((ComplexShape.down ℕ).next i))
    change A.d i ((ComplexShape.down ℕ).next i) w = _ at he
    rw [he]
    change (P.chainComplexπ R).f ((ComplexShape.down ℕ).next i)
      ((P.right.chainComplex R).d i ((ComplexShape.down ℕ).next i) z) = 0
    rw [← hb]
    exact congrArg (fun m ↦ m b)
      (P.chainComplex_condition_f R ((ComplexShape.down ℕ).next i))
  have hφw : φ.f i w = B.iCycles i c := by
    have he := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality f
    have hei := congrArg (fun m ↦ m.f i z) he
    change (Q.chainComplexπ R).f i ((SSet.chainComplexMap f.hom.right R).f i z) =
      φ.f i w at hei
    exact hei.symm.trans hc
  let cA := A.cyclesMk w ((ComplexShape.down ℕ).next i) rfl hw
  refine ⟨A.homologyπ i cA, ?_⟩
  have hcA : A.iCycles i cA = w := A.i_cyclesMk w _ rfl hw
  have he : HomologicalComplex.cyclesMap φ i cA = c := by
    apply (ModuleCat.mono_iff_injective (B.iCycles i)).mp inferInstance
    have hn := congrArg (fun m ↦ m cA) (HomologicalComplex.cyclesMap_i φ i)
    exact hn.trans (by change φ.f i (A.iCycles i cA) = _; rw [hcA]; exact hφw)
  have hn := congrArg (fun m ↦ m cA) (HomologicalComplex.homologyπ_naturality φ i)
  exact hn.trans (congrArg (B.homologyπ i) he)

end HolomorphicAnosov
