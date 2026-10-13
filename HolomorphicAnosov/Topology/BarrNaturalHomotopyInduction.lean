import HolomorphicAnosov.Topology.BarrRelativeHomotopyInduction
import Mathlib.Algebra.Homology.Functor

/-! Barr, Acyclic Models, Chapter 5 §5 Proposition 5.5, p.116:
relative uniqueness in the category of functors. -/

open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov

variable {C V : Type*} [Category* C] [Category* V] [Preadditive V]

/-- Regard a functor of chain complexes as a chain complex of functors.
The differentials are natural because its maps are chain maps. -/
def chainComplexOfFunctor (S : C ⥤ ChainComplex V ℕ) : ChainComplex (C ⥤ V) ℕ where
  X i := S ⋙ HomologicalComplex.eval V (.down ℕ) i
  d i j := { app X := (S.obj X).d i j
             naturality X Y f := (S.map f).comm i j }
  shape i j hij := by ext X; exact (S.obj X).shape i j hij
  d_comp_d' i j k _ _ := by ext X; exact (S.obj X).d_comp_d i j k

/-- A natural chain map, viewed degree by degree in the functor category. -/
def chainMapOfNaturalTransformation {S T : C ⥤ ChainComplex V ℕ} (Φ : S ⟶ T) :
    chainComplexOfFunctor S ⟶ chainComplexOfFunctor T where
  f i := { app X := (Φ.app X).f i
           naturality X Y f := congrArg (fun g ↦ g.f i) (Φ.naturality f) }
  comm' i j _ := by ext X; exact (Φ.app X).comm i j

/-- Natural relative uniqueness from natural cycle fillings.

Source: Barr, Acyclic Models, Chapter 5 §5 Proposition 5.5, p.116.
Apply the residual-cycle induction in the preadditive category of functors.
Its components are natural transformations; evaluating their equations gives
objectwise homotopies and their naturality. Starting the induction with zero
preserves the prescribed zero degree-zero component. -/
theorem barr_natural_relative_homotopy
    (S T : C ⥤ ChainComplex V ℕ) (Φ Ψ : S ⟶ T)
    (hzero : ∀ X, (Φ.app X).f 0 = (Ψ.app X).f 0)
    (hfill : ∀ (n : ℕ)
      (r : (chainComplexOfFunctor S).X (n + 1) ⟶
        (chainComplexOfFunctor T).X (n + 1)),
      r ≫ (chainComplexOfFunctor T).d (n + 1) n = 0 →
      ∃ s : (chainComplexOfFunctor S).X (n + 1) ⟶
        (chainComplexOfFunctor T).X (n + 2),
        s ≫ (chainComplexOfFunctor T).d (n + 2) (n + 1) = r) :
    ∃ H : ∀ X, _root_.Homotopy (Φ.app X) (Ψ.app X),
      (∀ X Y (f : X ⟶ Y) (i j : ℕ),
        (S.map f).f i ≫ (H Y).hom i j = (H X).hom i j ≫ (T.map f).f j) ∧
      (∀ X, (H X).hom 0 1 = 0) := by
  obtain ⟨H, hH⟩ := barr_relative_homotopy
    (chainMapOfNaturalTransformation Φ) (chainMapOfNaturalTransformation Ψ)
    (by ext X; exact hzero X) hfill
  let h (X : C) : _root_.Homotopy (Φ.app X) (Ψ.app X) :=
    { hom i j := (H.hom i j).app X
      zero i j hij := NatTrans.congr_app (H.zero i j hij) X
      comm i := NatTrans.congr_app (H.comm i) X }
  exact ⟨h, fun X Y f i j ↦ (H.hom i j).naturality f,
    fun X ↦ NatTrans.congr_app hH X⟩

end HolomorphicAnosov
