import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductEvaluation

/-! # Associativity of the singular cochain cup product

Source: Hatcher, Algebraic Topology, p.207, associativity of the front/back formula.
-/
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- The front/back cup product of arbitrary singular cochains is associative after
identifying the degrees (p+q)+r and p+(q+r).

Source: Hatcher, Algebraic Topology, p.207. On each singular simplex the two
products evaluate on the consecutive faces [0,…,p], [p,…,p+q], [p+q,…,p+q+r].
The face identities follow by their vertex indices, including zero degrees.
Ring multiplication is associative, and evaluation on the free simplex generators
determines a cochain. Degree identification is the complex's equality isomorphism. -/
theorem cupCochain_assoc (R : Type u) [CommRing R] (X : TopCat.{u})
    {p q r : ℕ} (a : cochains R X p) (b : cochains R X q) (c : cochains R X r) :
    ((complex R X).XIsoOfEq (Nat.add_assoc p q r)).hom
      (cupCochain R X (cupCochain R X a b) c) =
      cupCochain R X a (cupCochain R X b c) := by
  have htransport : ∀ {m n : ℕ} (h : m = n) (v : cochains R X m)
      (σ : (TopCat.toSSet.obj X) _⦋n⦌),
      simplexValue R X (((complex R X).XIsoOfEq h).hom v) σ =
        simplexValue R X v ((TopCat.toSSet.obj X).map
          (eqToHom (congrArg SimplexCategory.mk h)).op σ) := by
    intro m n h v σ
    subst h
    simp [HomologicalComplex.XIsoOfEq]
  let e := eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc p q r))
  have hfront : cupFront p q ≫ cupFront (p+q) r ≫ e = cupFront p (q+r) := by
    ext k
    simp [cupFront, e, SimplexCategory.eqToHom_toOrderHom]
  have hmiddle : cupBack p q ≫ cupFront (p+q) r ≫ e =
      cupFront q r ≫ cupBack p (q+r) := by
    ext k
    simp [cupFront, cupBack, e, SimplexCategory.eqToHom_toOrderHom]
  have hback : cupBack (p+q) r ≫ e = cupBack q r ≫ cupBack p (q+r) := by
    ext k
    simp [cupBack, e, SimplexCategory.eqToHom_toOrderHom, Nat.add_assoc]
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  ext
  change simplexValue R X (((complex R X).XIsoOfEq (Nat.add_assoc p q r)).hom
      (cupCochain R X (cupCochain R X a b) c)) σ =
    simplexValue R X (cupCochain R X a (cupCochain R X b c)) σ
  rw [htransport, cup_simplex_value, cup_simplex_value,
    cup_simplex_value, cup_simplex_value]
  have hcomp {l m n : SimplexCategory} (f : l ⟶ m) (g : m ⟶ n)
      (τ : (TopCat.toSSet.obj X).obj (op n)) :
      (TopCat.toSSet.obj X).map f.op ((TopCat.toSSet.obj X).map g.op τ) =
        (TopCat.toSSet.obj X).map (f ≫ g).op τ := by
    rw [op_comp, Functor.map_comp]
    rfl
  simp only [hcomp]
  change simplexValue R X a ((TopCat.toSSet.obj X).map
      (cupFront p q ≫ cupFront (p+q) r ≫ e).op σ) *
    simplexValue R X b ((TopCat.toSSet.obj X).map
      (cupBack p q ≫ cupFront (p+q) r ≫ e).op σ) *
    simplexValue R X c ((TopCat.toSSet.obj X).map (cupBack (p+q) r ≫ e).op σ) = _
  rw [hfront, hmiddle, hback, mul_assoc]

end HolomorphicAnosov.SingularCochain
