import HolomorphicAnosov.AlgebraicTopology.SingularCochainReversal
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductEvaluation
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- Hatcher Theorem 3.11 p.211: the reversal sign is multiplicative up to
the Koszul sign. This follows from the count of vertex inversions. -/
theorem reversalSign_add (R : Type u) [CommRing R] (p q : ℕ) :
    reversalSign R (p+q) = (-1:R)^(p*q) * reversalSign R p * reversalSign R q := by
  have hc : (p+q+1).choose 2 = (p+1).choose 2 + (q+1).choose 2 + p*q := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show p+(q+1)+1=(p+q+1)+1 by omega,
        Nat.choose_succ_succ, Nat.choose_one_right, ih]
      have hq := Nat.choose_succ_succ (q+1) 1
      simp only [Nat.choose_one_right] at hq
      nlinarith
  simp only [reversalSign, hc, pow_add]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Hatcher Theorem 3.11 p.211: reversing front and back faces interchanges
the cup factors, with the Koszul sign. Equality transport only commutes the
two natural degrees. This identity holds for arbitrary cochains. -/
theorem reverseCochain_cup (R : Type u) [CommRing R] (X : TopCat.{u})
    (p q : ℕ) (a : cochains R X p) (b : cochains R X q) :
    ((complex R X).XIsoOfEq (Nat.add_comm p q)).hom
      (cupCochain R X (reverseCochain R X p a) (reverseCochain R X q b)) =
    (-1:R)^(p*q) • reverseCochain R X (q+p) (cupCochain R X b a) := by
  have htransport : ∀ {m n : ℕ} (h : m=n) (v : cochains R X m)
      (σ : (TopCat.toSSet.obj X) _⦋n⦌),
      simplexValue R X (((complex R X).XIsoOfEq h).hom v) σ =
        simplexValue R X v ((TopCat.toSSet.obj X).map
          (eqToHom (congrArg SimplexCategory.mk h)).op σ) := by
    intro m n h v σ
    subst h
    simp [HomologicalComplex.XIsoOfEq]
  let e := eqToHom (congrArg SimplexCategory.mk (Nat.add_comm p q))
  have he (k : Fin (p+q+1)) : (e k).val = k.val := by
    change (e.toOrderHom k).val = k.val
    simp [e, SimplexCategory.eqToHom_toOrderHom]
  have hfront : (e : Fin (p+q+1) → Fin (q+p+1)) ∘
      (cupFront p q : Fin (p+1) → Fin (p+q+1)) ∘ Fin.rev =
      Fin.rev ∘ (cupBack q p : Fin (p+1) → Fin (q+p+1)) := by
    funext k
    apply Fin.ext
    simp only [Function.comp_apply, he]
    simp only [Fin.val_rev]
    change p+1-(k.val+1) = q+p+1-(q+k.val+1)
    omega
  have hback : (e : Fin (p+q+1) → Fin (q+p+1)) ∘
      (cupBack p q : Fin (q+1) → Fin (p+q+1)) ∘ Fin.rev =
      Fin.rev ∘ (cupFront q p : Fin (q+1) → Fin (q+p+1)) := by
    funext k
    apply Fin.ext
    simp only [Function.comp_apply, he]
    simp only [Fin.val_rev]
    change p+(q+1-(k.val+1)) = q+p+1-(k.val+1)
    have hk : k.val < q+1 := k.isLt
    omega
  apply cochain_ext R X
  intro σ
  rw [htransport, cup_simplex_value]
  change _ = (-1:R)^(p*q) *
    simplexValue R X (reverseCochain R X (q+p) (cupCochain R X b a)) σ
  simp only [reverseCochain_value, cup_simplex_value, ← vertexRestrict_face,
    vertexRestrict_comp]
  change (reversalSign R p * simplexValue R X a
      (vertexRestrict X ((e : Fin (p+q+1) → Fin (q+p+1)) ∘
        (cupFront p q : Fin (p+1) → Fin (p+q+1)) ∘ Fin.rev) σ)) *
    (reversalSign R q * simplexValue R X b
      (vertexRestrict X ((e : Fin (p+q+1) → Fin (q+p+1)) ∘
        (cupBack p q : Fin (q+1) → Fin (p+q+1)) ∘ Fin.rev) σ)) = _
  rw [hfront, hback, reversalSign_add]
  have hs : (-1:R)^(p*q) * (-1:R)^(q*p) = 1 := by rw [Nat.mul_comm q p, ← mul_pow]; simp
  calc
    _ = ((-1:R)^(p*q) * (-1:R)^(q*p)) *
        ((reversalSign R p * simplexValue R X a
          (vertexRestrict X (Fin.rev ∘ (cupBack q p : Fin (p+1) → Fin (q+p+1))) σ)) *
        (reversalSign R q * simplexValue R X b
          (vertexRestrict X (Fin.rev ∘ (cupFront q p : Fin (q+1) → Fin (q+p+1))) σ))) := by rw [hs]; ring
    _ = _ := by ring

end HolomorphicAnosov.SingularCochain
