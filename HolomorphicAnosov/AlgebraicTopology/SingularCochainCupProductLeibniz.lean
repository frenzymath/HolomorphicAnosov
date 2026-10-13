import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductEvaluation
import HolomorphicAnosov.AlgebraicTopology.SingularCochainReversal

/-!
# The singular cochain cup-product Leibniz identity

Source: Hatcher, *Algebraic Topology*, Lemma 3.6 and its proof, p.206.
DAG node: `topo.singular_cochain_cup_product_leibniz_g6`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- Leibniz's identity for the prescribed front/back singular cup cochain.

Source: Hatcher, *Algebraic Topology*, Lemma 3.6, p. 206. Evaluate on
each singular `(p+q+1)`-simplex and split its alternating face sum at the
shared vertex. The final term of the front-face sum and the first term of
the back-face sum have equal restrictions and opposite signs, so cancel.
The remaining terms are exactly the two displayed cup cochains. The
degree isomorphism identifies `(p+1)+q` with `p+q+1`; it does not change
the underlying cochain. This includes zero degrees and arbitrary spaces.
-/
theorem cochain_cup_leibniz (R : Type u) [CommRing R] (X : TopCat.{u}) {p q : ℕ}
 (a : cochains R X p) (b : cochains R X q) :
 coboundary R X (p+q) (cupCochain R X a b) =
 ((complex R X).XIsoOfEq (show (p+1)+q=p+q+1 by omega)).hom
   (cupCochain R X (coboundary R X p a) b) +
 (-1:R)^p • cupCochain R X a (coboundary R X q b) := by
 apply cochain_ext R X
 intro σ
 let early (i : Fin (p+1)) : Fin (p+q+2) :=
   ⟨i.val, i.isLt.trans_le (Nat.le_succ_of_le (Nat.succ_le_succ (Nat.le_add_right p q)))⟩
 let late (j : Fin (q+1)) : Fin (p+q+2) :=
   ⟨p+1+j.val, by
     simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
       using Nat.add_lt_add_left j.isLt (p+1)⟩
 let long_front : ⦋p+1⦌ ⟶ ⦋p+q+1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i ↦
        ⟨i.val, i.isLt.trans_le (Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_add_right p q)))⟩
      monotone' := fun _ _ h ↦ h }
 let shifted_back : ⦋q⦌ ⟶ ⦋p+q+1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i ↦ ⟨p+1+i.val, by omega⟩
      monotone' := fun _ _ h ↦ Nat.add_le_add_left h _ }
 have early_front (i : Fin (p+1)) :
  cupFront p q ≫ SimplexCategory.δ ((early i) : Fin (p+q+2)) =
  SimplexCategory.δ i.castSucc ≫ long_front := by
  ext k
  have hk : k.val < p+1 := k.isLt
  change (((early i) : Fin (p+q+2)).succAbove
    (⟨k.val, by omega⟩ : Fin (p+q+1))).val = (i.castSucc.succAbove k).val
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl
 have early_back (i : Fin (p+1)) :
  cupBack p q ≫ SimplexCategory.δ ((early i) : Fin (p+q+2)) = shifted_back := by
  ext k
  have hk : k.val < q+1 := k.isLt
  change (((early i) : Fin (p+q+2)).succAbove
    (⟨p+k.val, by omega⟩ : Fin (p+q+1))).val = p+1+k.val
  rw [Fin.succAbove_of_le_castSucc]
  · change p+k.val+1 = p+1+k.val
    omega
  · change i.val ≤ p+k.val
    omega
 let long_back : ⦋q+1⦌ ⟶ ⦋p+q+1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i ↦ ⟨p+i.val, by omega⟩
      monotone' := fun _ _ h ↦ Nat.add_le_add_left h _ }
 have late_front (j : Fin (q+1)) :
  cupFront p q ≫ SimplexCategory.δ ((late j) : Fin (p+q+2)) = cupFront p (q+1) := by
  ext k
  have hk : k.val < p+1 := k.isLt
  change (((late j) : Fin (p+q+2)).succAbove
    (⟨k.val, by omega⟩ : Fin (p+q+1))).val = k.val
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change k.val < p+1+j.val
    omega
 have late_back (j : Fin (q+1)) :
  cupBack p q ≫ SimplexCategory.δ ((late j) : Fin (p+q+2)) =
  SimplexCategory.δ j.succ ≫ long_back := by
  ext k
  have hk : k.val < q+1 := k.isLt
  change (((late j) : Fin (p+q+2)).succAbove
    (⟨p+k.val, by omega⟩ : Fin (p+q+1))).val = p+(j.succ.succAbove k).val
  simp only [late, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
 have shared_front :
  SimplexCategory.δ (Fin.last (p+1)) ≫ long_front = cupFront p (q+1) := by
  ext k
  have hk : k.val < p+1 := k.isLt
  change ((Fin.last (p+1)).succAbove k).val = k.val
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change k.val < p+1
    exact hk
 have shared_back :
  SimplexCategory.δ (0 : Fin (q+2)) ≫ long_back = shifted_back := by
  ext k
  change p+((0 : Fin (q+2)).succAbove k).val = p+1+k.val
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
  change p+(k.val+1)=p+1+k.val
  omega

 have simplex_restrict_comp {l m n : ℕ}
     (f : ⦋l⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
     (TopCat.toSSet.obj X).map f.op ((TopCat.toSSet.obj X).map g.op σ) =
       (TopCat.toSSet.obj X).map (f ≫ g).op σ := by
   exact (CategoryTheory.congr_fun ((TopCat.toSSet.obj X).map_comp g.op f.op) σ).symm
 have cup_face_early
  (i : Fin (p+1)) :
  simplexValue R X (cupCochain R X a b)
    ((TopCat.toSSet.obj X).δ ((early i) : Fin (p+q+2)) σ) =
  simplexValue R X a ((TopCat.toSSet.obj X).δ i.castSucc
    ((TopCat.toSSet.obj X).map (long_front).op σ)) *
  simplexValue R X b ((TopCat.toSSet.obj X).map (shifted_back).op σ) := by
  rw [cup_simplex_value]
  change simplexValue R X a ((TopCat.toSSet.obj X).map (cupFront p q).op
    ((TopCat.toSSet.obj X).map (SimplexCategory.δ (early i)).op σ)) *
    simplexValue R X b ((TopCat.toSSet.obj X).map (cupBack p q).op
    ((TopCat.toSSet.obj X).map (SimplexCategory.δ (early i)).op σ)) = _
  rw [simplex_restrict_comp, simplex_restrict_comp, early_front, early_back]
  rw [← simplex_restrict_comp]
  rfl

 have cup_face_late
  (j : Fin (q+1)) :
  simplexValue R X (cupCochain R X a b)
    ((TopCat.toSSet.obj X).δ ((late j) : Fin (p+q+2)) σ) =
  simplexValue R X a ((TopCat.toSSet.obj X).map (cupFront p (q+1)).op σ) *
  simplexValue R X b ((TopCat.toSSet.obj X).δ j.succ
    ((TopCat.toSSet.obj X).map (long_back).op σ)) := by
  rw [cup_simplex_value]
  change simplexValue R X a ((TopCat.toSSet.obj X).map (cupFront p q).op
    ((TopCat.toSSet.obj X).map (SimplexCategory.δ (late j)).op σ)) *
    simplexValue R X b ((TopCat.toSSet.obj X).map (cupBack p q).op
    ((TopCat.toSSet.obj X).map (SimplexCategory.δ (late j)).op σ)) = _
  rw [simplex_restrict_comp, simplex_restrict_comp, late_front, late_back]
  rw [← simplex_restrict_comp]
  rfl

 have split_cup_sum (f : Fin (p+q+2) → R) :
     ∑ i, f i = (∑ i : Fin (p+1), f (early i)) +
       ∑ j : Fin (q+1), f (late j) := by
   have h : (p+1)+(q+1)=p+q+2 := by omega
   rw [← (finCongr h).sum_comp f, Fin.sum_univ_add]
   rfl

 have simplex_cup_leibniz  :
  simplexValue R X (coboundary R X (p+q) (cupCochain R X a b)) σ =
  simplexValue R X (coboundary R X p a) ((TopCat.toSSet.obj X).map (long_front).op σ) *
    simplexValue R X b ((TopCat.toSSet.obj X).map (shifted_back).op σ) +
  (-1:R)^p * simplexValue R X a ((TopCat.toSSet.obj X).map (cupFront p (q+1)).op σ) *
    simplexValue R X (coboundary R X q b) ((TopCat.toSSet.obj X).map (long_back).op σ) := by
  rw [simplex_value_coboundary, split_cup_sum]
  simp only [cup_face_early, cup_face_late]
  rw [simplex_value_coboundary, simplex_value_coboundary]
  rw [Fin.sum_univ_castSucc (fun i : Fin (p+2) ↦ (-1:R)^i.val *
    simplexValue R X a ((TopCat.toSSet.obj X).δ i ((TopCat.toSSet.obj X).map (long_front).op σ)))]
  rw [Fin.sum_univ_succ (fun j : Fin (q+2) ↦ (-1:R)^j.val *
    simplexValue R X b ((TopCat.toSSet.obj X).δ j ((TopCat.toSSet.obj X).map (long_back).op σ)))]
  simp only [early, late, Fin.val_castSucc, Fin.val_last, Fin.val_zero, pow_zero, one_mul,
    Fin.val_succ, Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, pow_add, pow_succ]
  have hfront :
    (TopCat.toSSet.obj X).δ (Fin.last (p+1)) ((TopCat.toSSet.obj X).map (long_front).op σ) =
    (TopCat.toSSet.obj X).map (cupFront p (q+1)).op σ := by
    change (TopCat.toSSet.obj X).map (SimplexCategory.δ (Fin.last (p+1))).op _ = _
    rw [simplex_restrict_comp, shared_front]
    rfl
  have hback :
    (TopCat.toSSet.obj X).δ (0 : Fin (q+2)) ((TopCat.toSSet.obj X).map (long_back).op σ) =
    (TopCat.toSSet.obj X).map (shifted_back).op σ := by
    change (TopCat.toSSet.obj X).map (SimplexCategory.δ (0 : Fin (q+2))).op _ = _
    rw [simplex_restrict_comp, shared_back]
  rw [hfront, hback]
  ring_nf
  ac_rfl

 have simplex_value_degree_cast {m n : ℕ} (h : m=n)
     (a : cochains R X m) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
     simplexValue R X (((complex R X).XIsoOfEq h).hom a) σ =
       simplexValue R X a ((TopCat.toSSet.obj X).map
         (eqToHom (congrArg SimplexCategory.mk h)).op σ) := by
   subst h
   simp [HomologicalComplex.XIsoOfEq]

 have long_front_cast (h : (p+1)+q=p+q+1) :
  cupFront (p+1) q ≫ eqToHom (congrArg SimplexCategory.mk h) = long_front := by
  ext k
  simp [cupFront,long_front,SimplexCategory.eqToHom_toOrderHom]
 have shifted_back_cast (h : (p+1)+q=p+q+1) :
  cupBack (p+1) q ≫ eqToHom (congrArg SimplexCategory.mk h) = shifted_back := by
  ext k
  simp [cupBack,shifted_back,SimplexCategory.eqToHom_toOrderHom]
 have long_back_eq : long_back = cupBack p (q+1) := rfl

 change simplexValue R X (coboundary R X (p+q) (cupCochain R X a b)) σ =
   simplexValue R X (((complex R X).XIsoOfEq (show (p+1)+q=p+q+1 by omega)).hom
     (cupCochain R X (coboundary R X p a) b)) σ +
   (-1:R)^p * simplexValue R X (cupCochain R X a (coboundary R X q b)) σ
 rw [simplex_value_degree_cast]
 rw [cup_simplex_value, cup_simplex_value, simplex_cup_leibniz]
 rw [simplex_restrict_comp, simplex_restrict_comp,
   long_front_cast (by omega), shifted_back_cast (by omega)]
 rw [long_back_eq]
 ring_nf
 rfl


end HolomorphicAnosov.SingularCochain
