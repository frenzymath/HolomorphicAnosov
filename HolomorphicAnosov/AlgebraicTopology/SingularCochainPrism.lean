import HolomorphicAnosov.AlgebraicTopology.SingularCochainReversal

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- The vertex projection for the i-th signed prism simplex.
The ordered vertices are `0,…,i,n,…,i`. -/
def prismVertices (n : ℕ) (i : Fin (n+1)) :
    Fin (n+2) → Fin (n+1) := fun k ↦
  if h : k.val ≤ i.val then
    ⟨k.val, by omega⟩
  else
    ⟨n + i.val + 1 - k.val, by omega⟩

theorem prismVertices_first (n : ℕ) :
    prismVertices n 0 ∘ (0 : Fin (n+2)).succAbove = Fin.rev := by
  funext k
  apply Fin.ext
  simp [prismVertices, Fin.val_rev]

theorem prismVertices_last (n : ℕ) :
    prismVertices n (Fin.last n) ∘ (Fin.last (n+1)).succAbove = id := by
  funext k
  apply Fin.ext
  simp [prismVertices, Fin.succAbove_last, Nat.le_of_lt_succ k.isLt]

theorem prismVertices_adjacent (n : ℕ) (i : Fin n) :
    prismVertices n i.succ ∘ i.succ.castSucc.succAbove =
      prismVertices n i.castSucc ∘ (Fin.last (n+1)).succAbove := by
  funext k
  simp only [Function.comp_apply, Fin.succAbove_last]
  by_cases h : k.val < i.val + 1
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa only [Fin.lt_def,
      Fin.val_castSucc, Fin.val_succ] using h)]
    apply Fin.ext
    simp [prismVertices, show k.val ≤ i.val + 1 by omega,
      show k.val ≤ i.val by omega]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,
      Fin.val_castSucc, Fin.val_succ] using (Nat.le_of_not_gt h))]
    apply Fin.ext
    simp only [prismVertices, Fin.val_succ, Fin.val_castSucc]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    change n + (i.val + 1) + 1 - (k.val + 1) = n + i.val + 1 - k.val
    omega

theorem prismVertices_before (n : ℕ) (i : Fin (n+2)) (j : Fin (n+2))
    (hi : i ≠ 0) (hji : j.val < i.val) :
    prismVertices (n+1) i ∘ (Fin.succAbove (j.castSucc : Fin (n+3))) =
      (Fin.succAbove j) ∘ prismVertices n (i.pred hi) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, prismVertices, Fin.succAbove, Fin.lt_def,
    Fin.val_castSucc, Fin.val_pred, apply_dite Fin.val, dite_eq_ite,
    apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

theorem prismVertices_after (n : ℕ) (i : Fin (n+2)) (j : Fin (n+2))
    (hij : i.val < j.val) :
    prismVertices (n+1) i ∘
        (Fin.succAbove (⟨n + i.val + 2 - j.val, by omega⟩ : Fin (n+3))) =
      (Fin.succAbove j) ∘ prismVertices n (i.castLT (by omega)) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, prismVertices, Fin.succAbove, Fin.lt_def,
    Fin.val_castSucc, Fin.val_castLT, apply_dite Fin.val, dite_eq_ite,
    apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- The before-family face identity after evaluating a cochain on the face. -/
theorem prismFaceBeforeValue (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (i j : Fin (n+2)) (hi : i ≠ 0) (hji : j.val < i.val)
    (a : cochains R X (n+1))
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    simplexValue R X a
        ((TopCat.toSSet.obj X).δ j.castSucc
          (vertexRestrict X (prismVertices (n+1) i) σ)) =
      simplexValue R X a
        (vertexRestrict X (prismVertices n (i.pred hi))
          ((TopCat.toSSet.obj X).δ j σ)) := by
  change simplexValue R X a
      (vertexRestrict X (SimplexCategory.δ j.castSucc)
        (vertexRestrict X (prismVertices (n+1) i) σ)) =
    simplexValue R X a
      (vertexRestrict X (prismVertices n (i.pred hi))
        (vertexRestrict X (SimplexCategory.δ j) σ))
  rw [vertexRestrict_comp]
  change simplexValue R X a
      (vertexRestrict X
        (prismVertices (n+1) i ∘ Fin.succAbove (j.castSucc : Fin (n+3))) σ) =
    simplexValue R X a
      (vertexRestrict X (prismVertices n (i.pred hi))
        (vertexRestrict X (Fin.succAbove j) σ))
  rw [prismVertices_before n i j hi hji]
  rw [vertexRestrict_comp]

/-- The after-family face identity after evaluating a cochain on the face. -/
theorem prismFaceAfterValue (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (i j : Fin (n+2)) (hij : i.val < j.val)
    (a : cochains R X (n+1))
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    simplexValue R X a
        ((TopCat.toSSet.obj X).δ
          (⟨n + i.val + 2 - j.val, by omega⟩ : Fin (n+3))
          (vertexRestrict X (prismVertices (n+1) i) σ)) =
      simplexValue R X a
        (vertexRestrict X (prismVertices n (i.castLT (by omega)))
          ((TopCat.toSSet.obj X).δ j σ)) := by
  change simplexValue R X a
      (vertexRestrict X
        (SimplexCategory.δ
          (⟨n + i.val + 2 - j.val, by omega⟩ : Fin (n+3)))
        (vertexRestrict X (prismVertices (n+1) i) σ)) =
    simplexValue R X a
      (vertexRestrict X (prismVertices n (i.castLT (by omega)))
        (vertexRestrict X (SimplexCategory.δ j) σ))
  rw [vertexRestrict_comp, vertexRestrict_comp]
  exact congrArg (fun v ↦ simplexValue R X a (vertexRestrict X v σ))
    (prismVertices_after n i j hij)

/-- The dual prism operator from Hatcher's signed reversal proof.
For a degree-(n+1) cochain a, its value on an n-simplex is the finite
signed sum over the prism vertex projections. -/
def prismCochain (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (a : cochains R X (n+1)) : cochains R X n :=
  Sigma.desc fun σ ↦ ModuleCat.ofHom
    (LinearMap.mulLeft R
      (∑ i : Fin (n+1), (-1:R)^i.val * reversalSign R (n-i.val) *
        simplexValue R X a (vertexRestrict X (prismVertices n i) σ)))

theorem prismCochain_value (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (a : cochains R X (n+1)) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    simplexValue R X (prismCochain R X n a) σ =
      ∑ i : Fin (n+1), (-1:R)^i.val * reversalSign R (n-i.val) *
        simplexValue R X a (vertexRestrict X (prismVertices n i) σ) := by
  change (((TopCat.toSSet.obj X).ιChainComplex σ) ≫ prismCochain R X n a).hom 1 = _
  simp [SSet.ιChainComplex, prismCochain]

end HolomorphicAnosov.SingularCochain

