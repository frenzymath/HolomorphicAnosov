import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

variable (R : Type u) [CommRing R]

/-- Values on the canonical singular simplex generators determine a cochain. -/
theorem cochain_ext (X : TopCat.{u}) {p : ℕ} (a b : cochains R X p)
    (h : ∀ σ, simplexValue R X a σ = simplexValue R X b σ) : a = b := by
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  ext
  exact h σ

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the native singular coboundary on a generator. -/
theorem simplex_value_coboundary (X : TopCat.{u}) {p : ℕ} (a : cochains R X p)
    (σ : (TopCat.toSSet.obj X) _⦋p+1⦌) :
    simplexValue R X (coboundary R X p a) σ =
      ∑ i : Fin (p+2), (-1 : R)^i.val *
        simplexValue R X a ((TopCat.toSSet.obj X).δ i σ) := by
  let a' : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X p ⟶
      ModuleCat.of R R := a
  change (((TopCat.toSSet.obj X).ιChainComplex σ ≫
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d (p+1) p ≫ a').hom 1) = _
  rw [SSet.ιChainComplex_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, simplexValue, a']
  apply Finset.sum_congr rfl
  intro i hi
  change ((-1 : ℤ) ^ i.val) •
      (a.hom (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of R R) ((TopCat.toSSet.obj X).δ i σ)).hom 1)) =
    (-1 : R) ^ i.val *
      (a.hom (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of R R) ((TopCat.toSSet.obj X).δ i σ)).hom 1))
  simp [zsmul_eq_mul]

open Convexity

/-- Precomposition by the affine vertex map determined by an arbitrary map of vertices. -/
def vertexRestrict (X : TopCat.{u}) {m n : ℕ}
    (v : Fin (m+1) → Fin (n+1)) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X) _⦋m⦌ :=
  (X.toSSetObjEquiv (.op ⦋m⦌)).symm
    ((X.toSSetObjEquiv (.op ⦋n⦌) σ).comp
      ⟨StdSimplex.map v, StdSimplex.continuous_map ℝ v⟩)

theorem vertexRestrict_comp (X : TopCat.{u}) {l m n : ℕ}
    (v : Fin (l+1) → Fin (m+1)) (w : Fin (m+1) → Fin (n+1))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    vertexRestrict X v (vertexRestrict X w σ) = vertexRestrict X (w ∘ v) σ := by
  apply (X.toSSetObjEquiv (.op ⦋l⦌)).injective
  simp only [vertexRestrict, Equiv.apply_symm_apply]
  ext x
  change (X.toSSetObjEquiv (.op ⦋n⦌) σ) (StdSimplex.map w (StdSimplex.map v x)) =
    (X.toSSetObjEquiv (.op ⦋n⦌) σ) (StdSimplex.map (w ∘ v) x)
  exact congrArg (X.toSSetObjEquiv (.op ⦋n⦌) σ) (StdSimplex.map_comp x v w).symm

theorem vertexRestrict_face (X : TopCat.{u}) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    vertexRestrict X f σ = (TopCat.toSSet.obj X).map f.op σ := by
  apply (X.toSSetObjEquiv (.op ⦋m⦌)).injective
  ext x
  rfl

theorem reversal_face (X : TopCat.{u}) {n : ℕ} (i : Fin (n+2))
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    (TopCat.toSSet.obj X).δ i (vertexRestrict X Fin.rev σ) =
      vertexRestrict X Fin.rev ((TopCat.toSSet.obj X).δ i.rev σ) := by
  change (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op
      (vertexRestrict X Fin.rev σ) = _
  rw [← vertexRestrict_face, vertexRestrict_comp]
  change _ = vertexRestrict X Fin.rev
      ((TopCat.toSSet.obj X).map (SimplexCategory.δ i.rev).op σ)
  rw [← vertexRestrict_face, vertexRestrict_comp]
  congr 1
  funext k
  exact Fin.rev_succAbove i k

/-- The signed vertex reversal, with Hatcher's epsilon sign. -/
def reversalSign (n : ℕ) : R := (-1:R)^((n+1).choose 2)

theorem reversalSign_succ (n : ℕ) :
    reversalSign R (n+1) = (-1:R)^(n+1) * reversalSign R n := by
  dsimp [reversalSign]
  rw [show n+1+1=(n+1).succ by rfl, Nat.choose_succ_succ,
    Nat.choose_one_right, pow_add]

def reverseCochain (X : TopCat.{u}) (n : ℕ) (a : cochains R X n) :
    cochains R X n := Sigma.desc fun σ ↦ ModuleCat.ofHom
      (LinearMap.mulLeft R (reversalSign R n *
        simplexValue R X a (vertexRestrict X Fin.rev σ)))

theorem reverseCochain_value (X : TopCat.{u}) (n : ℕ) (a : cochains R X n)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    simplexValue R X (reverseCochain R X n a) σ =
      reversalSign R n * simplexValue R X a (vertexRestrict X Fin.rev σ) := by
  change (((TopCat.toSSet.obj X).ιChainComplex σ) ≫ reverseCochain R X n a).hom 1 = _
  simp [SSet.ιChainComplex, reverseCochain]

theorem reversal_face_sign (n : ℕ) (i : Fin (n+2)) :
    (-1:R)^i.val * reversalSign R n =
      reversalSign R (n+1) * (-1:R)^i.rev.val := by
  rw [reversalSign_succ]
  have he : i.val + i.rev.val = n+1 := by
    simp only [Fin.val_rev]
    omega
  have hs : (-1:R)^i.rev.val * (-1:R)^i.rev.val = 1 := by
    rw [← mul_pow]
    simp
  rw [← he, pow_add]
  calc
    (-1:R)^i.val * reversalSign R n =
        ((-1:R)^i.val * reversalSign R n) * 1 := by ring
    _ = ((-1:R)^i.val * reversalSign R n) *
        ((-1:R)^i.rev.val * (-1:R)^i.rev.val) := by rw [hs]
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- Signed reversal commutes with the native singular coboundary. -/
theorem reverseCochain_coboundary (X : TopCat.{u}) (n : ℕ)
    (a : cochains R X n) :
    coboundary R X n (reverseCochain R X n a) =
      reverseCochain R X (n+1) (coboundary R X n a) := by
  apply cochain_ext R X
  intro σ
  rw [simplex_value_coboundary]
  simp only [reverseCochain_value]
  rw [simplex_value_coboundary, Finset.mul_sum]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro i hi
  change (-1:R)^i.rev.val * (reversalSign R n *
      simplexValue R X a (vertexRestrict X Fin.rev
        ((TopCat.toSSet.obj X).δ i.rev σ))) =
    reversalSign R (n+1) * ((-1:R)^i.val *
      simplexValue R X a ((TopCat.toSSet.obj X).δ i
        (vertexRestrict X Fin.rev σ)))
  rw [reversal_face]
  rw [← mul_assoc, reversal_face_sign R n i.rev]
  simp [Fin.rev_rev, mul_assoc]

end HolomorphicAnosov.SingularCochain

