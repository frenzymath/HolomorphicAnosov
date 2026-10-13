import Mathlib.Algebra.DirectSum.Algebra
import HolomorphicAnosov.Algebra.ExteriorPowerMinorDiagonal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov

/-- A cup basis embedded in an algebra has the exterior-power principal-minor
formula whenever the algebra action agrees with the degree-one linear action.

Source: Hatcher, Algebraic Topology, Example 3.13 p.213 and Theorem 3.15
pp.216–218. Identify the exterior basis with the cup basis by their common
products in the ambient algebra. The exterior algebra universal property
intertwines the two actions because they agree on the degree-one generators.
Injectivity of the homogeneous inclusion gives the same intertwining in the
specified degree. Transport basis coordinates and apply the exterior minor
formula. No relation between an arbitrary matrix and an arbitrary linear map
is presumed. -/
theorem exterior_cup_basis_minor_g3
    {W V A : Type*} [AddCommGroup W] [Module ℚ W]
    [AddCommGroup V] [Module ℚ V] [Ring A] [Algebra ℚ A]
    (n k : ℕ) (c : Module.Basis (Fin n) ℚ W)
    (b : Module.Basis (Set.powersetCard (Fin n) k) ℚ V)
    (j : V →ₗ[ℚ] A) (hj : Function.Injective j)
    (L : ExteriorAlgebra ℚ W →ₐ[ℚ] A) (P : A →ₐ[ℚ] A)
    (f : V →ₗ[ℚ] V) (g : W →ₗ[ℚ] W)
    (hb : ∀ S, j (b S) = L (c.exteriorPower k S))
    (hf : ∀ x, j (f x) = P (j x))
    (hg : ∀ x, P (L (ExteriorAlgebra.ι ℚ x)) = L (ExteriorAlgebra.ι ℚ (g x)))
    (S : Set.powersetCard (Fin n) k) :
    b.repr (f (b S)) S =
      ((LinearMap.toMatrix c c g).submatrix
        (Subtype.val : S.val → Fin n) (Subtype.val : S.val → Fin n)).det := by
  let e := (c.exteriorPower k).equiv b (Equiv.refl _)
  have he : ∀ x, j (e x) = L x := by
    have h : j.comp e.toLinearMap =
        L.toLinearMap.comp (⋀[ℚ]^k W).subtype := by
      apply (c.exteriorPower k).ext
      intro U
      change j (e (c.exteriorPower k U)) = L (c.exteriorPower k U)
      rw [show e (c.exteriorPower k U) = b U from Module.Basis.equiv_apply _ _ _ _]
      exact hb U
    exact fun x ↦ LinearMap.congr_fun h x
  have hLP : P.comp L = L.comp (ExteriorAlgebra.map g) := by
    apply ExteriorAlgebra.hom_ext
    ext x
    simpa using hg x
  have ha (x : ⋀[ℚ]^k W) : f (e x) = e (exteriorPower.map k g x) := by
    apply hj
    rw [hf, he, he, exteriorPower.coe_map]
    exact DFunLike.congr_fun hLP (x : ExteriorAlgebra ℚ W)
  have hr : ∀ x, b.repr (e x) = (c.exteriorPower k).repr x := by
    intro x
    simp [e, Module.Basis.equiv]
  have hbS : e (c.exteriorPower k S) = b S := by
    exact Module.Basis.equiv_apply _ _ _ _
  rw [← hbS, ha, hr]
  exact exterior_power_minor_diagonal n k c g S

end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped DirectSum
/-- Naturality of the cup product propagates a degree-one matrix to the
principal minors in every degree of an ordered cup basis.
Source: Hatcher, Example 3.13 p.213 and Theorem 3.15 pp.216–218.
The square-zero degree-one inclusion extends to an exterior-algebra map. The
natural graded map acts on its generators by the transposed matrix. Its ordered
products are precisely the specified basis, so exterior basis transport gives
the principal minor; transposition does not change its determinant. -/
theorem graded_cup_basis_minor_g3
    (H : ℕ → Type*) [∀ d, AddCommGroup (H d)] [∀ d, Module ℚ (H d)]
    [DirectSum.GRing H] [DirectSum.GAlgebra ℚ H]
    (n k : ℕ) (α : Fin n → H 1)
    (b : Module.Basis (Set.powersetCard (Fin n) k) ℚ (H k))
    (hsq : ∀ x : H 1, GradedMonoid.GMul.mul x x = 0)
    (hb : ∀ S, DirectSum.lof ℚ ℕ H k (b S) =
      ((S.val.sort (· ≤ ·)).map (fun i ↦ DirectSum.lof ℚ ℕ H 1 (α i))).prod)
    (f : ∀ d, H d →ₗ[ℚ] H d)
    (hone : f 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one)
    (hmul : ∀ p q (x : H p) (y : H q),
      f (p + q) (GradedMonoid.GMul.mul x y) =
        GradedMonoid.GMul.mul (f p x) (f q y))
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hα : ∀ i, f 1 (α i) = ∑ j, B i j • α j)
    (S : Set.powersetCard (Fin n) k) :
    b.repr (f k (b S)) S =
      (B.submatrix (Subtype.val : S.val → Fin n) (Subtype.val : S.val → Fin n)).det := by
  classical
  let c := Pi.basisFun ℚ (Fin n)
  let a : (Fin n → ℚ) →ₗ[ℚ] H 1 := c.constr ℚ α
  let j := fun d ↦ DirectSum.lof ℚ ℕ H d
  have ha (i : Fin n) : a (c i) = α i := c.constr_basis ℚ α i
  have hsq' (x : Fin n → ℚ) : (j 1 (a x)) * (j 1 (a x)) = 0 := by
    change DirectSum.of H 1 (a x) * DirectSum.of H 1 (a x) = 0
    rw [DirectSum.of_mul_of, hsq, map_zero]
  let L : ExteriorAlgebra ℚ (Fin n → ℚ) →ₐ[ℚ] (⨁ d, H d) :=
    ExteriorAlgebra.lift ℚ ⟨(j 1).comp a, hsq'⟩
  let P : (⨁ d, H d) →ₐ[ℚ] (⨁ d, H d) :=
    DirectSum.toAlgebra ℚ H (fun d ↦ (j d).comp (f d))
      (by change j 0 (f 0 GradedMonoid.GOne.one) = 1; rw [hone]; rfl)
      (by
        intro p q x y
        change j (p + q) (f (p + q) (GradedMonoid.GMul.mul x y)) =
          j p (f p x) * j q (f q y)
        rw [hmul]
        exact (DirectSum.of_mul_of _ _).symm)
  have hP (d : ℕ) (x : H d) : P (j d x) = j d (f d x) := by
    change DirectSum.toModule ℚ ℕ (⨁ d, H d) (fun d ↦ (j d).comp (f d))
      (DirectSum.lof ℚ ℕ H d x) = _
    exact DirectSum.toModule_lof ℚ d x
  let g : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) := Matrix.toLin c c B.transpose
  have hgen (x : Fin n → ℚ) : P (L (ExteriorAlgebra.ι ℚ x)) =
      L (ExteriorAlgebra.ι ℚ (g x)) := by
    simp only [L, ExteriorAlgebra.lift_ι_apply, LinearMap.comp_apply, hP]
    congr 1
    have he : (f 1).comp a = a.comp g := by
      apply c.ext
      intro i
      simp only [LinearMap.comp_apply, ha, hα]
      rw [show g (c i) = ∑ t, B i t • c t by
        simp [g, Matrix.toLin_apply, Matrix.mulVec, dotProduct, Finsupp.single_apply]]
      simp only [map_sum, map_smul, ha]
    exact LinearMap.congr_fun he x
  have hbasis (U : Set.powersetCard (Fin n) k) :
      j k (b U) = L (c.exteriorPower k U) := by
    rw [hb, exteriorPower.basis_apply]
    change _ = L (ExteriorAlgebra.ιMulti ℚ k
      (c ∘ Set.powersetCard.ofFinEmbEquiv.symm U))
    rw [ExteriorAlgebra.ιMulti_apply, map_list_prod]
    rw [List.map_ofFn]
    simp only [L, ExteriorAlgebra.lift_ι_apply,
      LinearMap.comp_apply, Function.comp_def, ha,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
    have hs : List.ofFn (U.val.orderEmbOfFin U.property) = U.val.sort (· ≤ ·) := by
      rw [List.ofFn_eq_map, Finset.listMap_orderEmbOfFin_finRange]
    rw [List.ofFn_comp' (U.val.orderEmbOfFin U.property) (fun i ↦ j 1 (α i)), hs]
  have he := exterior_cup_basis_minor_g3 n k c b (j k)
    (DFinsupp.single_injective) L P (f k) g hbasis
    (fun x ↦ (hP k x).symm) hgen S
  change _ = ((LinearMap.toMatrix c c (Matrix.toLin c c B.transpose)).submatrix _ _).det at he
  rw [LinearMap.toMatrix_toLin] at he
  change _ = (B.submatrix (Subtype.val : S.val → Fin n)
    (Subtype.val : S.val → Fin n)).transpose.det at he
  simpa only [Matrix.det_transpose] using he

end HolomorphicAnosov

namespace HolomorphicAnosov
open scoped DirectSum
/-- Embedding a recursively defined homogeneous cup monomial into the direct
sum gives the ordinary ordered product. This is induction on the list, with
homogeneous degree casts removed by equality elimination. -/
theorem graded_monomial_product_g3
    (H : ℕ → Type*) [∀ d, AddCommGroup (H d)] [∀ d, Module ℚ (H d)]
    [DirectSum.GRing H] [DirectSum.GAlgebra ℚ H]
    (cup : ∀ p q, H p →ₗ[ℚ] H q →ₗ[ℚ] H (p + q)) (one : H 0)
    (hcup : ∀ p q x y, GradedMonoid.GMul.mul x y = cup p q x y)
    (hone : GradedMonoid.GOne.one = one)
    {I : Type*} (α : I → H 1) (l : List I) :
    let monomial : ∀ l : List I, H l.length := fun l ↦
      List.rec (motive := fun l ↦ H l.length) one
        (fun i l v ↦ cast (congrArg H (Nat.add_comm 1 l.length))
          (cup 1 l.length (α i) v)) l
    DirectSum.lof ℚ ℕ H l.length (monomial l) =
      (l.map (fun i ↦ DirectSum.lof ℚ ℕ H 1 (α i))).prod := by
  let monomial : ∀ l : List I, H l.length := fun l ↦
      List.rec (motive := fun l ↦ H l.length) one
        (fun i l v ↦ cast (congrArg H (Nat.add_comm 1 l.length))
          (cup 1 l.length (α i) v)) l
  change DirectSum.lof ℚ ℕ H l.length (monomial l) = _
  have hc {p q : ℕ} (h : p = q) (x : H p) :
      DirectSum.lof ℚ ℕ H q (cast (congrArg H h) x) = DirectSum.lof ℚ ℕ H p x := by
    subst q
    rfl
  induction l with
  | nil =>
    change DirectSum.lof ℚ ℕ H 0 one = 1
    rw [← hone]
    rfl
  | cons i l ih =>
    change DirectSum.lof ℚ ℕ H (l.length + 1)
      (cast (congrArg H (Nat.add_comm 1 l.length))
        (cup 1 l.length (α i) (monomial l))) = _
    rw [hc (Nat.add_comm 1 l.length), ← hcup]
    change DirectSum.of H (1 + l.length)
      (GradedMonoid.GMul.mul (α i) (monomial l)) = _
    rw [← DirectSum.of_mul_of]
    simpa only [List.map_cons, List.prod_cons, DirectSum.lof_eq_of] using
      congrArg (fun x ↦ DirectSum.lof ℚ ℕ H 1 (α i) * x) ih
end HolomorphicAnosov
