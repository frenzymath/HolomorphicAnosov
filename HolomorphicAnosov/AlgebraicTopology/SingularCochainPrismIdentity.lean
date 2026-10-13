import HolomorphicAnosov.AlgebraicTopology.SingularCochainPrismCancellation
import HolomorphicAnosov.AlgebraicTopology.FiniteOffDiagonalSum
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- Hatcher, Algebraic Topology, Theorem 3.11, pp.211–212. The two double
sums in the prism coboundary formula cancel along the off-diagonal face
families, and the two surviving diagonal families telescope to reversal minus
identity. This is the complete positive-degree formula, including n = 0. -/
theorem prism_identity_succ (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (a : cochains R X (n+1)) :
    coboundary R X n (prismCochain R X n a) +
        prismCochain R X (n+1) (coboundary R X (n+1) a) =
      reverseCochain R X (n+1) a - a := by
  classical
  apply cochain_ext R X
  intro σ
  let t (i : Fin (n+2)) (j : Fin (n+3)) : R :=
    (-1:R)^i.val * reversalSign R (n+1-i.val) * (-1:R)^j.val *
      simplexValue R X a ((TopCat.toSSet.obj X).δ j
        (vertexRestrict X (prismVertices (n+1) i) σ))
  let b (j : Fin (n+2)) (k : Fin (n+1)) : R :=
    (-1:R)^j.val * (-1:R)^k.val * reversalSign R (n-k.val) *
      simplexValue R X a (vertexRestrict X (prismVertices n k)
        ((TopCat.toSSet.obj X).δ j σ))
  let v (i j : Fin (n+2)) : Fin (n+2) :=
    if h : j.val ≤ i.val then j else ⟨n+i.val+2-j.val, by omega⟩
  have hv (i j : Fin (n+2)) : v i (v i j) = j := by
    dsimp [v]
    split_ifs with h h' <;> ext <;> simp_all <;> omega
  let e (i : Fin (n+2)) : Equiv.Perm (Fin (n+2)) :=
    { toFun := v i, invFun := v i, left_inv := hv i, right_inv := hv i }
  let f (i j : Fin (n+2)) : R :=
    t i (v i j).castSucc + if j = i then t i (Fin.last (n+2)) else 0
  have hrow (i : Fin (n+2)) : (∑ j, t i j) = ∑ j, f i j := by
    rw [Fin.sum_univ_castSucc]
    dsimp [f]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    exact (Equiv.sum_comp (e i) (fun j ↦ t i j.castSucc)).symm
  have hoff (j : Fin (n+2)) (k : Fin (n+1)) : f (j.succAbove k) j + b j k = 0 := by
    have hne : j ≠ j.succAbove k := (Fin.succAbove_ne j k).symm
    simp only [f, hne, ite_false, add_zero]
    by_cases hjk : j.val ≤ k.val
    · have hji : j.val < (j.succAbove k).val := by
        simp [Fin.succAbove, Fin.lt_def, show ¬ k.val < j.val by omega]
        omega
      have hi : j.succAbove k ≠ 0 := by intro h; rw [h] at hji; simp at hji
      have hp : (j.succAbove k).pred hi = k := by
        ext
        simp only [Fin.val_pred]
        simp [Fin.succAbove, Fin.lt_def, show ¬ k.val < j.val by omega]
      have h := prism_before_cancel R X n (j.succAbove k) j hi hji a σ
      dsimp [v]
      rw [dite_eq_left (by omega)]
      simpa only [t, b, Fin.val_castSucc, hp] using h
    · have hji : (j.succAbove k).val < j.val := by
        simp [Fin.succAbove, Fin.lt_def, show k.val < j.val by omega]
      have hp : (j.succAbove k).castLT (by omega) = k := by
        ext
        simp [Fin.succAbove, Fin.lt_def, show k.val < j.val by omega]
      have hpv : (j.succAbove k).val = k.val := congrArg Fin.val hp
      have h := prism_after_cancel R X n (j.succAbove k) j hji a σ
      dsimp [v]
      rw [dite_eq_right (by omega)]
      simpa only [t, b, Fin.val_castSucc, Fin.castSucc_mk, hp, hpv] using h
  have hsum := fin_double_sum_cancel_offDiagonal (n+1) f b hoff
  have heval :
      simplexValue R X (coboundary R X n (prismCochain R X n a)) σ +
        simplexValue R X (prismCochain R X (n+1) (coboundary R X (n+1) a)) σ =
      (∑ j, ∑ k, b j k) + ∑ i, ∑ j, t i j := by
    rw [simplex_value_coboundary, prismCochain_value]
    simp_rw [prismCochain_value, simplex_value_coboundary, Finset.mul_sum]
    dsimp [b, t]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
      apply Finset.sum_congr rfl <;> intro j hj <;> ring
  change simplexValue R X (coboundary R X n (prismCochain R X n a)) σ +
      simplexValue R X (prismCochain R X (n+1) (coboundary R X (n+1) a)) σ =
    simplexValue R X (reverseCochain R X (n+1) a) σ - simplexValue R X a σ
  rw [heval, add_comm]
  simp_rw [hrow]
  rw [hsum]
  have hdiag (i : Fin (n+2)) : f i i = t i i.castSucc + t i (Fin.last (n+2)) := by
    simp [f, v]
  simp_rw [hdiag]
  rw [Finset.sum_add_distrib]
  convert prism_diagonal_sum R X (n+1) a σ using 1
  simp only [t, Fin.val_castSucc, Fin.val_last, SimplicialObject.δ,
    ← vertexRestrict_face, vertexRestrict_comp]
  rfl

end HolomorphicAnosov.SingularCochain
