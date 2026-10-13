import HolomorphicAnosov.AlgebraicTopology.SingularCochainPrism

/-!
# Signed reversal-prism face cancellation

Hatcher, Algebraic Topology, Theorem 3.11, pp.211–212. The lateral face
coefficients cancel against the boundary-prism terms. Adjacent diagonal faces
cancel, so their finite sum is signed reversal minus the identity. These
identities hold over every commutative ring, including characteristic two.
DAG node: `topo.singular_cochain_prism_cancellation_g14`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
variable (R : Type u) [CommRing R]

/-- The lower lateral face of the signed reversal prism has the opposite
coefficient from the same prism on the corresponding boundary face.
Source: Hatcher, Algebraic Topology, Theorem 3.11, pp.211–212. -/
theorem prism_before_sign (n : ℕ) (i j : Fin (n+2)) (hi : i ≠ 0) :
    (-1:R)^i.val * reversalSign R (n+1-i.val) * (-1:R)^j.val =
      -((-1:R)^j.val * (-1:R)^(i.pred hi).val *
        reversalSign R (n-(i.pred hi).val)) := by
  have hi0 : i.val ≠ 0 := by intro h; apply hi; exact Fin.ext h
  have hp : i.val = (i.pred hi).val + 1 := by rw [Fin.val_pred]; omega
  have he : n+1-i.val = n-(i.pred hi).val := by omega
  rw [he, hp, pow_succ]
  ring

/-- The upper lateral face has the opposite coefficient from its boundary prism.
Source: Hatcher, Algebraic Topology, Theorem 3.11, p.212. -/
theorem prism_after_sign (n : ℕ) (i j : Fin (n+2)) (hij : i.val < j.val) :
    (-1:R)^i.val * reversalSign R (n+1-i.val) * (-1:R)^(n+i.val+2-j.val) =
      -((-1:R)^j.val * (-1:R)^i.val * reversalSign R (n-i.val)) := by
  have he : n+1-i.val = (n-i.val)+1 := by omega
  rw [he, reversalSign_succ]
  have hp : (-1:R)^((n-i.val+1)+(n+i.val+2-j.val)) = (-1:R)^(j.val+1) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (R := R) (j.val+1)]
    congr 1
    omega
  calc
    _ = (-1:R)^i.val * reversalSign R (n-i.val) *
        (-1:R)^((n-i.val+1)+(n+i.val+2-j.val)) := by rw [pow_add]; ring
    _ = _ := by rw [hp, pow_succ]; ring

/-- The two adjacent interior prism faces have cancelling coefficients.
Source: Hatcher, Algebraic Topology, Theorem 3.11, p.212. -/
theorem prism_adjacent_sign (n : ℕ) (i : Fin n) :
    (-1:R)^i.succ.val * reversalSign R (n-i.succ.val) * (-1:R)^i.succ.val =
      -((-1:R)^i.val * reversalSign R (n-i.val) * (-1:R)^(n+1)) := by
  have he : n-i.val = (n-i.succ.val)+1 := by simp only [Fin.val_succ]; omega
  rw [he, reversalSign_succ]
  have hleft : (-1:R)^i.succ.val * (-1:R)^i.succ.val = 1 := by
    rw [← mul_pow]; simp
  have hright : (-1:R)^(i.val+(n-i.succ.val+1)+(n+1)) = -1 := by
    rw [neg_one_pow_eq_pow_mod_two]
    have hmod : (i.val+(n-i.succ.val+1)+(n+1)) % 2 = 1 := by
      simp only [Fin.val_succ]; omega
    rw [hmod]
    simp
  calc
    _ = reversalSign R (n-i.succ.val) *
        ((-1:R)^i.succ.val * (-1:R)^i.succ.val) := by ring
    _ = reversalSign R (n-i.succ.val) := by rw [hleft]; ring
    _ = -((-1:R)^(i.val+(n-i.succ.val+1)+(n+1)) *
        reversalSign R (n-i.succ.val)) := by rw [hright]; ring
    _ = _ := by simp only [pow_add]; ring

/-- Cancellation of a lower lateral face with its term in Pδ.
Source: Hatcher, Algebraic Topology, Theorem 3.11, p.212. -/
theorem prism_before_cancel (X : TopCat.{u}) (n : ℕ) (i j : Fin (n+2))
    (hi : i ≠ 0) (hji : j.val < i.val) (a : cochains R X (n+1))
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    (-1:R)^i.val * reversalSign R (n+1-i.val) * (-1:R)^j.val *
        simplexValue R X a ((TopCat.toSSet.obj X).δ j.castSucc
          (vertexRestrict X (prismVertices (n+1) i) σ)) +
      (-1:R)^j.val * (-1:R)^(i.pred hi).val * reversalSign R (n-(i.pred hi).val) *
        simplexValue R X a (vertexRestrict X (prismVertices n (i.pred hi))
          ((TopCat.toSSet.obj X).δ j σ)) = 0 := by
  rw [prismFaceBeforeValue R X n i j hi hji, prism_before_sign R n i j hi]
  ring

/-- Cancellation of an upper lateral face with its term in Pδ.
Source: Hatcher, Algebraic Topology, Theorem 3.11, p.212. -/
theorem prism_after_cancel (X : TopCat.{u}) (n : ℕ) (i j : Fin (n+2))
    (hij : i.val < j.val) (a : cochains R X (n+1))
    (σ : (TopCat.toSSet.obj X) _⦋n+1⦌) :
    (-1:R)^i.val * reversalSign R (n+1-i.val) * (-1:R)^(n+i.val+2-j.val) *
        simplexValue R X a ((TopCat.toSSet.obj X).δ
          (⟨n+i.val+2-j.val, by omega⟩ : Fin (n+3))
          (vertexRestrict X (prismVertices (n+1) i) σ)) +
      (-1:R)^j.val * (-1:R)^i.val * reversalSign R (n-i.val) *
        simplexValue R X a (vertexRestrict X (prismVertices n (i.castLT (by omega)))
          ((TopCat.toSSet.obj X).δ j σ)) = 0 := by
  rw [prismFaceAfterValue R X n i j hij, prism_after_sign R n i j hij]
  ring

/-- Cancellation of the adjacent interior faces of the prism.
Source: Hatcher, Algebraic Topology, Theorem 3.11, pp.211–212. -/
theorem prism_adjacent_cancel (X : TopCat.{u}) (n : ℕ) (i : Fin n)
    (a : cochains R X n) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (-1:R)^i.succ.val * reversalSign R (n-i.succ.val) * (-1:R)^i.succ.val *
        simplexValue R X a (vertexRestrict X
          (prismVertices n i.succ ∘ i.succ.castSucc.succAbove) σ) +
      (-1:R)^i.val * reversalSign R (n-i.val) * (-1:R)^(n+1) *
        simplexValue R X a (vertexRestrict X
          (prismVertices n i.castSucc ∘ (Fin.last (n+1)).succAbove) σ) = 0 := by
  rw [prismVertices_adjacent, prism_adjacent_sign]
  ring

/-- The diagonal prism faces telescope to signed reversal minus the identity.
Source: Hatcher, Algebraic Topology, Theorem 3.11, pp.211–212.
Split the lower-face sum at its first term and the upper-face sum at its last
term. Every remaining pair is an adjacent interior face and cancels. The first
face is vertex reversal with coefficient εₙ; the last is the identity with
coefficient −1. The argument includes degree zero, where both interior sums
are empty. -/
theorem prism_diagonal_sum (X : TopCat.{u}) (n : ℕ) (a : cochains R X n)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (∑ i : Fin (n+1), (-1:R)^i.val * reversalSign R (n-i.val) * (-1:R)^i.val *
        simplexValue R X a (vertexRestrict X
          (prismVertices n i ∘ i.castSucc.succAbove) σ)) +
      (∑ i : Fin (n+1), (-1:R)^i.val * reversalSign R (n-i.val) * (-1:R)^(n+1) *
        simplexValue R X a (vertexRestrict X
          (prismVertices n i ∘ (Fin.last (n+1)).succAbove) σ)) =
      simplexValue R X (reverseCochain R X n a) σ - simplexValue R X a σ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hcancel :
      (∑ i : Fin n, (-1:R)^i.succ.val * reversalSign R (n-i.succ.val) *
          (-1:R)^i.succ.val * simplexValue R X a (vertexRestrict X
            (prismVertices n i.succ ∘ i.succ.castSucc.succAbove) σ)) +
        (∑ i : Fin n, (-1:R)^i.val * reversalSign R (n-i.val) * (-1:R)^(n+1) *
          simplexValue R X a (vertexRestrict X
            (prismVertices n i.castSucc ∘ (Fin.last (n+1)).succAbove) σ)) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ prism_adjacent_cancel R X n i a σ
  have hid : vertexRestrict X (id : Fin (n+1) → Fin (n+1)) σ = σ := by
    simpa using vertexRestrict_face X (𝟙 ⦋n⦌) σ
  have hsign : (-1:R)^n * (-1:R)^(n+1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    simp
  simp only [Fin.val_zero, Nat.sub_zero, pow_zero, one_mul, mul_one,
    Fin.val_last, Nat.sub_self, prismVertices_last,
    Fin.val_castSucc, hid, reverseCochain_value] at *
  have hsign0 : reversalSign R 0 = 1 := by simp [reversalSign]
  rw [hsign0, mul_one, hsign]
  simp only [Fin.castSucc_zero, prismVertices_first]
  grind only

end HolomorphicAnosov.SingularCochain
