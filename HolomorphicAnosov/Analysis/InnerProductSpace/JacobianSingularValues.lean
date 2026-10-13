import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Hermitian Jacobians and extremal singular values

Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*, Lemma 4.3,
equations (27)--(29), printed pp.15--16. The determinant modulus between different
Hermitian spaces is their norm determinant, equivalently the modulus of the matrix
determinant in any two orthonormal bases. No arbitrary identification of the spaces
is used.
-/

namespace HolomorphicAnosov

open Module

universe u v

/-- The Hermitian determinant and singular-value estimate used in Zhang (29).

Source: Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*, Lemma 4.3,
equation (29), printed p.16, with the unitary-frame determinant convention in
(27), p.15. DAG node: `zhang.jacobian_singular_values`.

Proof: Write the singular-value decomposition of `U` in unitary frames. Its
positive singular values are nonincreasing, the first is the operator norm, and
the last is the infimum of `‖U v‖` over the unit sphere. The unit sphere is nonempty
because its complex dimension `r` is positive. Unitary frame changes have
 determinant of modulus one. Consequently the norm determinant is the product
of these singular values. Equivalently, realification repeats every complex
singular value twice, its real norm determinant is the square of the complex
determinant modulus, and taking the nonnegative square root gives the same
product. This is the product formula in the node's named Mathlib prerequisite;
Mathlib also supplies the product formula directly over the complex field.
Each of the last `r - 1` values is at least the smallest one, so the product is
at least the largest value times the smallest to the power `r - 1`. If the
conorm is at least one, this is at least the operator norm. The final equality
states that the intrinsic norm determinant agrees with the matrix determinant
modulus in every pair of orthonormal bases, including when `V` and `W` differ.
The proof below uses the spectral basis of `U†U` for the extremal values and
Mathlib's direct complex norm-determinant product formula.
-/
theorem jacobian_singular_values
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    (r : ℕ) (hr : 0 < r)
    (hV : finrank ℂ V = r) (hW : finrank ℂ W = r)
    (U : V ≃L[ℂ] W) :
    let s := U.toLinearMap.singularValues
    let m := sInf ((fun v : V ↦ ‖U v‖) '' {v : V | ‖v‖ = 1})
    ‖U.toContinuousLinearMap‖ = s 0 ∧
      m = s (r - 1) ∧
      U.toLinearMap.normDet = ∏ i ∈ Finset.range r, s i ∧
      ‖U.toContinuousLinearMap‖ * m ^ (r - 1) ≤ U.toLinearMap.normDet ∧
      (1 ≤ m → ‖U.toContinuousLinearMap‖ ≤ U.toLinearMap.normDet) ∧
      ∀ (bV : OrthonormalBasis (Fin r) ℂ V) (bW : OrthonormalBasis (Fin r) ℂ W),
        U.toLinearMap.normDet =
          ‖(U.toLinearMap.toMatrix bV.toBasis bW.toBasis).det‖ := by
  classical
  dsimp only
  let L := U.toLinearMap
  let s := L.singularValues
  let hA := L.isSymmetric_adjoint_comp_self
  let b := hA.eigenvectorBasis hV
  have hformula (x : V) :
      ‖U x‖ ^ 2 = ∑ i : Fin r, s i ^ 2 * ‖inner ℂ (b i) x‖ ^ 2 := by
    have hd (i : Fin r) :
        inner ℂ (b i) ((L.adjoint ∘ₗ L) x) =
          (s i ^ 2 : ℂ) * inner ℂ (b i) x := by
      have hh := hA.eigenvectorBasis_apply_self_apply hV x i
      simpa [b, OrthonormalBasis.repr_apply_apply, ← L.sq_singularValues_fin hV i, s] using hh
    calc
      ‖U x‖ ^ 2 = (inner ℂ x ((L.adjoint ∘ₗ L) x)).re := by
        rw [LinearMap.comp_apply, L.adjoint_inner_right]
        simp [L, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
      _ = (∑ i : Fin r, inner ℂ x (b i) *
          inner ℂ (b i) ((L.adjoint ∘ₗ L) x)).re :=
        congrArg Complex.re (b.sum_inner_mul_inner x _).symm
      _ = ∑ i : Fin r, s i ^ 2 * ‖inner ℂ (b i) x‖ ^ 2 := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hd, ← mul_assoc, mul_comm (inner ℂ x (b i)) (s i ^ 2 : ℂ), mul_assoc]
        have hre : (inner ℂ x (b i) * inner ℂ (b i) x).re =
            ‖inner ℂ (b i) x‖ ^ 2 := by
          calc
            _ = ‖inner ℂ x (b i) * inner ℂ (b i) x‖ :=
              inner_mul_symm_re_eq_norm (𝕜 := ℂ) x (b i)
            _ = ‖inner ℂ (b i) x‖ ^ 2 := by
              rw [norm_mul, ← inner_conj_symm x (b i), RCLike.norm_conj]
              ring
        rw [← Complex.ofReal_pow, Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
  have hbounds (x : V) : s (r - 1) * ‖x‖ ≤ ‖U x‖ ∧ ‖U x‖ ≤ s 0 * ‖x‖ := by
    have hh := b.sum_sq_norm_inner_right x
    have hlo : (s (r - 1) * ‖x‖) ^ 2 ≤ ‖U x‖ ^ 2 := by
      rw [mul_pow, ← hh, Finset.mul_sum, hformula]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (L.singularValues_nonneg _) (L.singularValues_antitone
        (show (i : ℕ) ≤ r - 1 by omega)) 2
    have hup : ‖U x‖ ^ 2 ≤ (s 0 * ‖x‖) ^ 2 := by
      rw [mul_pow, ← hh, Finset.mul_sum, hformula]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (L.singularValues_nonneg _) (L.singularValues_antitone
        (Nat.zero_le _)) 2
    exact ⟨le_of_sq_le_sq hlo (norm_nonneg _),
      le_of_sq_le_sq hup (mul_nonneg (L.singularValues_nonneg _) (norm_nonneg _))⟩
  have hattain (i : Fin r) : ‖U (b i)‖ = s i := by
    have hh : ‖U (b i)‖ ^ 2 = s i ^ 2 := by
      rw [hformula, Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [b.inner_eq_ite, hji]
      · simp
    exact le_antisymm (le_of_sq_le_sq hh.le (L.singularValues_nonneg _))
      (le_of_sq_le_sq hh.ge (norm_nonneg _))
  have hnorm : ‖U.toContinuousLinearMap‖ = s 0 := by
    apply le_antisymm
    · exact ContinuousLinearMap.opNorm_le_bound _ (L.singularValues_nonneg _) fun x ↦
        (hbounds x).2
    · have hh := U.toContinuousLinearMap.le_opNorm (b ⟨0, hr⟩)
      simpa [hattain, b.norm_eq_one] using hh
  have hm : sInf ((fun x : V ↦ ‖U x‖) '' {x : V | ‖x‖ = 1}) = s (r - 1) := by
    apply IsLeast.csInf_eq
    refine ⟨?_, ?_⟩
    · refine ⟨b ⟨r - 1, by omega⟩, b.norm_eq_one _, ?_⟩
      exact hattain _
    · rintro y ⟨x, hx, rfl⟩
      change ‖x‖ = 1 at hx
      simpa [hx] using (hbounds x).1
  have hp : L.normDet = ∏ i ∈ Finset.range r, s i := by
    simpa [hV, L, s] using L.normDet_eq_prod_singularValues
  have hineq : s 0 * s (r - 1) ^ (r - 1) ≤ L.normDet := by
    rw [hp]
    have he : r = (r - 1) + 1 := by omega
    conv_rhs => rw [he, Finset.prod_range_succ']
    rw [mul_comm (∏ k ∈ Finset.range (r - 1), s (k + 1)) (s 0)]
    apply mul_le_mul_of_nonneg_left _ (L.singularValues_nonneg 0)
    have hc : s (r - 1) ^ (r - 1) =
        ∏ i ∈ Finset.range (r - 1), s (r - 1) := by simp
    rw [hc]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact L.singularValues_nonneg _
    · intro i hi
      exact L.singularValues_antitone (show i + 1 ≤ r - 1 by
        have := Finset.mem_range.mp hi
        omega)
  refine ⟨hnorm, hm, hp, ?_, ?_, ?_⟩
  · simpa [hnorm, hm, L, s] using hineq
  · intro hm1
    rw [hnorm]
    have hpow : 1 ≤ s (r - 1) ^ (r - 1) := one_le_pow₀ (hm ▸ hm1)
    have hh := mul_le_mul_of_nonneg_left hpow (L.singularValues_nonneg 0)
    simpa using hh.trans hineq
  · intro bV bW
    exact L.normDet_eq_norm_det_toMatrix bV bW

end HolomorphicAnosov

