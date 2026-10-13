import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.HermitianDolbeaultSquareBound
import HolomorphicAnosov.Analysis.InnerProductSpace.JacobianSingularValues
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Determinant decompositions and bounds for pullbacks of bilinear forms relative to complex
hyperplanes and Hermitian metrics. (Zhang, eqs. (8)–(10), Lemma 4.3, eq. (29)) -/

open Module
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- The norm determinant is the product of the norm determinants of the subspace restriction and the
orthogonal quotient block. -/
theorem normDet_invariant_subspace
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (P : Submodule ℂ V) (Q : Submodule ℂ W)
    (L : V ≃L[ℂ] W) (hmap : P.map L.toLinearMap = Q) :
    L.toLinearMap.normDet =
      (L.toLinearEquiv.ofSubmodules P Q hmap).toLinearMap.normDet *
        ((Qᗮ.orthogonalProjectionOnto.comp L.toContinuousLinearMap).comp Pᗮ.subtypeL).toLinearMap.normDet := by
  classical
  let U := L.toLinearEquiv.ofSubmodules P Q hmap
  have hPQ : finrank ℂ P = finrank ℂ Q := U.finrank_eq
  have hPQ' : finrank ℂ Pᗮ = finrank ℂ Qᗮ := by
    have hp := P.finrank_add_finrank_orthogonal
    have hq := Q.finrank_add_finrank_orthogonal
    have hv := L.toLinearEquiv.finrank_eq
    omega
  let bp := stdOrthonormalBasis ℂ P
  let bq := (stdOrthonormalBasis ℂ Q).reindex (finCongr hPQ.symm)
  let bn := stdOrthonormalBasis ℂ Pᗮ
  let bm := (stdOrthonormalBasis ℂ Qᗮ).reindex (finCongr hPQ'.symm)
  let b := (bp.prod bn).map P.orthogonalDecomposition.symm
  let c := (bq.prod bm).map Q.orthogonalDecomposition.symm
  let N := (Qᗮ.orthogonalProjectionOnto.comp L.toContinuousLinearMap).comp Pᗮ.subtypeL
  have hb (i) : b (Sum.inl i) = (bp i : V) := by
    simp only [b, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply]
    change (bp i : V) + 0 = _
    exact add_zero _
  have hbn (i) : b (Sum.inr i) = (bn i : V) := by
    simp only [b, OrthonormalBasis.map_apply, OrthonormalBasis.prod_apply]
    change (0 : V) + (bn i : V) = _
    exact zero_add _
  have hc (v : W) (i) : c.repr v (Sum.inl i) = bq.repr (Q.orthogonalProjectionOnto v) i := by
    change bq.repr (Q.orthogonalDecomposition v).fst i = _
    rw [Submodule.fst_orthogonalDecomposition_apply]
  have hcn (v : W) (i) : c.repr v (Sum.inr i) = bm.repr (Qᗮ.orthogonalProjectionOnto v) i := by
    change bm.repr (Q.orthogonalDecomposition v).snd i = _
    rw [Submodule.snd_orthogonalDecomposition_apply]
  have hm : LinearMap.toMatrix b.toBasis c.toBasis L.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bp.toBasis bq.toBasis U.toLinearMap)
        (fun i j ↦ c.repr (L (bn j)) (Sum.inl i))
        0 (LinearMap.toMatrix bn.toBasis bm.toBasis N.toLinearMap) := by
    ext i j
    cases i <;> cases j
    · rename_i i j
      simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁]
      change c.repr (L (b (Sum.inl j))) (Sum.inl i) = bq.repr (U (bp j)) i
      rw [hb, hc]
      rw [show Q.orthogonalProjectionOnto (L (bp j)) = U (bp j) from
        Q.orthogonalProjectionOnto_mem_subspace_eq_self (U (bp j))]
    · simp [LinearMap.toMatrix_apply, hbn]
    · rename_i i j
      simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      change c.repr (L (b (Sum.inl j))) (Sum.inr i) = 0
      rw [hb, hcn]
      have hmem : L (bp j) ∈ Q := by rw [← hmap]; exact ⟨_, (bp j).property, rfl⟩
      rw [Q.orthogonalProjectionOnto_orthogonal_apply_eq_zero hmem, map_zero]
      rfl
    · simp [LinearMap.toMatrix_apply, hbn, hcn, N]
  rw [L.toLinearMap.normDet_eq_norm_det_toMatrix b c, hm,
    Matrix.det_fromBlocks_zero₂₁, norm_mul,
    U.toLinearMap.normDet_eq_norm_det_toMatrix bp bq,
    N.toLinearMap.normDet_eq_norm_det_toMatrix bn bm]

/-- The norm determinant of a linear map between complex lines equals its operator norm. -/
theorem normDet_eq_opNorm_of_finrank_one
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (hV : finrank ℂ V = 1) (hW : finrank ℂ W = 1)
    (L : V →L[ℂ] W) : L.toLinearMap.normDet = ‖L‖ := by
  let b := (stdOrthonormalBasis ℂ V).reindex (finCongr hV)
  let c := (stdOrthonormalBasis ℂ W).reindex (finCongr hW)
  have hb (v : V) : b.repr v 0 • b 0 = v := by
    simpa only [Fin.sum_univ_one] using b.sum_repr v
  have hc (v : W) : c.repr v 0 • c 0 = v := by
    simpa only [Fin.sum_univ_one] using c.sum_repr v
  have hbn (v : V) : ‖b.repr v 0‖ = ‖v‖ := by
    simpa only [norm_smul, b.norm_eq_one, mul_one] using congrArg norm (hb v)
  have hcn (v : W) : ‖c.repr v 0‖ = ‖v‖ := by
    simpa only [norm_smul, c.norm_eq_one, mul_one] using congrArg norm (hc v)
  have hdet : L.toLinearMap.normDet = ‖L (b 0)‖ := by
    rw [L.toLinearMap.normDet_eq_norm_det_toMatrix b c, Matrix.det_unique]
    simp only [LinearMap.toMatrix_apply]
    exact hcn (L (b 0))
  rw [hdet]
  apply le_antisymm
  · simpa only [b.norm_eq_one, mul_one] using L.le_opNorm (b 0)
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro v
    conv_lhs => rw [← hb v, map_smul, norm_smul]
    rw [hbn, mul_comm]

/-- The pullback of a bounded bilinear form vanishing on pairs of subspace vectors is bounded by the
product of the quotient and total operator norms. -/
theorem bilinear_pullback_le_quotient_operator
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] [Module ℝ W]
    (P : Submodule ℂ V) (Q : Submodule ℂ W) (L : V ≃L[ℂ] W)
    (hmap : P.map L.toLinearMap = Q)
    (R : W →ₗ[ℝ] W →ₗ[ℝ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ v w, ‖R v w‖ ≤ C * ‖v‖ * ‖w‖)
    (hzero : ∀ v ∈ Q, ∀ w ∈ Q, R v w = 0) (v w : V) :
    ‖R (L v) (L w)‖ ≤ 2 * C * ‖L.toContinuousLinearMap‖ *
      ‖(Qᗮ.orthogonalProjectionOnto.comp L.toContinuousLinearMap).comp Pᗮ.subtypeL‖ *
        ‖v‖ * ‖w‖ := by
  let N := (Qᗮ.orthogonalProjectionOnto.comp L.toContinuousLinearMap).comp Pᗮ.subtypeL
  have hnormal (t : V) : ‖Qᗮ.starProjection (L t)‖ ≤ ‖N‖ * ‖t‖ := by
    have hmem : L (P.starProjection t) ∈ Q := by
      rw [← hmap]
      exact ⟨_, P.starProjection_apply_mem t, rfl⟩
    have heq : Qᗮ.orthogonalProjectionOnto (L t) = N (Pᗮ.orthogonalProjectionOnto t) := by
      conv_lhs => rw [← P.starProjection_add_starProjection_orthogonal t]
      rw [map_add, map_add, Q.orthogonalProjectionOnto_orthogonal_apply_eq_zero hmem,
        zero_add]
      rfl
    change ‖Qᗮ.orthogonalProjectionOnto (L t)‖ ≤ _
    rw [heq]
    exact (N.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (Pᗮ.norm_orthogonalProjectionOnto_apply_le t) (norm_nonneg N))
  have heq : R (L v) (L w) =
      R (L v) (Qᗮ.starProjection (L w)) +
        R (Qᗮ.starProjection (L v)) (Q.starProjection (L w)) := by
    calc
      R (L v) (L w) = R (L v)
          (Q.starProjection (L w) + Qᗮ.starProjection (L w)) := by
        rw [Q.starProjection_add_starProjection_orthogonal]
      _ = R (L v) (Q.starProjection (L w)) + R (L v) (Qᗮ.starProjection (L w)) :=
        map_add _ _ _
      _ = _ := by
        conv_lhs => arg 1; arg 1; rw [← Q.starProjection_add_starProjection_orthogonal (L v)]
        rw [map_add, LinearMap.add_apply,
          hzero _ (Q.starProjection_apply_mem _) _ (Q.starProjection_apply_mem _), zero_add]
        exact add_comm _ _
  rw [heq]
  calc
    _ ≤ ‖R (L v) (Qᗮ.starProjection (L w))‖ +
        ‖R (Qᗮ.starProjection (L v)) (Q.starProjection (L w))‖ := norm_add_le _ _
    _ ≤ C * ‖L v‖ * ‖Qᗮ.starProjection (L w)‖ +
        C * ‖Qᗮ.starProjection (L v)‖ * ‖Q.starProjection (L w)‖ :=
      add_le_add (hR _ _) (hR _ _)
    _ ≤ C * (‖L.toContinuousLinearMap‖ * ‖v‖) * (‖N‖ * ‖w‖) +
        C * (‖N‖ * ‖v‖) * (‖L.toContinuousLinearMap‖ * ‖w‖) := by
      gcongr
      · exact L.toContinuousLinearMap.le_opNorm v
      · exact hnormal w
      · exact hnormal v
      · exact (Q.norm_starProjection_apply_le _).trans (L.toContinuousLinearMap.le_opNorm w)
    _ = _ := by ring

/-- The squared norm of a bilinear pullback vanishing on hyperplane pairs is bounded by a Jacobian
factor divided by a power of the hyperplane conorm. -/
theorem bilinear_pullback_conorm_bound
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] [Module ℝ W]
    (P : Submodule ℂ V) (Q : Submodule ℂ W) (L : V ≃L[ℂ] W)
    (hmap : P.map L.toLinearMap = Q) (r : ℕ) (hr : 0 < r)
    (hP : finrank ℂ P = r) (hQ : finrank ℂ Q = r)
    (hPnormal : finrank ℂ Pᗮ = 1) (hQnormal : finrank ℂ Qᗮ = 1)
    (R : W →ₗ[ℝ] W →ₗ[ℝ] ℂ) (C B μ : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hμ : 0 < μ)
    (hR : ∀ v w, ‖R v w‖ ≤ C * ‖v‖ * ‖w‖)
    (hzero : ∀ v ∈ Q, ∀ w ∈ Q, R v w = 0)
    (hfull : ‖L.toContinuousLinearMap‖ ≤
      B * ‖(L.toLinearEquiv.ofSubmodules P Q hmap).toContinuousLinearEquiv.toContinuousLinearMap‖)
    (hmin : μ ≤ sInf ((fun v : P ↦
      ‖(L.toLinearEquiv.ofSubmodules P Q hmap) v‖) '' {v : P | ‖v‖ = 1}))
    (v w : V) :
    ‖R (L v) (L w)‖ * μ ^ (r - 1) ≤
      2 * C * B * L.toLinearMap.normDet * ‖v‖ * ‖w‖ := by
  let U := (L.toLinearEquiv.ofSubmodules P Q hmap).toContinuousLinearEquiv
  let N := (Qᗮ.orthogonalProjectionOnto.comp L.toContinuousLinearMap).comp Pᗮ.subtypeL
  have hsing := jacobian_singular_values r hr hP hQ U
  have hdet : ‖U.toContinuousLinearMap‖ * μ ^ (r - 1) ≤ U.toLinearMap.normDet :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ.le hmin _) (norm_nonneg _)).trans
      hsing.2.2.2.1
  have hfactor : L.toLinearMap.normDet = U.toLinearMap.normDet * ‖N‖ := by
    rw [normDet_invariant_subspace P Q L hmap,
      normDet_eq_opNorm_of_finrank_one hPnormal hQnormal]
    rfl
  have hbound := bilinear_pullback_le_quotient_operator P Q L hmap R C hC hR hzero v w
  calc
    _ ≤ (2 * C * ‖L.toContinuousLinearMap‖ * ‖N‖ * ‖v‖ * ‖w‖) * μ ^ (r - 1) :=
      mul_le_mul_of_nonneg_right hbound (pow_nonneg hμ.le _)
    _ ≤ (2 * C * (B * ‖U.toContinuousLinearMap‖) * ‖N‖ * ‖v‖ * ‖w‖) *
        μ ^ (r - 1) := by gcongr
    _ = (2 * C * B * ‖N‖ * ‖v‖ * ‖w‖) *
        (‖U.toContinuousLinearMap‖ * μ ^ (r - 1)) := by ring
    _ ≤ (2 * C * B * ‖N‖ * ‖v‖ * ‖w‖) * U.toLinearMap.normDet := by gcongr
    _ = _ := by rw [hfactor]; ring

/-- The hyperplane bilinear pullback bound holds for norms specified by Hermitian inner-product
cores. -/
theorem core_bilinear_pullback_conorm_bound
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Module ℝ W]
    (hV : InnerProductSpace.Core ℂ V) (hW : InnerProductSpace.Core ℂ W)
    (P : Submodule ℂ V) (Q : Submodule ℂ W) (L : V ≃ₗ[ℂ] W)
    (hmap : P.map L.toLinearMap = Q) (d : ℕ) (hd : 2 ≤ d)
    (hVdim : finrank ℂ V = d) (hWdim : finrank ℂ W = d)
    (hPdim : finrank ℂ P = d - 1) (hQdim : finrank ℂ Q = d - 1)
    (R : W →ₗ[ℝ] W →ₗ[ℝ] ℂ) (C B μ : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hμ : 0 < μ)
    (hR : ∀ v w, ‖R v w‖ ≤
      C * HermitianFibreAlgebra.coreLength hW v * HermitianFibreAlgebra.coreLength hW w)
    (hzero : ∀ v ∈ Q, ∀ w ∈ Q, R v w = 0)
    (hfull : fibreNormOperator (HermitianFibreAlgebra.coreLength hV)
      (HermitianFibreAlgebra.coreLength hW) ⊤ L ≤
      B * fibreNormOperator (HermitianFibreAlgebra.coreLength hV)
        (HermitianFibreAlgebra.coreLength hW) P L)
    (hmin : μ ≤ fibreNormConorm (HermitianFibreAlgebra.coreLength hV)
      (HermitianFibreAlgebra.coreLength hW) P L) :
    ∃ (b : Basis (Fin d) ℂ V) (c : Basis (Fin d) ℂ W),
      (∀ i j, hV.inner (b j) (b i) = if i = j then 1 else 0) ∧
      (∀ i j, hW.inner (c j) (c i) = if i = j then 1 else 0) ∧
      ∀ v w, ‖R (L v) (L w)‖ * μ ^ (d - 2) ≤
        2 * C * B * ‖(LinearMap.toMatrix b c L.toLinearMap).det‖ *
          HermitianFibreAlgebra.coreLength hV v * HermitianFibreAlgebra.coreLength hV w := by
  let Le := L
  let Ue := Le.ofSubmodules P Q hmap
  let : InnerProductSpace.Core ℂ V := hV
  let : InnerProductSpace.Core ℂ W := hW
  let : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  let : InnerProductSpace ℂ W := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ W)
  let L' := Le.toContinuousLinearEquiv
  let U := Ue.toContinuousLinearEquiv
  let b := (stdOrthonormalBasis ℂ V).reindex (finCongr hVdim)
  let c := (stdOrthonormalBasis ℂ W).reindex (finCongr hWdim)
  have hnormalP : finrank ℂ Pᗮ = 1 := by
    have hh := P.finrank_add_finrank_orthogonal
    omega
  have hnormalQ : finrank ℂ Qᗮ = 1 := by
    have hh := Q.finrank_add_finrank_orthogonal
    omega
  have hUop : fibreNormOperator (norm : V → ℝ) (norm : W → ℝ) P L' =
      ‖U.toContinuousLinearMap‖ := by
    change fibreNormOperator (norm : V → ℝ) (norm : W → ℝ) P L'.toContinuousLinearMap = _
    rw [fibreNormOperator_eq_restricted_opNorm P L'.toContinuousLinearMap]
    apply le_antisymm
    · exact (L'.toContinuousLinearMap.comp P.subtypeL).opNorm_le_bound
        (norm_nonneg U.toContinuousLinearMap) (fun v ↦ U.toContinuousLinearMap.le_opNorm v)
    · exact U.toContinuousLinearMap.opNorm_le_bound
        (norm_nonneg (L'.toContinuousLinearMap.comp P.subtypeL))
        (fun v ↦ (L'.toContinuousLinearMap.comp P.subtypeL).le_opNorm v)
  have hLop : fibreNormOperator (norm : V → ℝ) (norm : W → ℝ) ⊤ L' =
      ‖L'.toContinuousLinearMap‖ := by
    change fibreNormOperator (norm : V → ℝ) (norm : W → ℝ) ⊤ L'.toContinuousLinearMap = _
    rw [fibreNormOperator_eq_restricted_opNorm ⊤ L'.toContinuousLinearMap]
    apply le_antisymm
    · exact (L'.toContinuousLinearMap.comp (⊤ : Submodule ℂ V).subtypeL).opNorm_le_bound
        (norm_nonneg L'.toContinuousLinearMap) (fun v ↦ L'.toContinuousLinearMap.le_opNorm v)
    · exact L'.toContinuousLinearMap.opNorm_le_bound
        (norm_nonneg (L'.toContinuousLinearMap.comp (⊤ : Submodule ℂ V).subtypeL))
        (fun v ↦ (L'.toContinuousLinearMap.comp (⊤ : Submodule ℂ V).subtypeL).le_opNorm ⟨v, trivial⟩)
  have hset : (fun v : P ↦ ‖U v‖) '' {v : P | ‖v‖ = 1} =
      {a : ℝ | ∃ v : V, v ∈ P ∧ ‖v‖ = 1 ∧ a = ‖L' v‖} := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, v.property, hv, rfl⟩
    · rintro ⟨v, hv, hn, rfl⟩
      exact ⟨⟨v, hv⟩, hn, rfl⟩
  have hfull' : ‖L'.toContinuousLinearMap‖ ≤ B * ‖U.toContinuousLinearMap‖ := by
    rw [← hLop, ← hUop]
    exact hfull
  have hmin' : μ ≤ sInf ((fun v : P ↦ ‖U v‖) '' {v : P | ‖v‖ = 1}) := by
    rw [hset]
    exact hmin
  refine ⟨b.toBasis, c.toBasis, ?_, ?_, ?_⟩
  · intro i j
    exact (b.inner_eq_ite j i).trans (by simp only [eq_comm])
  · intro i j
    exact (c.inner_eq_ite j i).trans (by simp only [eq_comm])
  · intro v w
    have hh := bilinear_pullback_conorm_bound P Q L' hmap (d - 1) (by omega)
      hPdim hQdim hnormalP hnormalQ R C B μ hC hB hμ hR hzero hfull' hmin' v w
    rw [L'.toLinearMap.normDet_eq_norm_det_toMatrix b c] at hh
    have he : d - 1 - 1 = d - 2 := by omega
    rw [he] at hh
    convert! hh using 1

end HolomorphicAnosov


