import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import HolomorphicAnosov.Topology.Franks.PositiveEigenvectorUniqueness

open Set Matrix
open scoped BigOperators Topology

namespace HolomorphicAnosov

/-- A strictly positive finite real matrix has a normalized positive eigenvector.
Source: Gantmacher, *Applications of the Theory of Matrices* (1959), Chapter III
§2, pp.66–68, compact extremum and strict residual improvement.

On the compact simplex maximize r subject to Ax≥rx and 0≤r≤M, where M is the
sum of the entries. Every feasible r is bounded by M by summing coordinates.
If w=Ax−rx is nonzero, strict positivity makes Aw positive. Thus for some δ>0,
A(Ax)≥(r+δ)Ax. Normalize Ax to the simplex to contradict maximality. Hence Ax=rx.
Positivity of Ax then forces r and every coordinate of x to be positive.
The feasible-pair maximum is the minimum-ratio argument in closed-set form. -/
theorem franks_positive_perron_eigenvector
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ x : Fin n → ℝ,
      (∀ i, 0 < x i) ∧ (∑ i, x i) = 1 ∧ A *ᵥ x = ρ • x := by
  classical
  let M := ∑ i, ∑ j, A i j
  let Δ : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
  have hM : 0 < M := Finset.sum_pos (fun i _ ↦
    Finset.sum_pos (fun j _ ↦ hA i j) Finset.univ_nonempty) Finset.univ_nonempty
  have hcoord {x : Fin n → ℝ} (hx : x ∈ Δ) (i : Fin n) : x i ≤ 1 := by
    rw [← hx.2]
    exact Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)
  have hΔcompact : IsCompact Δ := by
    apply (isCompact_Icc : IsCompact (Icc (0 : Fin n → ℝ) 1)).of_isClosed_subset
    · have hnonneg : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
        simp only [ofPred_forall]
        exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
      exact hnonneg.inter (isClosed_eq (by fun_prop) continuous_const)
    · intro x hx
      exact ⟨hx.1, fun i ↦ hcoord hx i⟩
  have hΔne : Δ.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty (Fin n)›
    refine ⟨Pi.single i 1, ?_, ?_⟩
    · intro j
      by_cases h : j = i <;> simp [h]
    · simp
  have hbound {x : Fin n → ℝ} (hx : x ∈ Δ) {r : ℝ}
      (hr : ∀ i, r * x i ≤ (A *ᵥ x) i) : r ≤ M := by
    calc
      r = ∑ i, r * x i := by rw [← Finset.mul_sum, hx.2, mul_one]
      _ ≤ ∑ i, (A *ᵥ x) i := Finset.sum_le_sum fun i _ ↦ hr i
      _ ≤ M := by
        apply Finset.sum_le_sum
        intro i _
        change ∑ j, A i j * x j ≤ ∑ j, A i j
        apply Finset.sum_le_sum
        intro j _
        exact (mul_le_mul_of_nonneg_left (hcoord hx j) (hA i j).le).trans_eq (mul_one _)
  have hmulpos {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
      (hne : ∃ j, 0 < x j) (i : Fin n) : 0 < (A *ᵥ x) i := by
    obtain ⟨j,hj⟩ := hne
    exact (mul_pos (hA i j) hj).trans_le (Finset.single_le_sum
      (fun k _ ↦ mul_nonneg (hA i k).le (hx k)) (Finset.mem_univ j))
  have hΔpos {x : Fin n → ℝ} (hx : x ∈ Δ) : ∃ j, 0 < x j := by
    by_contra! hn
    have hz : ∑ j, x j = 0 := Finset.sum_eq_zero fun j _ ↦ le_antisymm (hn j) (hx.1 j)
    linarith [hx.2]
  let S : Set ((Fin n → ℝ) × ℝ) :=
    {p | p.1 ∈ Δ ∧ p.2 ∈ Icc 0 M ∧ ∀ i, p.2 * p.1 i ≤ (A *ᵥ p.1) i}
  have hScompact : IsCompact S := by
    apply (hΔcompact.prod isCompact_Icc).of_isClosed_subset
    · have hineqclosed : IsClosed {p : (Fin n → ℝ) × ℝ |
          ∀ i, p.2 * p.1 i ≤ (A *ᵥ p.1) i} := by
        simp only [ofPred_forall]
        apply isClosed_iInter
        intro i
        apply isClosed_le
        · fun_prop
        · simp only [Matrix.mulVec, dotProduct]
          fun_prop
      have hbase := (hΔcompact.isClosed.preimage continuous_fst).inter
        ((isClosed_Icc : IsClosed (Icc 0 M)).preimage (show Continuous (Prod.snd : (Fin n → ℝ) × ℝ → ℝ)
          from continuous_snd))
      convert hbase.inter hineqclosed using 1
      ext p
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_preimage, and_assoc]
    · intro p hp
      exact ⟨hp.1,hp.2.1⟩
  have hSne : S.Nonempty := by
    obtain ⟨x,hx⟩ := hΔne
    refine ⟨(x,0),hx,⟨le_rfl,hM.le⟩,?_⟩
    intro i
    simpa only [zero_mul] using (hmulpos hx.1 (hΔpos hx) i).le
  obtain ⟨⟨x,r⟩,hx,hmax⟩ := hScompact.exists_isMaxOn hSne continuous_snd.continuousOn
  have hxΔ : x ∈ Δ := hx.1
  have hr : 0 ≤ r := hx.2.1.1
  have hineq : ∀ i, r * x i ≤ (A *ᵥ x) i := hx.2.2
  let w := A *ᵥ x - r • x
  have hw : ∀ i, 0 ≤ w i := fun i ↦ sub_nonneg.mpr (hineq i)
  have hwzero : w = 0 := by
    by_contra hwne
    have hwn : ∃ j, 0 < w j := by
      by_contra! hn
      apply hwne
      funext j
      exact le_antisymm (hn j) (hw j)
    let y := A *ᵥ x
    have hy : ∀ i, 0 < y i := hmulpos hxΔ.1 (hΔpos hxΔ)
    have hAw : ∀ i, 0 < (A *ᵥ w) i := hmulpos hw hwn
    obtain ⟨i₀,_,hmin⟩ := Finset.exists_min_image Finset.univ
      (fun i ↦ (A *ᵥ w) i / y i) Finset.univ_nonempty
    let δ := (A *ᵥ w) i₀ / y i₀
    have hδ : 0 < δ := div_pos (hAw i₀) (hy i₀)
    have hδle (i : Fin n) : δ * y i ≤ (A *ᵥ w) i :=
      (le_div_iff₀ (hy i)).mp (hmin i (Finset.mem_univ i))
    have hAw_eq : A *ᵥ w = A *ᵥ y - r • y := by
      dsimp [w,y]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    have himprove (i : Fin n) : (r + δ) * y i ≤ (A *ᵥ y) i := by
      have hh := hδle i
      rw [hAw_eq] at hh
      change δ * y i ≤ (A *ᵥ y) i - r * y i at hh
      nlinarith
    let s := ∑ i, y i
    have hs : 0 < s := Finset.sum_pos (fun i _ ↦ hy i) Finset.univ_nonempty
    let z := s⁻¹ • y
    have hzΔ : z ∈ Δ := by
      constructor
      · intro i
        exact mul_nonneg (inv_nonneg.mpr hs.le) (hy i).le
      · change ∑ i, s⁻¹ * y i = 1
        rw [← Finset.mul_sum]
        exact inv_mul_cancel₀ (ne_of_gt hs)
    have hzineq (i : Fin n) : (r + δ) * z i ≤ (A *ᵥ z) i := by
      change (r + δ) * (s⁻¹ * y i) ≤ (A *ᵥ (s⁻¹ • y)) i
      rw [Matrix.mulVec_smul]
      change (r + δ) * (s⁻¹ * y i) ≤ s⁻¹ * (A *ᵥ y) i
      calc
        _ = s⁻¹ * ((r + δ) * y i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (himprove i) (inv_nonneg.mpr hs.le)
    have hzS : (z,r+δ) ∈ S := ⟨hzΔ,⟨by positivity,hbound hzΔ hzineq⟩,hzineq⟩
    have hh : r + δ ≤ r := hmax hzS
    linarith
  have heq : A *ᵥ x = r • x := sub_eq_zero.mp hwzero
  have hAxpos := hmulpos hxΔ.1 (hΔpos hxΔ)
  have hrpos : 0 < r := by
    obtain ⟨i⟩ := ‹Nonempty (Fin n)›
    have hi := hAxpos i
    rw [heq] at hi
    exact (mul_pos_iff.mp hi).resolve_right (fun hh ↦ (not_lt_of_ge hr hh.1)) |>.1
  refine ⟨r,hrpos,x,?_,hxΔ.2,heq⟩
  intro i
  have hi := hAxpos i
  rw [heq] at hi
  exact (mul_pos_iff.mp hi).resolve_right (fun hh ↦ (not_lt_of_gt hrpos hh.1)) |>.2

/-- A nonnegative matrix with a strictly positive positive power has a positive
eigenvector. Gantmacher, Chapter III, Theorem 8, pp.97–98.
Apply the positive-matrix existence theorem to A^k. Commutation makes Ax a
second eigenvector of A^k with the same eigenvalue, so positive eigendirection
uniqueness gives Ax=ρx. Nonnegativity and A^k x≠0 force ρ>0. -/
theorem franks_primitive_perron_eigenvector
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (hk : 0 < k)
    (hAk : ∀ i j, 0 < (A ^ k) i j) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ x : Fin n → ℝ,
      (∀ i, 0 < x i) ∧ (∑ i, x i) = 1 ∧ A *ᵥ x = ρ • x := by
  obtain ⟨r,hr,x,hx,hsum,hpow⟩ := franks_positive_perron_eigenvector (A ^ k) hAk
  have hcomm : A ^ k *ᵥ (A *ᵥ x) = r • (A *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, ← pow_succ, pow_succ', ← Matrix.mulVec_mulVec,
      hpow, Matrix.mulVec_smul]
  obtain ⟨ρ,hρ⟩ := franks_manning_positive_eigenvector_unique
    (A ^ k) hAk x (A *ᵥ x) hx r hpow hcomm
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  have hnonneg : 0 ≤ ρ := by
    have hp : 0 ≤ (A *ᵥ x) i := by
      exact Finset.sum_nonneg (s := Finset.univ) fun j _ ↦ mul_nonneg (hA i j) (hx j).le
    rw [hρ] at hp
    exact nonneg_of_mul_nonneg_left hp (hx i)
  have hne : ρ ≠ 0 := by
    intro he
    have hz : A *ᵥ x = 0 := by simpa only [he, zero_smul] using hρ
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hzpow : A ^ (l+1) *ᵥ x = 0 := by
      rw [pow_succ, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    have hh : r * x i = 0 := by
      have := congrFun (hpow.symm.trans hzpow) i
      exact this
    exact (ne_of_gt (mul_pos hr (hx i))) hh
  exact ⟨ρ,lt_of_le_of_ne hnonneg (Ne.symm hne),x,hx,hsum,hρ⟩

/-- An irreducible nonnegative matrix has a normalized strictly positive
Perron eigenvector. Sum finitely many positive connecting powers to get a
strictly positive matrix commuting with A, then use positive eigendirection
uniqueness. A positive diagonal connecting power rules out eigenvalue zero. -/
theorem franks_irreducible_perron_eigenvector
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ x : Fin n → ℝ,
      (∀ i, 0 < x i) ∧ (∑ i, x i) = 1 ∧ A *ᵥ x = ρ • x := by
  classical
  have hc := (Matrix.isIrreducible_iff_exists_pow_pos hA).mp hirr
  choose k hk hkpos using hc
  let B : Matrix (Fin n) (Fin n) ℝ := ∑ p : Fin n × Fin n, A^(k p.1 p.2)
  have hB (i j) : 0 < B i j := by
    change 0 < (∑ p : Fin n × Fin n, A^(k p.1 p.2)) i j
    simp only [Matrix.sum_apply]
    exact (hkpos i j).trans_le (Finset.single_le_sum
      (fun (p : Fin n × Fin n) _ ↦ Matrix.pow_apply_nonneg hA (k p.1 p.2) i j) (Finset.mem_univ (i,j)))
  obtain ⟨r,hr,x,hx,hsum,hBx⟩ := franks_positive_perron_eigenvector B hB
  have hBA : B*A=A*B := by
    dsimp [B]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact pow_mul_comm' A _
  have hcomm : B *ᵥ (A *ᵥ x) = r • (A *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, hBA, ← Matrix.mulVec_mulVec, hBx, Matrix.mulVec_smul]
  obtain ⟨ρ,hρ⟩ := franks_manning_positive_eigenvector_unique B hB x (A *ᵥ x) hx r hBx hcomm
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  have hnonneg : 0 ≤ ρ := by
    have hp : 0 ≤ (A *ᵥ x) i :=
      Finset.sum_nonneg (s := Finset.univ) fun j _ ↦ mul_nonneg (hA i j) (hx j).le
    rw [hρ] at hp
    exact nonneg_of_mul_nonneg_left hp (hx i)
  have hne : ρ ≠ 0 := by
    intro he
    have hz : A *ᵥ x = 0 := by simpa only [he, zero_smul] using hρ
    obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hk i i))
    have hzpow : A ^ (k i i) *ᵥ x = 0 := by
      rw [hl, pow_succ, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    have hpos : 0 < (A^(k i i) *ᵥ x) i :=
      (mul_pos (hkpos i i) (hx i)).trans_le (Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (Matrix.pow_apply_nonneg hA (k i i) i j) (hx j).le) (Finset.mem_univ i))
    simp only [hzpow, Pi.zero_apply, lt_self_iff_false] at hpos
  exact ⟨ρ,lt_of_le_of_ne hnonneg (Ne.symm hne),x,hx,hsum,hρ⟩

/-- A positive stochastic matrix strictly contracts vectors of zero stationary
mean in the sup norm. This is the elementary averaging form of the positive
matrix spectral-gap argument in Gantmacher (1959), Chapter III, pp.68–73.
Choose δ>0 with P_ij≥δπ_j for all i,j. Summing a row gives δ≤1. On vectors with
π·v=0, subtract δ times the mean from each row. The remaining nonnegative
weights sum to 1−δ, so the triangle inequality gives the strict contraction. -/
theorem positive_stochastic_contraction
    {n : ℕ} [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 < P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (π : Fin n → ℝ) (hπ : ∀ j, 0 < π j) (hsum : ∑ j, π j = 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ v : Fin n → ℝ, (∑ j, π j * v j) = 0 → ‖P *ᵥ v‖ ≤ c * ‖v‖ := by
  classical
  obtain ⟨p,_,hmin⟩ := Finset.exists_min_image Finset.univ
    (fun p : Fin n × Fin n ↦ P p.1 p.2 / π p.2) Finset.univ_nonempty
  let δ := P p.1 p.2 / π p.2
  have hδ : 0 < δ := div_pos (hP _ _) (hπ _)
  have hentry (i j : Fin n) : δ * π j ≤ P i j :=
    (le_div_iff₀ (hπ j)).mp (hmin (i,j) (Finset.mem_univ _))
  have hδone : δ ≤ 1 := by
    calc
      δ = ∑ j, δ * π j := by rw [← Finset.mul_sum, hsum, mul_one]
      _ ≤ ∑ j, P p.1 j := Finset.sum_le_sum fun j _ ↦ hentry _ _
      _ = 1 := hrow _
  refine ⟨1-δ,sub_nonneg.mpr hδone,by linarith,?_⟩
  intro v hv
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (sub_nonneg.mpr hδone) (norm_nonneg v))).mpr
  intro i
  have hrewrite : (P *ᵥ v) i = ∑ j, (P i j - δ * π j) * v j := by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hv, mul_zero,
      sub_zero, Matrix.mulVec, dotProduct]
  rw [hrewrite]
  calc
    ‖∑ j, (P i j - δ * π j) * v j‖ ≤ ∑ j, ‖(P i j - δ * π j) * v j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, (P i j - δ * π j) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hentry i j))]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (sub_nonneg.mpr (hentry i j))
    _ = (1-δ) * ‖v‖ := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hrow, ← Finset.mul_sum, hsum, mul_one]

/-- Every stochastic matrix is nonexpanding in the sup norm, since each row is a
convex average. Used between positive-power contraction times. -/
theorem stochastic_norm_le
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n)) (v : Fin n → ℝ) : ‖P *ᵥ v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  change ‖∑ j, P i j * v j‖ ≤ ‖v‖
  calc
    ‖∑ j, P i j * v j‖ ≤ ∑ j, ‖P i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, P i j * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hP.1 i j)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (hP.1 i j)
    _ = ‖v‖ := by rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP, one_mul]

/-- Powers of a primitive stochastic matrix send each zero stationary-mean
vector to zero. Apply the strict contraction at multiples of a positive power;
all intervening powers are nonexpanding. -/
theorem primitive_stochastic_zero_mean_limit
    {n : ℕ} [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n)) (k : ℕ) (_hk : 0 < k)
    (hPk : ∀ i j, 0 < (P ^ k) i j)
    (π : Fin n → ℝ) (hπ : ∀ j, 0 < π j) (hsum : ∑ j, π j = 1)
    (hstat : π ᵥ* P = π) (v : Fin n → ℝ) (hv : π ⬝ᵥ v = 0) :
    Filter.Tendsto (fun m : ℕ ↦ P ^ m *ᵥ v) Filter.atTop (𝓝 0) := by
  have hPpow (m : ℕ) : P ^ m ∈ Matrix.rowStochastic ℝ (Fin n) :=
    (Matrix.rowStochastic ℝ (Fin n)).pow_mem hP m
  have hstatpow (m : ℕ) : π ᵥ* P ^ m = π := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hstat]
  have hmean (m : ℕ) : π ⬝ᵥ (P ^ m *ᵥ v) = 0 := by
    rw [Matrix.dotProduct_mulVec, hstatpow, hv]
  obtain ⟨c,hc,hc1,hcontract⟩ := positive_stochastic_contraction
    (P ^ k) hPk (Matrix.sum_row_of_mem_rowStochastic (hPpow k)) π hπ hsum
  have hblock (N : ℕ) : ‖P ^ (k * N) *ᵥ v‖ ≤ c ^ N * ‖v‖ := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Nat.mul_succ, Nat.add_comm (k*N) k, pow_add]
      rw [← Matrix.mulVec_mulVec]
      calc
        _ ≤ c * ‖P ^ (k*N) *ᵥ v‖ := hcontract _ (hmean _)
        _ ≤ c * (c ^ N * ‖v‖) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (N+1) * ‖v‖ := by rw [pow_succ]; ring
  have hlim : Filter.Tendsto (fun N : ℕ ↦ c ^ N * ‖v‖)
      Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).mul_const ‖v‖
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  refine ⟨k*N,?_⟩
  intro m hm
  have hdecomp : m = (m-k*N) + k*N := (Nat.sub_add_cancel hm).symm
  rw [dist_zero_right, hdecomp, pow_add, ← Matrix.mulVec_mulVec]
  exact ((stochastic_norm_le _ (hPpow _) _).trans (hblock N)).trans_lt
    (lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using hN N le_rfl))

/-- The trace of the powers of a primitive stochastic matrix tends to one.
Subtract from each coordinate basis vector its constant stationary average.
The resulting mean-zero vector tends to zero, so the j-th diagonal entry tends
to π_j. Summing finitely many diagonal limits gives sum π_j=1. -/
theorem primitive_stochastic_trace_limit
    {n : ℕ} [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n)) (k : ℕ) (hk : 0 < k)
    (hPk : ∀ i j, 0 < (P ^ k) i j)
    (π : Fin n → ℝ) (hπ : ∀ j, 0 < π j) (hsum : ∑ j, π j = 1)
    (hstat : π ᵥ* P = π) :
    Filter.Tendsto (fun m : ℕ ↦ Matrix.trace (P ^ m)) Filter.atTop (𝓝 1) := by
  classical
  have hdiag (j : Fin n) : Filter.Tendsto (fun m : ℕ ↦ (P ^ m) j j)
      Filter.atTop (𝓝 (π j)) := by
    let v : Fin n → ℝ := Pi.single j 1 - π j • (1 : Fin n → ℝ)
    have hv : π ⬝ᵥ v = 0 := by
      simp only [v, dotProduct, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
        mul_one, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj
        simp [Pi.single_eq_of_ne hbj]
      · simp
    have hh := primitive_stochastic_zero_mean_limit P hP k hk hPk π hπ hsum hstat v hv
    have hhj := (continuous_apply j).tendsto 0 |>.comp hh
    have hcoord (m : ℕ) : (P ^ m *ᵥ v) j = (P ^ m) j j - π j := by
      have hp := (Matrix.rowStochastic ℝ (Fin n)).pow_mem hP m
      dsimp only [v]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hp.2]
      simp
    simp only [Function.comp_def, hcoord, Pi.zero_apply] at hhj
    simpa only [sub_add_cancel, zero_add] using hhj.add_const (π j)
  simpa only [Matrix.trace, Matrix.diag, hsum] using
    tendsto_finsetSum Finset.univ (fun j _ ↦ hdiag j)


/-- Normalized traces of a primitive matrix tend to one. Gantmacher Chapter III,
pp.66–75 and pp.97–98. Positive left and right eigenvectors have the same eigenvalue
by pairing. Divide by that eigenvalue and conjugate by the positive right coordinates.
The resulting stochastic matrix has stationary probability proportional to the product
of left and right coordinates. Its trace limit is one by the preceding contraction proof,
and conjugation preserves the normalized trace at every power. -/
theorem positive_eigenvector_normalized_trace_limit
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (hk : 0 < k)
    (hAk : ∀ i j, 0 < (A ^ k) i j)
    (ρ : ℝ) (hρ : 0 < ρ) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hAx : A *ᵥ x = ρ • x) :
    Filter.Tendsto (fun m : ℕ ↦ Matrix.trace (A ^ m) / ρ ^ m)
      Filter.atTop (𝓝 1) := by
  classical
  obtain ⟨σ,hσ,z,hz,_,hAz⟩ := franks_primitive_perron_eigenvector A.transpose
    (fun i j ↦ hA j i) k hk (by
      rw [← Matrix.transpose_pow]
      exact fun i j ↦ hAk j i)
  have hleft : z ᵥ* A = σ • z := by
    rw [← Matrix.mulVec_transpose]
    exact hAz
  let s := ∑ i, z i * x i
  have hs : 0 < s := Finset.sum_pos (fun i _ ↦ mul_pos (hz i) (hx i)) Finset.univ_nonempty
  have hρσ : ρ = σ := by
    have he := Matrix.dotProduct_mulVec z A x
    rw [hAx,hleft,dotProduct_smul,smul_dotProduct] at he
    change ρ * s = σ * s at he
    exact mul_right_cancel₀ (ne_of_gt hs) he
  rw [← hρσ] at hleft
  let P : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ A i j * x j / (ρ * x i)
  have hPnonneg (i j : Fin n) : 0 ≤ P i j :=
    div_nonneg (mul_nonneg (hA i j) (hx j).le) (mul_pos hρ (hx i)).le
  have hPsum (i : Fin n) : ∑ j, P i j = 1 := by
    change ∑ j, A i j * x j / (ρ * x i) = 1
    rw [← Finset.sum_div]
    change (A *ᵥ x) i / (ρ * x i) = 1
    rw [hAx]
    exact div_self (ne_of_gt (mul_pos hρ (hx i)))
  have hP : P ∈ Matrix.rowStochastic ℝ (Fin n) :=
    Matrix.mem_rowStochastic_iff_sum.mpr ⟨hPnonneg,hPsum⟩
  have hPpow (m : ℕ) : ∀ i j : Fin n,
      (P ^ m) i j = (A ^ m) i j * x j / (ρ ^ m * x i) := by
    induction m with
    | zero =>
      intro i j
      by_cases hij : i = j
      · subst j
        simp [ne_of_gt (hx i)]
      · simp [hij]
    | succ m ih =>
      intro i j
      rw [pow_succ,pow_succ,Matrix.mul_apply,Matrix.mul_apply]
      simp_rw [ih]
      change ∑ l, ((A ^ m) i l * x l / (ρ ^ m * x i)) *
        (A l j * x j / (ρ * x l)) = (∑ l, (A ^ m) i l * A l j) * x j / (ρ ^ (m+1) * x i)
      rw [Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l _
      rw [pow_succ]
      field_simp [ne_of_gt (hx l), ne_of_gt hρ]
  have hPk (i j : Fin n) : 0 < (P ^ k) i j := by
    rw [hPpow]
    exact div_pos (mul_pos (hAk i j) (hx j)) (mul_pos (pow_pos hρ k) (hx i))
  let π : Fin n → ℝ := fun i ↦ z i * x i / s
  have hπ (i : Fin n) : 0 < π i := div_pos (mul_pos (hz i) (hx i)) hs
  have hπsum : ∑ i, π i = 1 := by
    change ∑ i, z i * x i / s = 1
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hs)
  have hπstat : π ᵥ* P = π := by
    funext j
    change (∑ i, (z i * x i / s) * (A i j * x j / (ρ * x i))) = z j * x j / s
    calc
      _ = ∑ i, z i * A i j * x j / (s * ρ) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [ne_of_gt (hx i), ne_of_gt hρ]
      _ = (z ᵥ* A) j * x j / (s * ρ) := by
        simp only [Matrix.vecMul,dotProduct,Finset.sum_mul,Finset.sum_div]
      _ = z j * x j / s := by
        rw [hleft]
        change (ρ * z j) * x j / (s * ρ) = _
        field_simp
  have htrace (m : ℕ) : Matrix.trace (P ^ m) = Matrix.trace (A ^ m) / ρ ^ m := by
    simp only [Matrix.trace,Matrix.diag,hPpow,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt (hx i), ne_of_gt hρ]
  simpa only [htrace] using primitive_stochastic_trace_limit P hP k hk hPk π hπ hπsum hπstat

/-- Primitive Perron existence together with the normalized principal trace limit. -/
theorem franks_primitive_normalized_trace_limit
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (hk : 0 < k)
    (hAk : ∀ i j, 0 < (A ^ k) i j) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Filter.Tendsto (fun m : ℕ ↦ Matrix.trace (A ^ m) / ρ ^ m)
        Filter.atTop (𝓝 1) := by
  obtain ⟨ρ,hρ,x,hx,_,hAx⟩ := franks_primitive_perron_eigenvector A hA k hk hAk
  exact ⟨ρ,hρ,positive_eigenvector_normalized_trace_limit A hA k hk hAk ρ hρ x hx hAx⟩

/-- A positive eigenvector gives two-sided exponential bounds on the sum of
entries of a nonnegative matrix power. The logarithmic growth rate is the
logarithm of its eigenvalue. This is the weighted row-sum proof behind the
primitive word-growth normalization in Gantmacher Chapter III and Walkden,
MAGIC010 Lecture 8, Proposition 8.17 pp.15–16.

Normalize the eigenvector sum to one. Its minimum a>0 and maximum b>0 bound
all its coordinates. Weighting the nonnegative entries of A^m by these
coordinates gives exactly ρ^m. Thus ρ^m/b ≤ sum(A^m) ≤ ρ^m/a. Take logarithms,
divide by m>0, and squeeze between logρ−logb/m and logρ−loga/m. -/
theorem positive_eigenvector_entry_growth
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (ρ : ℝ) (hρ : 0 < ρ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1)
    (hAx : A *ᵥ x = ρ • x) :
    Filter.Tendsto (fun m : ℕ ↦ Real.log (∑ i, ∑ j, (A ^ m) i j) / m)
      Filter.atTop (𝓝 (Real.log ρ)) := by
  classical
  obtain ⟨imin,_,hmin⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  obtain ⟨imax,_,hmax⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have hnonneg (m : ℕ) : ∀ i j, 0 ≤ (A ^ m) i j := by
    induction m with
    | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
    | succ m ih =>
      intro i j
      rw [pow_succ,Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (ih i l) (hA l j)
  have heig (m : ℕ) : A ^ m *ᵥ x = ρ ^ m • x := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec,hAx,Matrix.mulVec_smul,ih,pow_succ]
      ext i
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
  have hweighted (m : ℕ) : ∑ i, ∑ j, (A ^ m) i j * x j = ρ ^ m := by
    change ∑ i, (A ^ m *ᵥ x) i = ρ ^ m
    rw [heig]
    change ∑ i, ρ ^ m * x i = ρ ^ m
    rw [← Finset.mul_sum,hsum,mul_one]
  have hlow (m : ℕ) : ρ ^ m / x imax ≤ ∑ i, ∑ j, (A ^ m) i j := by
    apply (div_le_iff₀ (hx imax)).mpr
    rw [← hweighted m, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hnonneg m i j)
  have hupp (m : ℕ) : (∑ i, ∑ j, (A ^ m) i j) ≤ ρ ^ m / x imin := by
    apply (le_div_iff₀ (hx imin)).mpr
    rw [← hweighted m,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ j)) (hnonneg m i j)
  have hlower := (tendsto_const_nhds (x := Real.log ρ)).sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log (x imax)))
  have hupper := (tendsto_const_nhds (x := Real.log ρ)).sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log (x imin)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlower) (by simpa using hupper)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    have hh := div_le_div_of_nonneg_right
      (Real.log_le_log (div_pos (pow_pos hρ m) (hx imax)) (hlow m)) (Nat.cast_nonneg m)
    rw [Real.log_div (ne_of_gt (pow_pos hρ m)) (ne_of_gt (hx imax)),Real.log_pow] at hh
    convert hh using 1; field_simp
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    have hpos := (div_pos (pow_pos hρ m) (hx imax)).trans_le (hlow m)
    have hh := div_le_div_of_nonneg_right (Real.log_le_log hpos (hupp m)) (Nat.cast_nonneg m)
    rw [Real.log_div (ne_of_gt (pow_pos hρ m)) (ne_of_gt (hx imin)),Real.log_pow] at hh
    convert hh using 1; field_simp

/-- A nonnegative matrix with row sums bounded by c has sup operator norm at
most c. The entrywise triangle inequality proves the bound directly. -/
theorem nonnegative_matrix_norm_le_rows
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (c : ℝ) (hc : 0 ≤ c) (hrow : ∀ i, ∑ j, P i j ≤ c) (v : Fin n → ℝ) :
    ‖P *ᵥ v‖ ≤ c * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg v))).mpr
  intro i
  change ‖∑ j, P i j * v j‖ ≤ c * ‖v‖
  calc
    _ ≤ ∑ j, ‖P i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, P i j * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hP i j)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (hP i j)
    _ ≤ c * ‖v‖ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg v)

/-- A substochastic matrix whose one positive power loses mass in every row has
powers tending to zero. Take the maximum deficient row sum c<1; its block powers
contract by c^N, and every intervening power remains nonexpanding. This is the
finite-matrix forbidden-transition estimate behind Manning's boundary gap. -/
theorem substochastic_power_decay
    {n : ℕ} [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (k : ℕ) (_hk : 0 < k) (hdefect : ∀ i, ∑ j, (P^k) i j < 1)
    (v : Fin n → ℝ) :
    Filter.Tendsto (fun m : ℕ ↦ P^m *ᵥ v) Filter.atTop (𝓝 0) := by
  have hpnonneg (m : ℕ) : ∀ i j, 0 ≤ (P^m) i j := by
    induction m with
    | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
    | succ m ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (ih i l) (hP l j)
  have hnonexp (m : ℕ) (w : Fin n → ℝ) : ‖P^m *ᵥ w‖ ≤ ‖w‖ := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      have hh := nonnegative_matrix_norm_le_rows P hP 1 zero_le_one hrow (P^m *ᵥ w)
      rw [one_mul] at hh
      exact hh.trans ih
  classical
  obtain ⟨i₀,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i ↦ ∑ j, (P^k) i j) Finset.univ_nonempty
  let c := ∑ j, (P^k) i₀ j
  have hc : 0 ≤ c := Finset.sum_nonneg fun j _ ↦ hpnonneg k i₀ j
  have hc1 : c < 1 := hdefect i₀
  have hcontract (w : Fin n → ℝ) : ‖P^k *ᵥ w‖ ≤ c * ‖w‖ :=
    nonnegative_matrix_norm_le_rows _ (hpnonneg k) c hc
      (fun i ↦ hmax i (Finset.mem_univ i)) w
  have hblock (N : ℕ) : ‖P^(k*N) *ᵥ v‖ ≤ c^N * ‖v‖ := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Nat.mul_succ, Nat.add_comm (k*N) k, pow_add, ← Matrix.mulVec_mulVec]
      calc
        _ ≤ c * ‖P^(k*N) *ᵥ v‖ := hcontract _
        _ ≤ c * (c^N * ‖v‖) := mul_le_mul_of_nonneg_left ih hc
        _ = c^(N+1) * ‖v‖ := by rw [pow_succ]; ring
  have hlim : Filter.Tendsto (fun N : ℕ ↦ c^N * ‖v‖) Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).mul_const ‖v‖
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  refine ⟨k*N,?_⟩
  intro m hm
  have hdecomp : m = (m-k*N) + k*N := (Nat.sub_add_cancel hm).symm
  rw [dist_zero_right, hdecomp, pow_add, ← Matrix.mulVec_mulVec]
  exact ((hnonexp _ _).trans (hblock N)).trans_lt
    (lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using hN N le_rfl))

/-- Removing at least one positive transition from a primitive stochastic matrix
makes every power tend to zero. After k steps all rows see the missing mass;
comparison with P^k makes Q^(k+1) strictly substochastic in every row. -/
theorem proper_substochastic_power_decay
    {n : ℕ} [Nonempty (Fin n)] (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin n))
    (hQ : ∀ i j, 0 ≤ Q i j) (hQP : ∀ i j, Q i j ≤ P i j)
    (k : ℕ) (hk : 0 < k) (hPk : ∀ i j, 0 < (P^k) i j)
    (a b : Fin n) (hab : Q a b < P a b) (v : Fin n → ℝ) :
    Filter.Tendsto (fun m : ℕ ↦ Q^m *ᵥ v) Filter.atTop (𝓝 0) := by
  have hQrow (i : Fin n) : ∑ j, Q i j ≤ 1 := by
    rw [← Matrix.sum_row_of_mem_rowStochastic hP i]
    exact Finset.sum_le_sum fun j _ ↦ hQP i j
  have hQa : ∑ j, Q a j < 1 := by
    rw [← Matrix.sum_row_of_mem_rowStochastic hP a]
    exact Finset.sum_lt_sum (fun j _ ↦ hQP a j) ⟨b, Finset.mem_univ b, hab⟩
  have hpowP (m : ℕ) : P^m ∈ Matrix.rowStochastic ℝ (Fin n) :=
    (Matrix.rowStochastic ℝ (Fin n)).pow_mem hP m
  have hpowQ (m : ℕ) : ∀ i j, 0 ≤ (Q^m) i j := by
    induction m with
    | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
    | succ m ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (ih i l) (hQ l j)
  have hpowle (m : ℕ) : ∀ i j, (Q^m) i j ≤ (P^m) i j := by
    induction m with
    | zero => intro i j; rfl
    | succ m ih =>
      intro i j
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_le_sum fun l _ ↦
        mul_le_mul (ih i l) (hQP l j) (hQ l j) ((hpowP m).1 i l)
  apply substochastic_power_decay Q hQ hQrow (k+1) (by omega) _ v
  intro i
  have hsum : ∑ j, (Q^(k+1)) i j = ∑ l, (Q^k) i l * (∑ j, Q l j) := by
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  calc
    _ ≤ ∑ l, (P^k) i l * (∑ j, Q l j) :=
      Finset.sum_le_sum fun l _ ↦ mul_le_mul_of_nonneg_right (hpowle k i l)
        (Finset.sum_nonneg fun j _ ↦ hQ l j)
    _ < ∑ l, (P^k) i l * 1 := by
      apply Finset.sum_lt_sum
      · intro l _
        exact mul_le_mul_of_nonneg_left (hQrow l) ((hpowP k).1 i l)
      · exact ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left hQa (hPk i a)⟩
    _ = 1 := by simp only [mul_one]; exact Matrix.sum_row_of_mem_rowStochastic (hpowP k) i

/-- Diagonal conjugation and scalar normalization commute with every power. -/
theorem diagonal_normalized_matrix_power
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (x : Fin n → ℝ) (hx : ∀ i, x i ≠ 0) (m : ℕ) (i j : Fin n) :
    ((Matrix.of (fun i j ↦ A i j * x j / (ρ * x i)))^m) i j =
      (A^m) i j * x j / (ρ^m * x i) := by
  induction m generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst j; simp [hx i]
    · simp [hij]
  | succ m ih =>
    rw [pow_succ,pow_succ,Matrix.mul_apply,Matrix.mul_apply]
    simp_rw [ih]
    rw [Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    rw [pow_succ]
    simp only [Matrix.of_apply]
    field_simp [hx l,hρ]

/-- Every entry of a proper nonnegative submatrix of a primitive nonnegative
matrix is negligible after normalization by the Perron eigenvalue. Conjugate
both matrices by the same positive eigenvector. The full matrix is stochastic;
the proper submatrix loses mass and its powers tend to zero. -/
theorem proper_submatrix_normalized_entry_limit
    {n : ℕ} [Nonempty (Fin n)] (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hBA : ∀ i j, B i j ≤ A i j)
    (k : ℕ) (hk : 0 < k) (hAk : ∀ i j, 0 < (A^k) i j)
    (a b : Fin n) (hab : B a b < A a b)
    (ρ : ℝ) (hρ : 0 < ρ) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hAx : A *ᵥ x = ρ • x) (i j : Fin n) :
    Filter.Tendsto (fun m : ℕ ↦ (B^m) i j / ρ^m) Filter.atTop (𝓝 0) := by
  let P : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ A i j * x j / (ρ*x i)
  let Q : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ B i j * x j / (ρ*x i)
  have hP : P ∈ Matrix.rowStochastic ℝ (Fin n) := by
    apply Matrix.mem_rowStochastic_iff_sum.mpr
    refine ⟨fun i j ↦ div_nonneg (mul_nonneg (hA i j) (hx j).le) (mul_pos hρ (hx i)).le,?_⟩
    intro i
    change ∑ j, A i j * x j / (ρ*x i) = 1
    rw [← Finset.sum_div]
    change (A *ᵥ x) i / (ρ*x i) = 1
    rw [hAx]
    exact div_self (ne_of_gt (mul_pos hρ (hx i)))
  have hQ : ∀ i j, 0 ≤ Q i j := fun i j ↦
    div_nonneg (mul_nonneg (hB i j) (hx j).le) (mul_pos hρ (hx i)).le
  have hQP : ∀ i j, Q i j ≤ P i j := fun i j ↦
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hBA i j) (hx j).le)
      (mul_pos hρ (hx i)).le
  have hPk (i j : Fin n) : 0 < (P^k) i j := by
    change 0 < ((Matrix.of (fun i j ↦ A i j * x j / (ρ*x i)))^k) i j
    rw [diagonal_normalized_matrix_power A ρ (ne_of_gt hρ) x (fun i ↦ ne_of_gt (hx i))]
    exact div_pos (mul_pos (hAk i j) (hx j)) (mul_pos (pow_pos hρ k) (hx i))
  have hstrict : Q a b < P a b :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hab (hx b)) (mul_pos hρ (hx a))
  have hlim := proper_substochastic_power_decay P Q hP hQ hQP k hk hPk a b hstrict
    (Pi.single j 1)
  have hentry := (continuous_apply i).tendsto (0 : Fin n → ℝ) |>.comp hlim
  have hentry' : Filter.Tendsto (fun m : ℕ ↦ (Q^m) i j) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Pi.zero_apply, Matrix.col_apply] using hentry
  have hh := hentry'.mul_const (x i / x j)
  have heq (m : ℕ) : (Q^m) i j * (x i / x j) = (B^m) i j / ρ^m := by
    change ((Matrix.of (fun i j ↦ B i j * x j / (ρ*x i)))^m) i j *
      (x i / x j) = (B^m) i j / ρ^m
    rw [diagonal_normalized_matrix_power B ρ (ne_of_gt hρ) x (fun i ↦ ne_of_gt (hx i))]
    field_simp [ne_of_gt (hx i), ne_of_gt (hx j), ne_of_gt hρ]
  simpa only [heq, zero_mul] using hh

end HolomorphicAnosov







