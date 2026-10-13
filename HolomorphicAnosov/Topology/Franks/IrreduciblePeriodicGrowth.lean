import HolomorphicAnosov.Topology.Franks.PositivePerronEigenvector
import HolomorphicAnosov.Topology.Franks.UnitProductNoExponentialLimit

open Filter Matrix
open scoped _root_.Topology BigOperators

namespace HolomorphicAnosov

/-- Perron normalization reduces an irreducible nonnegative matrix to a
stochastic matrix. Its trace on a common iterate has a positive integral limit,
and the minimum positive eigenvector coordinate bounds every word count. -/
theorem franks_irreducible_periodic_growth
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      (∀ m : ℕ, (∑ i, ∑ j, (A^m) i j) ≤ K*ρ^m) ∧
      ∃ q c : ℕ, 0 < q ∧ 0 < c ∧
        Tendsto (fun m : ℕ ↦ Matrix.trace (A^(q*m))/ρ^(q*m)) atTop (𝓝 (c:ℝ)) := by
  classical
  obtain ⟨ρ,hρ,x,hx,hsum,hAx⟩ := franks_irreducible_perron_eigenvector A hA hirr
  let P : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j ↦ A i j * x j / (ρ*x i))
  have hp : ∀ i j, 0 ≤ P i j := fun i j ↦
    div_nonneg (mul_nonneg (hA i j) (hx j).le) (mul_pos hρ (hx i)).le
  have hs (i) : ∑ j, P i j = 1 := by
    change ∑ j, A i j * x j / (ρ*x i) = 1
    rw [← Finset.sum_div]
    change (A *ᵥ x) i / (ρ*x i) = 1
    rw [hAx]
    exact div_self (ne_of_gt (mul_pos hρ (hx i)))
  obtain ⟨q,c,hq,hc,hlim⟩ := stochastic_trace_common_iterate_limit P hp hs
  have hpow (m : ℕ) : (P^m).map Complex.ofReal = (P.map Complex.ofReal)^m := by
    exact Matrix.map_pow P Complex.ofRealHom m
  have htrace (m : ℕ) : (Matrix.trace ((P.map Complex.ofReal)^m)).re =
      Matrix.trace (A^m)/ρ^m := by
    rw [← hpow]
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, Complex.re_sum, Complex.ofReal_re]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    change ((Matrix.of (fun i j ↦ A i j * x j / (ρ*x i)))^m) i i = _
    rw [diagonal_normalized_matrix_power A ρ (ne_of_gt hρ) x (fun i ↦ ne_of_gt (hx i))]
    field_simp [ne_of_gt (hx i)]
  have hlimR := Complex.continuous_re.tendsto (c:ℂ) |>.comp hlim
  have hlim' : Tendsto (fun m : ℕ ↦ Matrix.trace (A^(q*m))/ρ^(q*m)) atTop (𝓝 (c:ℝ)) := by
    simpa only [Function.comp_def,htrace,Complex.natCast_re] using hlimR
  obtain ⟨imin,_,hmin⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  refine ⟨ρ,(x imin)⁻¹,hρ,inv_pos.mpr (hx imin),?_,q,c,hq,hc,hlim'⟩
  intro m
  have heig (m : ℕ) : A^m *ᵥ x = ρ^m • x := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec,hAx,Matrix.mulVec_smul,ih,pow_succ]
      ext i
      simp only [Pi.smul_apply,smul_eq_mul]
      ring
  have hweighted : ∑ i, ∑ j, (A^m) i j * x j = ρ^m := by
    change ∑ i, (A^m *ᵥ x) i = ρ^m
    rw [heig]
    change ∑ i, ρ^m * x i = ρ^m
    rw [← Finset.mul_sum,hsum,mul_one]
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ (hx imin)).mpr
  rw [← hweighted,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ j)) (Matrix.pow_apply_nonneg hA m i j)

/-- A sequence squeezed between the trace and the entry sum of one irreducible
nonnegative matrix has two-sided exponential bounds along a common iterate. -/
theorem count_exponential_bounds_of_irreducible_matrix
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (p : ℕ → ℝ) (D : ℝ) (hD : 0 < D)
    (hcount : ∀ m : ℕ, 0 < m → Matrix.trace (A^m) ≤ D*p m ∧
      p m ≤ ∑ i, ∑ j, (A^m) i j) :
    ∃ ρ a b : ℝ, ∃ q : ℕ, 0 < ρ ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      (∀ m : ℕ, 0 < m → p m ≤ b*ρ^m) ∧
      ∀ᶠ m : ℕ in atTop, a*ρ^(q*m) ≤ p (q*m) := by
  obtain ⟨ρ,b,hρ,hb,hupp,q,c,hq,hc,hlim⟩ := franks_irreducible_periodic_growth A hA hirr
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hlow : ∀ᶠ m : ℕ in atTop, (c:ℝ)/2 < Matrix.trace (A^(q*m))/ρ^(q*m) :=
    hlim.eventually (lt_mem_nhds (show (c:ℝ)/2 < (c:ℝ) by linarith))
  refine ⟨ρ,(c:ℝ)/(2*D),b,q,hρ,div_pos hcR (by positivity),hb,hq,
    fun m hm ↦ (hcount m hm).2.trans (hupp m),?_⟩
  filter_upwards [hlow, eventually_ge_atTop 1] with m hm hmpos
  have hp : 0 < ρ^(q*m) := pow_pos hρ _
  have ht := (lt_div_iff₀ hp).mp hm
  have hcnt := (hcount (q*m) (Nat.mul_pos hq (by omega))).1
  apply (mul_le_mul_iff_of_pos_right hD).mp
  calc
    (c:ℝ)/(2*D)*ρ^(q*m)*D = (c:ℝ)/2*ρ^(q*m) := by field_simp [ne_of_gt hD]
    _ ≤ Matrix.trace (A^(q*m)) := ht.le
    _ ≤ D*p (q*m) := hcnt
    _ = p (q*m)*D := mul_comm _ _

/-- A finite nonempty sum of nonnegative counts inherits two-sided exponential
bounds. Use a component of maximal rate for the lower bound and sum all upper
coefficients; only the maximal component's iterate is needed. -/
theorem finite_sum_count_exponential_bounds
    {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℕ → ℝ)
    (hnonneg : ∀ i m, 0 ≤ p i m)
    (hgrowth : ∀ i, ∃ ρ a b : ℝ, ∃ q : ℕ, 0 < ρ ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      (∀ m : ℕ, 0 < m → p i m ≤ b*ρ^m) ∧
      ∀ᶠ m : ℕ in atTop, a*ρ^(q*m) ≤ p i (q*m)) :
    ∃ r a b : ℝ, ∃ q : ℕ, 0 < r ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      ∀ᶠ m : ℕ in atTop, a*r^m ≤ ∑ i, p i (q*m) ∧
        (∑ i, p i (q*m)) ≤ b*r^m := by
  classical
  choose ρ a b q hρ ha hb hq hu hl using hgrowth
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ ρ Finset.univ_nonempty
  have hbpos : 0 < ∑ j, b j := Finset.sum_pos (fun j _ ↦ hb j) Finset.univ_nonempty
  refine ⟨ρ i ^ q i,a i,∑ j, b j,q i,pow_pos (hρ i) _,ha i,hbpos,hq i,?_⟩
  filter_upwards [hl i,eventually_ge_atTop 1] with m hm hmpos
  constructor
  · rw [← pow_mul]
    exact hm.trans (Finset.single_le_sum (fun j _ ↦ hnonneg j _) (Finset.mem_univ i))
  · calc
      ∑ j, p j (q i*m) ≤ ∑ j, b j * ρ j ^ (q i*m) :=
        Finset.sum_le_sum fun j _ ↦ hu j _ (Nat.mul_pos (hq i) (by omega))
      _ ≤ ∑ j, b j * ρ i ^ (q i*m) := Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hρ j).le (hi j (Finset.mem_univ _)) _) (hb j).le
      _ = (∑ j, b j) * (ρ i^q i)^m := by rw [← Finset.sum_mul,pow_mul]

end HolomorphicAnosov


