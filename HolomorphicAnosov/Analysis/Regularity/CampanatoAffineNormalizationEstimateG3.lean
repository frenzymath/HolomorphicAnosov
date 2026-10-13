import HolomorphicAnosov.Analysis.Regularity.CampanatoAffineTransportG3
import HolomorphicAnosov.Analysis.Regularity.PolynomialAffineMixedPartialIdentityG3
import HolomorphicAnosov.Analysis.Regularity.EuclideanPolynomialMixedPartial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HolomorphicAnosov.Analysis.Regularity

/-- Exact positive-radius exponent cancellation used in Campanato's affine
normalization. -/
theorem campanato_rpow_affine_exponent_g3
    (ρ : ℝ) (hρ : 0 < ρ) (b : ℝ) (N : ℕ) :
    Real.rpow ρ (-b - (N : ℝ) / 2) * Real.rpow ρ ((N : ℝ) / 2) =
      Real.rpow ρ (-b) := by
  calc
    Real.rpow ρ (-b - (N : ℝ) / 2) * Real.rpow ρ ((N : ℝ) / 2) =
        Real.rpow ρ ((-b - (N : ℝ) / 2) + (N : ℝ) / 2) :=
      (Real.rpow_add hρ _ _).symm
    _ = Real.rpow ρ (-b) := by congr 1 ; ring

/-- Positivity bookkeeping for the Campanato normalization constant. -/
theorem campanato_normalization_constant_positive_g3
    (K₀ v : ℝ) (hK₀ : 0 < K₀) :
    0 < K₀ * max 1 (Real.sqrt v) := by
  exact mul_pos hK₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- Inverse-radius form of an affine mixed-partial scaling identity. -/
theorem campanato_affine_derivative_rescale_g3
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (x y : ℝ)
    (hxy : x = ρ ^ m * y) :
    |y| = Real.rpow ρ (-(m : ℝ)) * |x| := by
  have hneg : Real.rpow ρ (-(m : ℝ)) = (Real.rpow ρ (m : ℝ))⁻¹ :=
    Real.rpow_neg (le_of_lt hρ) (m : ℝ)
  have hnat : Real.rpow ρ (m : ℝ) = ρ ^ m := Real.rpow_natCast ρ m
  rw [hxy, abs_mul, hneg, hnat]
  rw [abs_of_pos (pow_pos hρ m)]
  field_simp

/-! The finite coefficient-to-classical-derivative calculation used by the
Campanato normalization is kept as a named provider obligation. -/

/-- Repeated differentiation in one coordinate sends a monomial to the
subtracted exponent monomial with the descending-factorial coefficient.

This is the one-coordinate algebraic part of Campanato's finite monomial
calculation (printed p.143). -/
theorem campanato_iterated_pderiv_monomial_g3
    {N : ℕ} (i : Fin N) (s : Fin N →₀ ℕ) (c : ℝ) (k : ℕ) :
    (MvPolynomial.pderiv i)^[k] (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - Finsupp.single i k)
        (c * (s i).descFactorial k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial]
      rw [MvPolynomial.monomial_eq_monomial_iff]
      left
      constructor
      · ext j
        by_cases h : j = i <;> simp [h, Nat.sub_sub]
      · rw [Nat.descFactorial_succ]
        rw [show (s - Finsupp.single i k) i = s i - k by simp]
        push_cast
        ring

/-! The distinct-coordinate finite fold is isolated from its zero-evaluation
calculation.  This stronger normal form is the next finite Finsupp provider
obligation in the Campanato coefficient calculation. -/

/-- Distinct-coordinate truncated subtraction commutes in the finite monomial
fold. -/
theorem campanato_fold_monomial_list_subtraction_commute_g3
    {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (s : Fin N →₀ ℕ) (a b : ℕ) :
    (s - Finsupp.single i a) - Finsupp.single j b =
      s - (Finsupp.single i a + Finsupp.single j b) := by
  ext k
  by_cases hik : k = i
  · subst k
    have hj : j ≠ i := by intro h; exact hij h.symm
    simp [Finsupp.single_eq_same, Nat.sub_sub]
  · by_cases hjk : k = j
    · subst k
      simp [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hik]
    · simp [Finsupp.single_eq_of_ne hik, Finsupp.single_eq_of_ne hjk]

/-- Finite list arithmetic preserving the monomial derivative normal form.
This earlier plumbing theorem lets the initialized tail fold reuse the same
normal-form calculation without a declaration-order cycle. -/
theorem campanato_fold_monomial_list_arithmetic_g3
    {N : ℕ} (L : List (Fin N)) (hL : L.Nodup)
    (s β : Fin N →₀ ℕ) (c : ℝ) :
    L.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q)
        (MvPolynomial.monomial s c) =
      MvPolynomial.monomial
        (s - L.foldl (fun t i ↦ t + Finsupp.single i (β i)) 0)
        (c * L.foldl (fun q i ↦ q * (s i).descFactorial (β i)) 1) := by
  have aux : ∀ (K : List (Fin N)), K.Nodup → ∀ (s : Fin N →₀ ℕ) (c : ℝ),
      K.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q)
        (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - (K.map (fun i => Finsupp.single i (β i))).sum)
        (c * ((K.map (fun i => (s i).descFactorial (β i))).prod : ℕ)) := by
    intro K
    induction K with
    | nil => intros; simp
    | cons j K ih =>
      intro hK s c
      rw [List.foldl_cons, campanato_iterated_pderiv_monomial_g3, ih hK.of_cons]
      have hm : K.map (fun k => ((s - Finsupp.single j (β j)) k).descFactorial (β k)) =
          K.map (fun k => (s k).descFactorial (β k)) := by
        apply List.map_congr_left
        intro k hk
        have hkj : k ≠ j := by
          intro heq
          exact (List.nodup_cons.mp hK).1 (heq ▸ hk)
        simp [hkj]
      rw [hm]
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [tsub_tsub]
      push_cast
      rw [mul_assoc]
  simpa only [List.sum_eq_foldl, List.prod_eq_foldl, List.foldl_map] using aux L hL s c

theorem campanato_fold_monomial_list_tail_cons_arithmetic_g3
    {N : ℕ} (i : Fin N) (L : List (Fin N)) (hL : L.Nodup)
    (hnot : i ∉ L) (s β : Fin N →₀ ℕ) (c : ℝ) :
    L.foldl (fun Q j ↦ (MvPolynomial.pderiv j)^[β j] Q)
        (MvPolynomial.monomial (s - Finsupp.single i (β i))
          (c * (s i).descFactorial (β i))) =
      MvPolynomial.monomial
        (s - L.foldl (fun t j ↦ t + Finsupp.single j (β j))
          (Finsupp.single i (β i)))
        (c * L.foldl (fun q j ↦ q * (s j).descFactorial (β j))
          ((s i).descFactorial (β i))) := by
  rw [campanato_fold_monomial_list_arithmetic_g3 L hL]
  have hm : L.map (fun j => ((s - Finsupp.single i (β i)) j).descFactorial (β j)) =
      L.map (fun j => (s j).descFactorial (β j)) := by
    apply List.map_congr_left
    intro j hj
    have hji : j ≠ i := by
      intro heq
      exact hnot (heq ▸ hj)
    simp [hji]
  have addfold : ∀ (a : Fin N →₀ ℕ),
      L.foldl (fun t j => t + Finsupp.single j (β j)) a =
        a + (L.map (fun j => Finsupp.single j (β j))).sum := by
    intro a
    rw [← List.foldl_map]
    conv_lhs => arg 2; rw [← add_zero a]
    rw [List.foldl_assoc, ← List.sum_eq_foldl]
  have mulfold : ∀ (f : Fin N → ℕ) (a : ℕ),
      L.foldl (fun q j => q * f j) a = a * (L.map f).prod := by
    intro f a
    rw [← List.foldl_map]
    conv_lhs => arg 2; rw [← mul_one a]
    rw [List.foldl_assoc, ← List.prod_eq_foldl]
  rw [addfold, addfold, mulfold, mulfold, hm]
  simp only [zero_add, one_mul, tsub_tsub, Nat.cast_mul, mul_assoc]



theorem campanato_fold_monomial_list_tail_invariance_g3
    {N : ℕ} (i : Fin N) (L : List (Fin N)) (hL : L.Nodup)
    (hnot : i ∉ L) (s β : Fin N →₀ ℕ) (c : ℝ) :
    L.foldl (fun Q j ↦ (MvPolynomial.pderiv j)^[β j] Q)
        (MvPolynomial.monomial (s - Finsupp.single i (β i))
          (c * (s i).descFactorial (β i))) =
      MvPolynomial.monomial
        (s - L.foldl (fun t j ↦ t + Finsupp.single j (β j))
          (Finsupp.single i (β i)))
        (c * L.foldl (fun q j ↦ q * (s j).descFactorial (β j))
          ((s i).descFactorial (β i))) := by
  exact campanato_fold_monomial_list_tail_cons_arithmetic_g3 i L hL hnot s β c

theorem campanato_fold_monomial_list_induction_step_g3
    {N : ℕ} (i : Fin N) (L : List (Fin N)) (hL : L.Nodup)
    (hnot : i ∉ L) (s β : Fin N →₀ ℕ) (c : ℝ) :
    L.foldl (fun Q j ↦ (MvPolynomial.pderiv j)^[β j] Q)
        (MvPolynomial.monomial (s - Finsupp.single i (β i))
          (c * (s i).descFactorial (β i))) =
      MvPolynomial.monomial
        (s - L.foldl (fun t j ↦ t + Finsupp.single j (β j))
          (Finsupp.single i (β i)))
        (c * L.foldl (fun q j ↦ q * (s j).descFactorial (β j))
          ((s i).descFactorial (β i))) := by
  exact campanato_fold_monomial_list_tail_invariance_g3 i L hL hnot s β c


/-- List-level monomial fold normal form. Distinct coordinates make the
coordinatewise Finsupp subtraction independent, while coefficient factors
multiply in list order. -/
theorem campanato_fold_monomial_list_form_g3
    {N : ℕ} (L : List (Fin N)) (hL : L.Nodup)
    (s β : Fin N →₀ ℕ) (c : ℝ) :
    L.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q)
        (MvPolynomial.monomial s c) =
      MvPolynomial.monomial
        (s - L.foldl (fun t i ↦ t + Finsupp.single i (β i)) 0)
        (c * L.foldl (fun q i ↦ q * (s i).descFactorial (β i)) 1) := by
  exact campanato_fold_monomial_list_arithmetic_g3 L hL s β c

theorem campanato_finRange_fold_single_sum_g3
    {N : ℕ} (β : Fin N →₀ ℕ) :
    (List.finRange N).foldl
        (fun t i ↦ t + Finsupp.single i (β i)) 0 = β := by
  have hsum : ((List.finRange N).map (fun i => Finsupp.single i (β i))).sum = β := by
    rw [← Fin.sum_univ_def]
    exact Finsupp.univ_sum_single β
  simpa only [List.sum_eq_foldl, List.foldl_map] using hsum

theorem campanato_finRange_fold_descfactorial_prod_g3
    {N : ℕ} (s β : Fin N →₀ ℕ) :
    (List.finRange N).foldl
        (fun q i ↦ q * (s i).descFactorial (β i)) 1 =
      β.prod (fun i k ↦ (s i).descFactorial k) := by
  have hprod : β.prod (fun i k ↦ (s i).descFactorial k) =
      ∏ i : Fin N, (s i).descFactorial (β i) := by
    apply Finsupp.prod_fintype
    intro i
    simp
  have hlist : ((List.finRange N).map
      (fun i => (s i).descFactorial (β i))).prod =
      β.prod (fun i k ↦ (s i).descFactorial k) := by
    rw [← Fin.prod_univ_def, hprod]
  simpa only [List.prod_eq_foldl, List.foldl_map] using hlist


theorem campanato_finRange_fold_aggregate_g3
    {N : ℕ} (s β : Fin N →₀ ℕ) :
    (List.finRange N).foldl
        (fun t i ↦ t + Finsupp.single i (β i)) 0 = β ∧
      (List.finRange N).foldl
        (fun q i ↦ q * (s i).descFactorial (β i)) 1 =
        β.prod (fun i k ↦ (s i).descFactorial k) := by
  exact ⟨campanato_finRange_fold_single_sum_g3 β,
    campanato_finRange_fold_descfactorial_prod_g3 s β⟩

theorem campanato_finRange_fold_derivative_form_g3
    {N : ℕ} (s β : Fin N →₀ ℕ) (c : ℝ) :
    (List.finRange N).foldl
        (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q)
        (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - β)
        (c * (β.prod (fun i k ↦ (s i).descFactorial k) : ℝ)) := by
  rw [campanato_fold_monomial_list_form_g3 (List.finRange N)
    (List.nodup_finRange N) s β c]
  have ha := campanato_finRange_fold_aggregate_g3 s β
  rw [ha.1, ha.2]
  congr 2
  exact_mod_cast rfl


/-- Finite Finsupp arithmetic for the zero evaluation of the derivative form.
The zero branch must retain the descending-factorial vanishing when one
coordinate of `β` exceeds the corresponding coordinate of `s`; this is the
remaining reusable arithmetic provider for the coefficient calculation. -/
theorem campanato_finRange_fold_zero_arithmetic_g3
    {N : ℕ} (s β : Fin N →₀ ℕ) (c : ℝ) :
    (if s - β = 0 then
        c * (β.prod (fun i k ↦ (s i).descFactorial k) : ℝ)
      else 0) =
      if s = β then
        (β.prod (fun _ k ↦ k.factorial) : ℝ) * c
      else 0 := by
  classical
  by_cases hEq : s = β
  · subst β
    have hp : s.prod (fun i k ↦ (s i).descFactorial k) =
        s.prod (fun _ k ↦ k.factorial) := by
      apply Finsupp.prod_congr
      intro i hi
      simp [Nat.descFactorial_self]
    have hpr : (s.prod (fun i k ↦ (s i).descFactorial k) : ℝ) =
        (s.prod (fun _ k ↦ k.factorial) : ℝ) := by
      exact_mod_cast hp
    simp [hpr, mul_comm]
  · by_cases hsub : s - β = 0
    · have hle : s ≤ β := (Finsupp.le_def).2 (by
        intro i
        have hi := congrArg (fun t : Fin N →₀ ℕ => t i) hsub
        exact Nat.le_of_sub_eq_zero hi)
      have hex : ∃ i, s i < β i := by
        by_contra hno
        push Not at hno
        have hge : β ≤ s := (Finsupp.le_def).2 (by
          intro i
          exact hno i)
        exact hEq (le_antisymm hle hge)
      rcases hex with ⟨i, hi⟩
      have hib : i ∈ β.support := (Finsupp.mem_support_iff).2 (by
        have : β i ≠ 0 := by omega
        exact this)
      have hprod : β.prod (fun j k ↦ (s j).descFactorial k) = 0 := by
        apply (Finsupp.prod_eq_zero_iff).2
        refine ⟨i, hib, ?_⟩
        exact (Nat.descFactorial_eq_zero_iff_lt).2 hi
      have hprodr : (β.prod (fun j k ↦ (s j).descFactorial k) : ℝ) = 0 := by
        exact_mod_cast hprod
      simp [hsub, hEq, hprodr]
    · simp [hsub, hEq]

/-- The remaining finite-coordinate monomial evaluation: after the distinct
`Fin N` coordinate derivatives have been applied, evaluation at zero keeps
exactly the beta monomial and contributes the product of factorials. -/
theorem campanato_finRange_fold_monomial_zero_g3
    {N : ℕ} (s β : Fin N →₀ ℕ) (c : ℝ) :
    MvPolynomial.eval (fun _ ↦ 0)
        ((List.finRange N).foldl
          (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q)
          (MvPolynomial.monomial s c)) =
      (β.prod (fun _ k ↦ k.factorial) : ℝ) *
        (MvPolynomial.monomial s c).coeff β := by
  rw [campanato_finRange_fold_derivative_form_g3]
  rw [MvPolynomial.eval_zero']
  rw [MvPolynomial.constantCoeff_eq]
  simp [MvPolynomial.coeff_monomial]
  exact campanato_finRange_fold_zero_arithmetic_g3 s β c

/-- The ordered polynomial `pderiv` fold evaluated at zero extracts the
corresponding coefficient with the product of coordinate factorials.

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], printed p.143.  Expand the finite monomial support and apply the
descending-factorial formula in each coordinate; all unmatched monomials
vanish at the origin. -/
theorem campanato_fold_pderiv_coeff_zero_g3
    {N : ℕ} (P : MvPolynomial (Fin N) ℝ) (β : Fin N →₀ ℕ) :
    MvPolynomial.eval (fun _ ↦ 0)
        ((List.finRange N).foldl
          (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q) P) =
      (β.prod (fun _ k ↦ k.factorial) : ℝ) * P.coeff β := by
  classical
  have iter_add : ∀ (i : Fin N) (k : ℕ) (P Q : MvPolynomial (Fin N) ℝ),
      (MvPolynomial.pderiv i)^[k] (P + Q) =
        (MvPolynomial.pderiv i)^[k] P + (MvPolynomial.pderiv i)^[k] Q := by
    intro i k
    induction k with
    | zero => intro P Q; simp
    | succ k ih =>
        intro P Q
        rw [Function.iterate_succ_apply']
        have hk := ih P Q
        rw [hk, Derivation.map_add]
        simp only [← Function.iterate_succ_apply']
  induction P using MvPolynomial.induction_on' with
  | monomial s c => exact campanato_finRange_fold_monomial_zero_g3 s β c
  | add P Q hP hQ =>
      have hfold : ∀ (L : List (Fin N)) (P Q : MvPolynomial (Fin N) ℝ),
          L.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q) (P + Q) =
            L.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q) P +
              L.foldl (fun Q i ↦ (MvPolynomial.pderiv i)^[β i] Q) Q := by
        intro L
        induction L with
        | nil => intro P Q; simp
        | cons i L ih =>
            simp only [List.foldl]
            intro P Q
            rw [iter_add, ih]
      rw [hfold, MvPolynomial.eval_add]
      rw [hP, hQ]
      change _ = (β.prod (fun _ k ↦ k.factorial) : ℝ) *
        (P.coeff β + Q.coeff β)
      ring

/-- At the origin, the ordered classical mixed partial of a polynomial is its
coefficient multiplied by the multi-index factorial.

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], printed p.143.  Expand the polynomial into its finite monomial
sum, differentiate each coordinate the prescribed number of times, and
evaluate at zero.  Terms whose exponent is below the prescribed index vanish
under differentiation, terms above it retain a positive power of a coordinate
and vanish at zero, and the matching term contributes the product of
factorials.  The ordered fold in `euclideanPolynomialMixedPartial` is the
coordinate implementation of this finite calculation. -/
theorem campanato_mixed_partial_coeff_at_zero_g3
    {N : ℕ} (P : MvPolynomial (Fin N) ℝ) (β : Fin N →₀ ℕ) :
    euclideanPolynomialMixedPartial P (fun i ↦ β i) 0 =
      (β.prod (fun _ k ↦ k.factorial) : ℝ) * P.coeff β := by
  rw [mixed_eval_fold]
  exact campanato_fold_pderiv_coeff_zero_g3 P β

/-! The unit-ball coefficient-to-derivative step is separated from the
affine change of variables in the core estimate below. -/

/-- Campanato's normalized coefficient minimum gives a unit-ball mixed-partial
L2 bound at the origin.

This is the finite-dimensional coefficient step in Campanato, *Proprietà di
una famiglia di spazi funzionali* (1964), Lemma [2.I], equations (2.7)--(2.9),
pp.140--142.  The linear coefficient chart supplied by `hlower` controls the
polynomial coefficient vector on measurable subsets of the unit ball.  The
coefficient-to-classical-derivative conversion uses the exact mixed-partial
identity `hmixed`; positivity of the resulting constant is retained.  The
remaining formal work is the compact finite-dimensional norm comparison and
its measurable-subset integral bookkeeping, isolated here as a named Stage 1
obligation.
-/
/- The first finite-dimensional residual is the coefficient functional bound
for the chosen linear chart.  It is stated separately so that the subsequent
unit-ball argument only has to combine this norm comparison with the supplied
positive sphere minimum. -/
theorem campanato_admissible_multiindex_finite_g3
    (N n : ℕ) :
    ∃ I : Finset (Fin N →₀ ℕ),
      ∀ β : Fin N →₀ ℕ, (∑ i, β i) ≤ n → β ∈ I := by
  let S := {β : Fin N →₀ ℕ // (∑ i, β i) ≤ n}
  let f : S → (Fin N → Fin (n + 1)) := fun β i =>
    ⟨β.1 i, Nat.lt_succ_of_le (by
      have hle : β.1 i ≤ β.1.sum (fun _ m => m) :=
        Finsupp.single_eval_le_sum β.1 (g := id) (by rfl)
          (by intro x; exact Nat.zero_le _) i
      have hsum : β.1.sum (fun _ m => m) = ∑ j, β.1 j := by
        rw [Finsupp.sum_fintype]
        simp
      exact hle.trans (hsum ▸ β.2))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    ext i
    have hi := congrFun hxy i
    change (f x i).val = (f y i).val
    exact congrArg Fin.val hi
  let : Finite S := Finite.of_injective f hf
  let : Fintype S := Fintype.ofFinite S
  let I : Finset (Fin N →₀ ℕ) := Finset.univ.image (fun β : S => β.1)
  refine ⟨I, ?_⟩
  intro β hβ
  exact Finset.mem_image.mpr ⟨⟨β, hβ⟩, Finset.mem_univ _, rfl⟩

theorem campanato_unit_ball_coefficient_norm_comparison_g3
    {N n d : ℕ}
    (e : (Fin d → ℝ) ≃ₗ[ℝ]
      ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n)) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (hP : P.totalDegree ≤ n)
        (β : Fin N →₀ ℕ) (_hβ : (∑ i, β i) ≤ n),
        |P.coeff β| ≤
          B * ‖e.symm ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩‖ := by
  obtain ⟨I, hI⟩ := campanato_admissible_multiindex_finite_g3 N n
  let L : (Fin N →₀ ℕ) → ((Fin d → ℝ) →L[ℝ] ℝ) := fun β =>
    ContinuousLinearMap.mk
      ((MvPolynomial.lcoeff ℝ β).comp
        ((Submodule.subtype _).comp e.toLinearMap))
      (LinearMap.continuous_of_finiteDimensional _)
  let B : ℝ := 1 + ∑ β ∈ I, ‖L β‖
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro P hP β hβ
  have hβI : β ∈ I := hI β hβ
  have hnorm : ‖L β‖ ≤ ∑ γ ∈ I, ‖L γ‖ := by
    exact Finset.single_le_sum (fun γ hγ => norm_nonneg _) hβI
  have hv := (L β).le_opNorm
    (e.symm ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩)
  have hcoeff :
      L β (e.symm ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩) = P.coeff β := by
    simp [L]
  rw [hcoeff, Real.norm_eq_abs] at hv
  calc
    |P.coeff β| ≤ ‖L β‖ * ‖e.symm ⟨P,
        (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩‖ := hv
    _ ≤ B * ‖e.symm ⟨P,
        (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩‖ := by
      gcongr
      dsimp [B]
      linarith

theorem campanato_unit_ball_normalized_integral_rescaling_g3
    (N n d : ℕ) (A _c : ℝ)
    (e : (Fin d → ℝ) ≃ₗ[ℝ]
      ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n)) :
    ∀ (P : MvPolynomial (Fin N) ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
      ∀ hP : P.totalDegree ≤ n, NullMeasurableSet E volume →
      E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
      A ≤ volume.real E →
      ∀ v : Fin d → ℝ,
        (v ≠ 0) →
        e v = ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩ →
        (∫ x in E, |MvPolynomial.eval (fun i ↦ x i)
          ((e (‖v‖⁻¹ • v)).val)| ^ 2) =
          ‖v‖⁻¹ ^ 2 * (∫ x in E, |euclideanPolynomialEval P x| ^ 2) := by
  intro P E hP hE hEK hA v hv hveq
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin N),
      MvPolynomial.eval (fun i ↦ x i) ((e (‖v‖⁻¹ • v)).val) =
        ‖v‖⁻¹ * euclideanPolynomialEval P x := by
    intro x
    rw [LinearEquiv.map_smul e, hveq]
    simp [euclideanPolynomialEval]
  calc
    _ = ∫ x in E, |‖v‖⁻¹ * euclideanPolynomialEval P x| ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hpoint]
    _ = ‖v‖⁻¹ ^ 2 * (∫ x in E, |euclideanPolynomialEval P x| ^ 2) := by
      rw [show (fun x => |‖v‖⁻¹ * euclideanPolynomialEval P x| ^ 2) =
          (fun x => ‖v‖⁻¹ ^ 2 * |euclideanPolynomialEval P x| ^ 2) by
            funext x
            rw [abs_mul, mul_pow, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]]
      rw [MeasureTheory.integral_const_mul]

theorem campanato_unit_ball_normalized_chart_scaling_g3
    (N n d : ℕ) (A c : ℝ) (hc : 0 < c)
    (e : (Fin d → ℝ) ≃ₗ[ℝ]
      ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n))
    (hmin : ∀ v : Fin d → ℝ, v ∈ Metric.sphere (0 : Fin d → ℝ) 1 →
      ∀ E : Set (EuclideanSpace ℝ (Fin N)),
        NullMeasurableSet E volume →
        E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
        A ≤ volume.real E →
        c ≤ ∫ x in E,
          |MvPolynomial.eval (fun i ↦ x i) ((e v).val)| ^ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
        ∀ hP : P.totalDegree ≤ n, NullMeasurableSet E volume →
        E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
        A ≤ volume.real E →
        ‖e.symm ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩‖ ≤
          C * Real.sqrt (∫ x in E, |euclideanPolynomialEval P x| ^ 2) := by
  have hrescale := campanato_unit_ball_normalized_integral_rescaling_g3
    N n d A c e
  refine ⟨(Real.sqrt c)⁻¹, by positivity, ?_⟩
  intro P E hP hE hEK hA
  let v := e.symm ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩
  by_cases hv : v = 0
  · simp [v, hv]
    positivity
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : u ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
      rw [Metric.mem_sphere]
      simp [u, norm_smul]
      field_simp
    have hm := hmin u hu E hE hEK hA
    have hs := hrescale P E hP hE hEK hA v hv (e.apply_symm_apply _)
    rw [hs] at hm
    have hI : 0 ≤ ∫ x in E, |euclideanPolynomialEval P x| ^ 2 := by
      exact integral_nonneg (fun _ ↦ sq_nonneg _)
    have hmul : c * ‖v‖ ^ 2 ≤
        ∫ x in E, |euclideanPolynomialEval P x| ^ 2 := by
      calc
        c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 *
            (∫ x in E, |euclideanPolynomialEval P x| ^ 2)) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hm (sq_nonneg _)
        _ = ∫ x in E, |euclideanPolynomialEval P x| ^ 2 := by
          field_simp
    have hsq : ‖v‖ ^ 2 ≤
        (Real.sqrt c)⁻¹ ^ 2 *
          (Real.sqrt (∫ x in E, |euclideanPolynomialEval P x| ^ 2)) ^ 2 := by
      have hc' : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
      have htarget : (Real.sqrt c) ^ 2 * ‖v‖ ^ 2 ≤
          (Real.sqrt (∫ x in E, |euclideanPolynomialEval P x| ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt hc.le, Real.sq_sqrt hI]
        exact hmul
      have hh := mul_le_mul_of_nonneg_left htarget
        (sq_nonneg (Real.sqrt c)⁻¹)
      calc
        ‖v‖ ^ 2 = (Real.sqrt c)⁻¹ ^ 2 * ((Real.sqrt c) ^ 2 * ‖v‖ ^ 2) := by
          field_simp
        _ ≤ (Real.sqrt c)⁻¹ ^ 2 *
            (Real.sqrt (∫ x in E, |euclideanPolynomialEval P x| ^ 2)) ^ 2 := hh
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (Real.sqrt_pos.2 hc).le)
      (Real.sqrt_nonneg _))).mp (by simpa [mul_pow] using hsq)

theorem campanato_affine_normalization_unit_ball_coeff_derivative_g3
    (N n : ℕ) (_hN : 1 ≤ N) (_hN0 : 0 ≤ N) (A : ℝ) (_hA : 0 < A)
    (_hAv : A ≤ volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))
    (hmixed : ∀ (P : MvPolynomial (Fin N) ℝ) (β : Fin N →₀ ℕ),
      euclideanPolynomialMixedPartial P (fun i ↦ β i) 0 =
        (β.prod (fun _ k ↦ k.factorial) : ℝ) * P.coeff β)
    (hlower :
      ∃ d : ℕ,
        ∃ e : (Fin d → ℝ) ≃ₗ[ℝ]
          ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n),
        ∃ c : ℝ, 0 < c ∧
          ∀ v : Fin d → ℝ, v ∈ Metric.sphere (0 : Fin d → ℝ) 1 →
          ∀ E : Set (EuclideanSpace ℝ (Fin N)),
            NullMeasurableSet E volume →
            E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
            A ≤ volume.real E →
            c ≤ ∫ x in E,
              |MvPolynomial.eval (fun i ↦ x i) ((e v).val)| ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
        P.totalDegree ≤ n → NullMeasurableSet E volume →
        E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
        A ≤ volume.real E →
        ∀ β : Fin N → ℕ, (∑ i, β i) ≤ n →
          |euclideanPolynomialMixedPartial P β 0| ≤
            K * Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
  obtain ⟨d, e, c, hc, hmin⟩ := hlower
  obtain ⟨B, hB, hcoef⟩ := campanato_unit_ball_coefficient_norm_comparison_g3 e
  obtain ⟨C, hC, hscale⟩ := campanato_unit_ball_normalized_chart_scaling_g3
    N n d A c hc e hmin
  obtain ⟨I, hI⟩ := campanato_admissible_multiindex_finite_g3 N n
  let F : ℝ := 1 + ∑ γ ∈ I, (γ.prod (fun _ k ↦ k.factorial) : ℝ)
  have hF : 0 < F := by
    have hsum : 0 ≤ ∑ γ ∈ I, (γ.prod (fun _ k ↦ k.factorial) : ℝ) := by
      exact Finset.sum_nonneg (fun γ _ ↦ Finset.prod_nonneg
        (fun _ _ ↦ Nat.cast_nonneg _))
    dsimp [F]
    linarith
  refine ⟨F * B * C, mul_pos (mul_pos hF hB) hC, ?_⟩
  intro P E hP hE hEK hA β hβ
  let b : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm β
  have hbfun : (fun i ↦ b i) = β := by
    exact Finsupp.equivFunOnFinite.apply_symm_apply β
  have hbsum : (∑ i, b i) = ∑ i, β i := by
    simp [b]
  have hb : (∑ i, b i) ≤ n := hbsum ▸ hβ
  have hβI : b ∈ I := hI b hb
  have hfac_nonneg : 0 ≤ (b.prod (fun _ k ↦ k.factorial) : ℝ) := by
    simpa [Finsupp.prod] using
      (Finset.prod_nonneg (s := b.support)
        (fun i hi ↦ Nat.cast_nonneg (b i).factorial))
  have hfac : (b.prod (fun _ k ↦ k.factorial) : ℝ) ≤ F := by
    dsimp [F]
    calc
      (b.prod (fun _ k ↦ k.factorial) : ℝ) ≤
          ∑ γ ∈ I, (γ.prod (fun _ k ↦ k.factorial) : ℝ) := by
        exact Finset.single_le_sum
          (f := fun γ : Fin N →₀ ℕ => (γ.prod (fun _ k ↦ k.factorial) : ℝ))
          (fun γ _ ↦ by
            simpa [Finsupp.prod] using
              (Finset.prod_nonneg (s := γ.support)
                (fun i hi ↦ Nat.cast_nonneg (γ i).factorial))) hβI
      _ ≤ 1 + ∑ γ ∈ I, (γ.prod (fun _ k ↦ k.factorial) : ℝ) := by linarith
  have hnorm := hscale P E hP hE hEK hA
  have hcoeff := hcoef P hP b hb
  calc
    |euclideanPolynomialMixedPartial P β 0| =
        (b.prod (fun _ k ↦ k.factorial) : ℝ) * |P.coeff b| := by
      rw [← hbfun, hmixed P b, abs_mul, abs_of_nonneg hfac_nonneg]
    _ ≤ (b.prod (fun _ k ↦ k.factorial) : ℝ) *
        (B * ‖e.symm ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩‖) := by
      exact mul_le_mul_of_nonneg_left hcoeff hfac_nonneg
    _ ≤ F * (B * ‖e.symm ⟨P,
        (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP⟩‖) := by
      exact mul_le_mul_of_nonneg_right hfac
        (mul_nonneg hB.le (norm_nonneg _))
    _ ≤ F * (B * (C * Real.sqrt (∫ y in E,
        |euclideanPolynomialEval P y| ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hnorm hB.le) hF.le
    _ = (F * B * C) * Real.sqrt (∫ y in E,
        |euclideanPolynomialEval P y| ^ 2) := by ring

 /-- Affine transfer from the unit-ball coefficient estimate to arbitrary balls.
 
 The source calculation pulls a null-measurable subset of `Metric.ball a ρ` back
 along `y ↦ a + ρ • y`, uses the positive Jacobian `ρ ^ N`, and applies the
 unit-ball estimate to the pullback polynomial.  The polynomial affine identity
 scales the ordered mixed partial by `ρ ^ ∑ i, β i`; the integral square root
 contributes `ρ ^ (-N / 2)`, and the positive-radius real-power identities combine
 these factors into the stated exponent.  Null measurability pulls back by
 quasi-measure preservation, and continuity on the compact closed ball supplies
 integrability.  Source: Campanato (1964), Lemma [2.I], equations (2.7)–(2.12),
 pp.140–143. -/
theorem campanato_affine_normalization_core_transfer_g3
    (N n : ℕ) (_hN : 1 ≤ N) (_hN0 : 0 ≤ N) (A : ℝ) (hA : 0 < A)
    (_hAv : A ≤ volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))
    (_hmixed : ∀ (P : MvPolynomial (Fin N) ℝ) (β : Fin N →₀ ℕ),
      euclideanPolynomialMixedPartial P (fun i ↦ β i) 0 =
        (β.prod (fun _ k ↦ k.factorial) : ℝ) * P.coeff β)
    (hunit :
      ∃ K : ℝ, 0 < K ∧
        ∀ (P : MvPolynomial (Fin N) ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
          P.totalDegree ≤ n → NullMeasurableSet E volume →
          E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
          A ≤ volume.real E →
          ∀ β : Fin N → ℕ, (∑ i, β i) ≤ n →
            |euclideanPolynomialMixedPartial P β 0| ≤
              K * Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (a : EuclideanSpace ℝ (Fin N))
        (ρ : ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
        P.totalDegree ≤ n → 0 < ρ → NullMeasurableSet E volume →
        E ⊆ Metric.ball a ρ → A * ρ ^ N ≤ volume.real E →
        ∀ β : Fin N → ℕ, (∑ i, β i) ≤ n →
          |euclideanPolynomialMixedPartial P β a| ≤
            K * Real.rpow ρ (-((∑ i, β i) : ℝ) - (N : ℝ) / 2) *
              Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
  obtain ⟨K, hK, hunit⟩ := hunit
  refine ⟨K, hK, ?_⟩
  intro P a ρ E hP hρ hE hEB hvol β hβ
  let vars : Fin N → MvPolynomial (Fin N) ℝ :=
    fun i ↦ MvPolynomial.C (a i) + MvPolynomial.C ρ * MvPolynomial.X i
  let Q := MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin N) ℝ) vars P
  let T : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun y ↦ a + ρ • y
  let E' := T ⁻¹' E
  have hQeval (y : EuclideanSpace ℝ (Fin N)) :
      euclideanPolynomialEval Q y = euclideanPolynomialEval P (T y) := by
    simp only [euclideanPolynomialEval, Q, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_eval₂]
    congr 1
    · ext c
      simp
    · funext i
      simp [vars, T]
  have hQdeg : Q.totalDegree ≤ n := by
    have hv (i : Fin N) : (vars i).totalDegree ≤ 1 := by
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · simp
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        simp
    change (MvPolynomial.eval₂Hom _ vars P).totalDegree ≤ n
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro s hs
    rw [MvPolynomial.eval₂Hom_monomial]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      ∑ i ∈ s.support, (vars i ^ s i).totalDegree ≤ ∑ i ∈ s.support, s i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hv i))
      _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hs
      _ ≤ n := hP
  have hT : Measure.QuasiMeasurePreserving T volume volume :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul volume hρ.ne')
  have hE' : NullMeasurableSet E' volume := hE.preimage hT
  have hE'B : E' ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 := by
    intro y hy
    have hy' := hEB hy
    change dist (a + ρ • y) a < ρ at hy'
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ] at hy'
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (lt_of_mul_lt_mul_left (show ρ * ‖y‖ < ρ * 1 by simpa using hy') hρ.le).le
  have hmeasure : volume E' = ENNReal.ofReal ((ρ ^ N)⁻¹) * volume E := by
    change volume ((fun y ↦ ρ • y) ⁻¹' ((fun z ↦ a + z) ⁻¹' E)) = _
    rw [Measure.addHaar_preimage_smul volume hρ.ne', measure_preimage_add]
    simp [abs_of_pos (inv_pos.mpr (pow_pos hρ N))]
  have hreal : volume.real E' = (ρ ^ N)⁻¹ * volume.real E := by
    simp only [Measure.real, hmeasure, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hρ.le N))]
  have hvol' : A ≤ volume.real E' := by
    rw [hreal]
    have hh := mul_le_mul_of_nonneg_left hvol (inv_nonneg.mpr (pow_nonneg hρ.le N))
    calc
      A = (ρ ^ N)⁻¹ * (A * ρ ^ N) := by field_simp
      _ ≤ (ρ ^ N)⁻¹ * volume.real E := hh
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin N) ↦ |euclideanPolynomialEval P y| ^ 2) := by
    exact ((P.continuous_eval.comp (by fun_prop)).abs).pow 2
  have hint : IntegrableOn (fun y ↦ |euclideanPolynomialEval P y| ^ 2) E volume :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall a ρ)).mono_set
      (hEB.trans Metric.ball_subset_closedBall)
  have hI := campanato_affine_setIntegral_transport_g3 N a ρ
    (fun y ↦ |euclideanPolynomialEval P y| ^ 2) E hρ hE hint
  change (∫ y in E, |euclideanPolynomialEval P y| ^ 2) =
    ρ ^ N * (∫ y in E', |euclideanPolynomialEval P (T y)| ^ 2) at hI
  simp_rw [← hQeval] at hI
  have hroot : Real.sqrt (∫ y in E', |euclideanPolynomialEval Q y| ^ 2) =
      Real.rpow ρ (-(N : ℝ) / 2) * Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
    rw [hI, Real.sqrt_mul (pow_nonneg hρ.le N)]
    have hs : Real.sqrt (ρ ^ N) = Real.rpow ρ ((N : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      congr 1
      ring
    have hp : Real.rpow ρ (-(N : ℝ) / 2) * Real.rpow ρ ((N : ℝ) / 2) = 1 := by
      calc
        _ = Real.rpow ρ (-(N : ℝ) / 2 + (N : ℝ) / 2) := (Real.rpow_add hρ _ _).symm
        _ = 1 := by rw [show -(N : ℝ) / 2 + (N : ℝ) / 2 = 0 by ring]; exact Real.rpow_zero ρ
    rw [hs, ← mul_assoc, hp, one_mul]
  have hu := hunit Q E' hQdeg hE' hE'B hvol' β hβ
  have hd := euclideanPolynomialMixedPartial_affine_identity_g3 P a ρ β
  change euclideanPolynomialMixedPartial Q β 0 =
    ρ ^ (∑ i, β i) * euclideanPolynomialMixedPartial P β a at hd
  rw [campanato_affine_derivative_rescale_g3 ρ hρ _ _ _ hd]
  simp only [← Nat.cast_sum]
  calc
    Real.rpow ρ (-((∑ i, β i : ℕ) : ℝ)) * |euclideanPolynomialMixedPartial Q β 0| ≤
        Real.rpow ρ (-((∑ i, β i : ℕ) : ℝ)) *
          (K * Real.sqrt (∫ y in E', |euclideanPolynomialEval Q y| ^ 2)) :=
      mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hρ.le _)
    _ = K * Real.rpow ρ (-((∑ i, β i : ℕ) : ℝ) - (N : ℝ) / 2) *
        Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
      rw [hroot]
      have hp : Real.rpow ρ (-((∑ i, β i : ℕ) : ℝ) - (N : ℝ) / 2) =
          Real.rpow ρ (-((∑ i, β i : ℕ) : ℝ)) * Real.rpow ρ (-(N : ℝ) / 2) := by
        rw [show -((∑ i, β i : ℕ) : ℝ) - (N : ℝ) / 2 =
          -((∑ i, β i : ℕ) : ℝ) + (-(N : ℝ) / 2) by ring]
        exact Real.rpow_add hρ _ _
      rw [hp]
      ring

 /-- Core Campanato coefficient-to-derivative normalization, combining the
unit-ball coefficient estimate with exact affine transport. -/
theorem campanato_affine_normalization_core_g3
    (N n : ℕ) (hN : 1 ≤ N) (hN0 : 0 ≤ N) (A : ℝ) (hA : 0 < A)
    (hAv : A ≤ volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))
    (hmixed : ∀ (P : MvPolynomial (Fin N) ℝ) (β : Fin N →₀ ℕ),
      euclideanPolynomialMixedPartial P (fun i ↦ β i) 0 =
        (β.prod (fun _ k ↦ k.factorial) : ℝ) * P.coeff β)
    (hlower :
      ∃ d : ℕ,
        ∃ e : (Fin d → ℝ) ≃ₗ[ℝ]
          ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n),
        ∃ c : ℝ, 0 < c ∧
          ∀ v : Fin d → ℝ, v ∈ Metric.sphere (0 : Fin d → ℝ) 1 →
          ∀ E : Set (EuclideanSpace ℝ (Fin N)),
            NullMeasurableSet E volume →
            E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
            A ≤ volume.real E →
            c ≤ ∫ x in E,
              |MvPolynomial.eval (fun i ↦ x i) ((e v).val)| ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (a : EuclideanSpace ℝ (Fin N))
        (ρ : ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
        P.totalDegree ≤ n → 0 < ρ → NullMeasurableSet E volume →
        E ⊆ Metric.ball a ρ → A * ρ ^ N ≤ volume.real E →
        ∀ β : Fin N → ℕ, (∑ i, β i) ≤ n →
          |euclideanPolynomialMixedPartial P β a| ≤
            K * Real.rpow ρ (-((∑ i, β i) : ℝ) - (N : ℝ) / 2) *
              Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
  have hunit := campanato_affine_normalization_unit_ball_coeff_derivative_g3
    N n hN hN0 A hA hAv hmixed hlower
  exact campanato_affine_normalization_core_transfer_g3
    N n hN hN0 A hA hAv hmixed hunit

/-- Campanato's affine normalization estimate after the unit-ball coefficient
minimum has been supplied.

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], equations (2.7)--(2.12), pp.140--143.  The proof applies the
normalized coefficient lower bound to the affine preimage of `E`, transports
the square integral by the positive Jacobian, and uses the mixed-partial
scaling identity.  The completed-measure representative and all positivity
side conditions are retained in the statement.  The remaining arithmetic and
finite-derivative composition is isolated here as a named Stage 1 obligation.
-/
theorem campanato_affine_normalization_estimate_g3
    (N n : ℕ) (hN : 1 ≤ N) (A : ℝ) (hA : 0 < A)
    (hAv : A ≤ volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))
    (_htransport :
      ∀ (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ)
        (f : EuclideanSpace ℝ (Fin N) → ℝ)
        (E : Set (EuclideanSpace ℝ (Fin N))),
        0 < ρ → NullMeasurableSet E volume → IntegrableOn f E volume →
          (∫ x in E, f x) =
            ρ ^ N * ∫ y in ((fun y ↦ a + ρ • y) ⁻¹' E), f (a + ρ • y))
    (hlower :
      ∃ d : ℕ,
        ∃ e : (Fin d → ℝ) ≃ₗ[ℝ]
          ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n),
        ∃ c : ℝ, 0 < c ∧
          ∀ v : Fin d → ℝ, v ∈ Metric.sphere (0 : Fin d → ℝ) 1 →
          ∀ E : Set (EuclideanSpace ℝ (Fin N)),
            NullMeasurableSet E volume →
            E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 →
            A ≤ volume.real E →
            c ≤ ∫ x in E,
              |MvPolynomial.eval (fun i ↦ x i) ((e v).val)| ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (a : EuclideanSpace ℝ (Fin N))
        (ρ : ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
        P.totalDegree ≤ n → 0 < ρ → NullMeasurableSet E volume →
        E ⊆ Metric.ball a ρ → A * ρ ^ N ≤ volume.real E →
        ∀ β : Fin N → ℕ, (∑ i, β i) ≤ n →
          |euclideanPolynomialMixedPartial P β a| ≤
            K * Real.rpow ρ (-((∑ i, β i) : ℝ) - (N : ℝ) / 2) *
              Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
  exact campanato_affine_normalization_core_g3 N n hN (Nat.zero_le N) A hA hAv
    (fun P β ↦ campanato_mixed_partial_coeff_at_zero_g3 P β) hlower


end HolomorphicAnosov.Analysis.Regularity
