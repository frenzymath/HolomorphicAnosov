import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Unit-ball coefficient estimate for bounded-degree real polynomials

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], equations (2.3), (2.10), (2.11), printed pp.140–142.
DAG node: `analysis.polynomial_unit_ball_coefficient_estimate_g3`.
The ball uses the original Euclidean norm and its Lebesgue measure. The coefficient
is multiplied by the full multi-index factorial, not a divided-derivative convention.
-/

open MeasureTheory
open scoped BoundedContinuousFunction
namespace HolomorphicAnosov

/-- Coefficients of bounded-degree polynomials are bounded by their unit-ball L² norm.
Source: Campanato (1964), Lemma [2.I], equations (2.3), (2.10), (2.11), printed pp.140–142,
specialized to the whole unit ball and q = 2.

Proof: specialize Campanato's normalized coefficient argument to q = 2 and fixed
weight 1 on the entire unit ball. Index the monomials of total order at most n by
a finite set I and give their real coefficient space the Euclidean norm. Mathlib's
basis of the polynomial subspace supported on I identifies this space with the
polynomials of degree at most n. Evaluation on the closed ball is a continuous
linear map; restriction to the open ball followed by the bounded-continuous-function
map into L² gives a linear map J. Its squared norm is continuous and equals the
integral in the statement, by the L² inner-product and subtype integral identities.

This squared norm is positive for every nonzero coefficient vector. Indeed, the
open-ball measure is finite and positive on nonempty relatively open sets, so a
continuous function with zero L² class vanishes throughout the ball. Polynomial
evaluation is real analytic; the identity theorem and polynomial extensionality
then make the polynomial, and its coefficient vector, zero. This supplies the
positivity step used in Campanato's (2.10) for the whole-ball specialization.

The Euclidean unit sphere of monomial coefficients is nonempty and compact, so
the continuous squared L² norm attains a strictly positive minimum there. Normalize
a nonzero coefficient vector by its norm and use homogeneity to obtain
‖c‖ ≤ ‖J(c₀)‖⁻¹ ‖J(c)‖, where c₀ is a minimizer. Each monomial coefficient has
absolute value at most ‖c‖. The finite sum A of the factorial products β! bounds
each such factor. Thus (A + 1) / ‖J(c₀)‖ is a positive uniform constant K.
Zero polynomials and n = 0 are included. -/
theorem polynomial_unit_ball_coefficient_estimate (N n : ℕ) (_hN : 1 ≤ N) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ), P.totalDegree ≤ n →
        ∀ (β : Fin N →₀ ℕ), (β.sum fun _ k ↦ k) ≤ n →
          |(β.prod (fun _ k ↦ k.factorial) : ℝ) * P.coeff β| ≤
            K * Real.sqrt (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1,
              |MvPolynomial.eval (fun i ↦ y i) P| ^ 2 ∂volume) := by
  -- Use the source monomial coefficient sphere; L² expresses its continuous integral.
  classical
  let I := ↥({β : Fin N →₀ ℕ | (β.sum fun _ k ↦ k) ≤ n})
  have hfin : Finite I := by
    have hbounded : Set.Finite {β : Fin N →₀ ℕ | ∀ i, β i ≤ n} :=
      (Set.Finite.pi' fun _ : Fin N ↦ Set.finite_le_nat n).preimage DFunLike.coe_injective.injOn
    apply Set.Finite.to_subtype (s := {β : Fin N →₀ ℕ | (β.sum fun _ k ↦ k) ≤ n})
    apply hbounded.subset
    intro β hβ i
    exact (Finsupp.single_eval_le_sum β (g := id) rfl (fun m ↦ Nat.zero_le m) i).trans hβ
  let := hfin
  let : Fintype I := Fintype.ofFinite I
  let C := EuclideanSpace ℝ I
  let e : C ≃ₗ[ℝ] ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n) :=
    (WithLp.linearEquiv 2 ℝ (I → ℝ)).trans
      (MvPolynomial.basisRestrictSupport ℝ
        {β : Fin N →₀ ℕ | (β.sum fun _ k ↦ k) ≤ n}).equivFun.symm
  let T₀ : C →ₗ[ℝ] C(↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1), ℝ) :=
    { toFun := fun c ↦
        ⟨fun x ↦ MvPolynomial.eval (fun i ↦ x.val i) (e c).val,
          ((AnalyticOnNhd.eval_continuousLinearMap'
            (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)
            (e c).val).continuous).comp continuous_subtype_val⟩
      map_add' := by
        intro c c'
        ext x
        change MvPolynomial.eval _ (e (c + c')).val =
          MvPolynomial.eval _ (e c).val + MvPolynomial.eval _ (e c').val
        simp
      map_smul' := by
        intro r c
        ext x
        change MvPolynomial.eval _ (e (r • c)).val =
          r • MvPolynomial.eval _ (e c).val
        rw [map_smul]
        exact MvPolynomial.eval₂Hom_smul (RingHom.id ℝ) _ r (e c).val }
  let T : C →L[ℝ] C(↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1), ℝ) :=
    ⟨T₀, T₀.continuous_of_finiteDimensional⟩
  have hT (c : C) (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)) :
      T c x = MvPolynomial.eval (fun i ↦ x.val i) (e c).val := rfl
  let E := EuclideanSpace ℝ (Fin N)
  let B := ↥(Metric.ball (0 : E) 1)
  let μ : Measure B := volume.comap Subtype.val
  have hfinite : IsFiniteMeasure μ := by
    constructor
    change (volume.comap (Subtype.val : B → E)) Set.univ < ⊤
    rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply]
    simpa only [Set.image_univ, Subtype.range_coe] using
      (measure_ball_lt_top (μ := (volume : Measure E)) (x := 0) (r := 1))
  let := hfinite
  let : μ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap volume
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  let inclusion : C(B, ↥(Metric.closedBall (0 : E) 1)) :=
    ⟨fun x ↦ ⟨x.val, Metric.ball_subset_closedBall x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let S : C →ₗ[ℝ] (B →ᵇ ℝ) :=
    { toFun := fun c ↦ (BoundedContinuousFunction.mkOfCompact (T c)).compContinuous inclusion
      map_add' := by intros; ext x; simp
      map_smul' := by intros; ext x; simp }
  have hS (c : C) (x : B) : S c x = MvPolynomial.eval (fun i ↦ x.val i) (e c).val :=
    hT c (inclusion x)
  let J : C →ₗ[ℝ] Lp ℝ 2 μ :=
    (BoundedContinuousFunction.toLp 2 μ ℝ).toLinearMap.comp S
  have hJinj : Function.Injective J := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have hsc : S c = 0 := (BoundedContinuousFunction.toLp_injective μ)
      (show BoundedContinuousFunction.toLp 2 μ ℝ (S c) =
        BoundedContinuousFunction.toLp 2 μ ℝ 0 by simpa [J] using hc)
    have hvan : ∀ x ∈ Metric.ball (0 : E) 1,
        MvPolynomial.eval (fun i ↦ x i) (e c).val = 0 := by
      intro x hx
      simpa [hS] using
        congrArg (fun f : B →ᵇ ℝ ↦ f ⟨x, hx⟩) hsc
    have ha := AnalyticOnNhd.eval_continuousLinearMap'
      (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i) (e c).val
    have hall : ∀ x : E, MvPolynomial.eval (fun i ↦ x i) (e c).val = 0 := by
      have hh := ha.eq_of_eventuallyEq
        (analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : E ↦ (0 : ℝ)) Set.univ)
        (z₀ := (0 : E)) (by
          filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
          exact hvan x hx)
      exact fun x ↦ congrFun hh x
    have hp : (e c).val = 0 := MvPolynomial.funext fun x ↦ by
      simpa using hall (WithLp.toLp 2 x)
    apply e.injective
    apply Subtype.ext
    simpa using hp
  have hnorm (c : C) : ‖J c‖ = Real.sqrt
      (∫ y in Metric.ball (0 : E) 1, |MvPolynomial.eval (fun i ↦ y i) (e c).val| ^ 2) := by
    have hh := BoundedContinuousFunction.inner_toLp μ (S c) (S c)
    have hi : ‖J c‖ ^ 2 =
        ∫ y in Metric.ball (0 : E) 1, |MvPolynomial.eval (fun i ↦ y i) (e c).val| ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ (BoundedContinuousFunction.toLp 2 μ ℝ (S c))
        (BoundedContinuousFunction.toLp 2 μ ℝ (S c)) = _
      rw [hh]
      simp only [RCLike.conj_to_real, hS, ← sq, sq_abs]
      exact integral_subtype_comap (measurableSet_ball (x := (0 : E)) (ε := 1))
        (fun y : E ↦ MvPolynomial.eval (fun i ↦ y i) (e c).val ^ 2)
    rw [← hi, Real.sqrt_sq (norm_nonneg _)]
  -- Campanato (2.3)--(2.10), with fixed weight 1: minimize the squared L² norm
  -- on the Euclidean sphere of monomial coefficients.
  have hsphere : (Metric.sphere (0 : C) 1).Nonempty := by
    refine ⟨PiLp.single 2 (⟨0, by simp⟩ : I) (1 : ℝ), ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right]
    rw [PiLp.norm_single]
    norm_num
  obtain ⟨c₀, hc₀, hmin⟩ := (isCompact_sphere (0 : C) 1).exists_isMinOn hsphere
    ((J.continuous_of_finiteDimensional.norm.pow 2).continuousOn)
  have hc₀norm : ‖c₀‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hc₀
  have hjpos : 0 < ‖J c₀‖ := norm_pos_iff.mpr (by
    intro h
    have : c₀ = 0 := hJinj (by simpa using h)
    simp [this] at hc₀norm)
  let K : ℝ := ‖J c₀‖⁻¹
  have hK : 0 < K := inv_pos.mpr hjpos
  have hbound (c : C) : ‖c‖ ≤ K * ‖J c‖ := by
    by_cases hc : c = 0
    · simp [hc]
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hu : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : C) 1 := by
      simp [Metric.mem_sphere, dist_zero_right, norm_smul, hcpos.ne']
    have hm := hmin hu
    change ‖J c₀‖ ^ 2 ≤ ‖J (‖c‖⁻¹ • c)‖ ^ 2 at hm
    have hsq : ‖J c₀‖ ^ 2 ≤ (‖c‖⁻¹ * ‖J c‖) ^ 2 := by
      simpa only [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos] using hm
    have hmnorm : ‖J c₀‖ ≤ ‖c‖⁻¹ * ‖J c‖ := by
      have : 0 ≤ ‖c‖⁻¹ * ‖J c‖ := mul_nonneg (inv_nonneg.mpr hcpos.le) (norm_nonneg _)
      nlinarith [norm_nonneg (J c₀)]
    have hmul := mul_le_mul_of_nonneg_right hmnorm hcpos.le
    have hmul' : ‖c‖ * ‖J c₀‖ ≤ ‖J c‖ := calc
      _ = ‖J c₀‖ * ‖c‖ := mul_comm _ _
      _ ≤ (‖c‖⁻¹ * ‖J c‖) * ‖c‖ := hmul
      _ = ‖J c‖ := by field_simp
    calc
      ‖c‖ ≤ ‖J c‖ / ‖J c₀‖ := (le_div_iff₀ hjpos).mpr hmul'
      _ = K * ‖J c‖ := by rw [div_eq_mul_inv, mul_comm]
  let A : ℝ := ∑ β : I, (β.val.prod (fun _ k ↦ k.factorial) : ℝ)
  have hAnonneg : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro β _
    exact Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _
  refine ⟨(A + 1) * K, mul_pos (by positivity) hK, ?_⟩
  intro P hP β hβ
  let p : ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n) :=
    ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hP⟩
  let c := e.symm p
  have hc : (e c).val = P := congrArg Subtype.val (e.apply_symm_apply p)
  have hcoeffeq : c (⟨β, hβ⟩ : I) = P.coeff β := by rfl
  have hcoeff : |P.coeff β| ≤ ‖c‖ := by
    have hh := PiLp.norm_apply_le c (⟨β, hβ⟩ : I)
    simpa only [hcoeffeq, Real.norm_eq_abs] using hh
  have hfac : (β.prod (fun _ k ↦ k.factorial) : ℝ) ≤ A :=
    Finset.single_le_sum (f := fun γ : I ↦ (γ.val.prod (fun _ k ↦ k.factorial) : ℝ))
      (fun γ _ ↦ Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (Finset.mem_univ (⟨β, hβ⟩ : I))
  calc
    _ = (β.prod (fun _ k ↦ k.factorial) : ℝ) * |P.coeff β| := by
      rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)]
    _ ≤ (A + 1) * ‖c‖ := mul_le_mul (by linarith) hcoeff (abs_nonneg _) (by positivity)
    _ ≤ (A + 1) * (K * ‖J c‖) := mul_le_mul_of_nonneg_left (hbound c) (by positivity)
    _ = ((A + 1) * K) * Real.sqrt
        (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1,
          |MvPolynomial.eval (fun i ↦ y i) P| ^ 2) := by
      rw [hnorm, hc, mul_assoc]

end HolomorphicAnosov

