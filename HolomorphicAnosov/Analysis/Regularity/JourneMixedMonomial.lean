import HolomorphicAnosov.Analysis.Regularity.JourneFiniteProductHolder
import HolomorphicAnosov.Analysis.Regularity.JournePolynomialTopDerivative
import HolomorphicAnosov.Analysis.Regularity.JourneBlockMonomialSpace
import HolomorphicAnosov.Analysis.Regularity.JourneRescaledGraph
import Mathlib.Algebra.BigOperators.Fin

/-!
This file proves Hölder estimates for mixed monomials along small-slope graphs (Journé, 1988).
-/ 

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Journé's normalized mixed monomial estimate. (Journé, 1988) -/
theorem mixed_monomial_top_holder_small
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n a b : ℕ} (hn : 1 ≤ n) (hb : b ≤ n)
    {S : Set E} (hS : IsOpen S) (hconv : Convex ℝ S)
    {α M δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (φ : Fin a → E → ℝ) (c : Fin a → ℝ) (L : E →L[ℝ] (Fin b → ℝ))
    (hφ : ∀ i, HasFiniteHolderBounds n α M (φ i) S)
    (hc : ∀ i, |c i| ≤ M)
    (hd : ∀ i, HasFiniteHolderBounds n α δ (fun x ↦ φ i x-c i) S)
    (hL : ∀ j, HasFiniteHolderBounds n α M (fun x ↦ L x j) S) :
    let F : E → ℝ := fun x ↦ (∏ i, φ i x)*(∏ j, L x j)
    ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n F x-iteratedFDeriv ℝ n F y‖ ≤
        ((2:ℝ)^(2*n+1)*(a:ℝ)*((2:ℝ)^(2*n+1)*M)^a*
          ((2:ℝ)^(2*n+1)*M)^b*δ)*‖x-y‖^α := by
  classical
  let Q : ℝ := 2^(2*n+1)
  have hQ : 0 ≤ Q := by positivity
  have hM0 : 0 ≤ M := by linarith
  let U : E → ℝ := fun x ↦ ∏ i, φ i x
  let V : E → ℝ := fun x ↦ ∏ j, L x j
  let d : ℝ := ∏ i, c i
  let R : E → ℝ := fun x ↦ (U x-d)*V x
  let G : E → ℝ := fun x ↦ d*V x
  have hUdiff : HasFiniteHolderBounds n α ((a:ℝ)*(Q*M)^a*δ) (fun x ↦ U x-d) S := by
    have H := finite_product_difference_holder_bound hn hS hconv hα hα1 hM hδ φ
      (fun i _ ↦ c i) (List.ofFn (fun i : Fin a ↦ i))
      (fun i _ ↦ hφ i)
      (fun i _ ↦ (finiteHolderBounds_const n hn α S (c i)).mono_bound (hc i))
      (fun i _ ↦ hd i)
    simpa [U,d,Q,List.map_ofFn,Function.comp_def,Fin.prod_ofFn] using H
  have hV : HasFiniteHolderBounds n α ((Q*M)^b) V S := by
    have H := finite_product_holder_bound hn hS hconv hα hα1 hM (fun j x ↦ L x j)
      (List.ofFn (fun j : Fin b ↦ j)) (fun j _ ↦ hL j)
    simpa [V,Q,List.map_ofFn,Function.comp_def,Fin.prod_ofFn] using H
  have hR := scalar_mul_holder_bound hS hconv hα hα1 (by positivity) (by positivity) hUdiff hV
  let P : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ ℝ) ℝ :=
    d • ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin b) ℝ
  have hG : G = P ∘ L := by funext x; simp [G,V,P,smul_eq_mul]
  have hGc : ContDiff ℝ n G := by rw [hG]; exact P.contDiff.comp L.contDiff
  have hGn (x y : E) : iteratedFDeriv ℝ n G x = iteratedFDeriv ℝ n G y := by
    rw [hG]
    exact multilinear_polynomial_top_derivative_const hb P L x y
  have hF : (fun x ↦ (∏ i, φ i x)*(∏ j, L x j)) = fun x ↦ R x+G x := by
    funext x
    dsimp [R,G,U,V]
    ring
  dsimp only
  intro x hx y hy
  rw [hF]
  have he (z : E) (hz : z ∈ S) :
      iteratedFDeriv ℝ n (fun x ↦ R x+G x) z =
        iteratedFDeriv ℝ n R z+iteratedFDeriv ℝ n G z :=
    iteratedFDeriv_add_apply (hR.1.contDiffAt (hS.mem_nhds hz)) hGc.contDiffAt
  rw [he x hx,he y hy,hGn x y,add_sub_add_right_eq_sub]
  convert hR.2.2 x hx y hy using 1; dsimp [Q]; ring

/-- A full Hölder bound for a genuine block monomial restricted to a graph. -/
theorem block_bimonomial_graph_holder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q n : ℕ} (hn : 1 ≤ n) (i : BlockBidegreeIndex p q n)
    {S : Set E} (hS : IsOpen S) (hconv : Convex ℝ S)
    {α M : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M)
    (φ : E → Block p) (ψ : E → Block q)
    (hφ : ∀ j, HasFiniteHolderBounds n α M (fun x ↦ φ x j) S)
    (hψ : ∀ j, HasFiniteHolderBounds n α M (fun x ↦ ψ x j) S) :
    HasFiniteHolderBounds n α
      ((2:ℝ)^(2*n+1)*((2:ℝ)^(2*n+1)*M)^n*((2:ℝ)^(2*n+1)*M)^n)
      (fun x ↦ blockBimonomial i (φ x,ψ x)) S := by
  classical
  obtain ⟨A,hA,heA⟩ := monomial_coordinate_factors i.1.val
  obtain ⟨B,hB,heB⟩ := monomial_coordinate_factors i.2.val
  have HA := finite_product_holder_bound hn hS hconv hα hα1 hM
    (fun j x ↦ φ x j) A (fun j _ ↦ hφ j)
  have HB := finite_product_holder_bound hn hS hconv hα hα1 hM
    (fun j x ↦ ψ x j) B (fun j _ ↦ hψ j)
  have H := scalar_mul_holder_bound hS hconv hα hα1 (by positivity) (by positivity) HA HB
  let Q : ℝ := 2^(2*n+1)
  have hQM : 1 ≤ Q*M := by
    have : 1 ≤ Q := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num)
    nlinarith
  have hAn : A.length ≤ n := hA ▸ i.1.property
  have hBn : B.length ≤ n := hB ▸ i.2.property
  have hbound : Q*(Q*M)^A.length*(Q*M)^B.length ≤ Q*(Q*M)^n*(Q*M)^n :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQM hAn) (by positivity))
      (pow_le_pow_right₀ hQM hBn) (by positivity) (by positivity)
  have H' := H.mono_bound hbound
  have he : (fun x ↦ blockBimonomial i (φ x,ψ x)) =
      fun x ↦ (A.map (fun j ↦ φ x j)).prod*(B.map (fun j ↦ ψ x j)).prod := by
    funext x
    simp only [blockBimonomial,heA,heB]
    exact congrArg₂ (·*·) (Fin.prod_univ_fun_getElem A (fun j ↦ φ x j))
      (Fin.prod_univ_fun_getElem B (fun j ↦ ψ x j))
  rw [he]
  exact H'

/-- Apply the repeated-factor estimate to an actual block monomial indexed by exponent vectors. -/
theorem block_bimonomial_graph_top_holder_small
    {p q n : ℕ} (hn : 1 ≤ n) (i : BlockBidegreeIndex p q n)
    {S : Set (Block q)} (hS : IsOpen S) (hconv : Convex ℝ S)
    {α M δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (φ : Block q → Block p) (c : Block p)
    (hφ : ∀ j, HasFiniteHolderBounds n α M (fun x ↦ φ x j) S)
    (hc : ∀ j, |c j| ≤ M)
    (hd : ∀ j, HasFiniteHolderBounds n α δ (fun x ↦ φ x j-c j) S)
    (hL : ∀ j, HasFiniteHolderBounds n α M (fun x : Block q ↦ x j) S) :
    ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) x-
        iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) y‖ ≤
        ((2:ℝ)^(2*n+1)*((i.1.val.sum fun _ e ↦ e : ℕ):ℝ)*
          ((2:ℝ)^(2*n+1)*M)^(i.1.val.sum fun _ e ↦ e)*
          ((2:ℝ)^(2*n+1)*M)^(i.2.val.sum fun _ e ↦ e)*δ)*‖x-y‖^α := by
  classical
  obtain ⟨A,hA,heA⟩ := monomial_coordinate_factors i.1.val
  obtain ⟨B,hB,heB⟩ := monomial_coordinate_factors i.2.val
  let L : Block q →L[ℝ] (Fin B.length → ℝ) :=
    ContinuousLinearMap.pi fun j ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin q ↦ ℝ) (B.get j)
  have hBn : B.length ≤ n := hB ▸ i.2.property
  have H := mixed_monomial_top_holder_small hn hBn hS hconv hα hα1 hM hδ
    (fun j x ↦ φ x (A.get j)) (fun j ↦ c (A.get j)) L
    (fun j ↦ hφ (A.get j)) (fun j ↦ hc (A.get j)) (fun j ↦ hd (A.get j))
    (fun j ↦ hL (B.get j))
  have he : (fun x ↦ blockBimonomial i (φ x,x)) =
      fun x ↦ (∏ j : Fin A.length, φ x (A.get j))*(∏ j : Fin B.length, L x j) := by
    funext x
    simp only [blockBimonomial,heA,heB]
    rfl
  rw [he]
  simpa only [hA,hB] using H

/-- Coordinate projections of a Euclidean-valued function do not enlarge its full finite Hölder bound. -/
theorem block_coordinate_holder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d n : ℕ} {α K : ℝ} (hK : 0 ≤ K) {S : Set E} (hS : IsOpen S)
    {f : E → Block d} (hf : HasFiniteHolderBounds n α K f S) (j : Fin d) :
    HasFiniteHolderBounds n α K (fun x ↦ f x j) S := by
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) j
  have hp : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul,P,PiLp.proj_apply] using PiLp.norm_apply_le x j
  exact (hf.clm_comp hS P).mono_bound (mul_le_of_le_one_left hK hp)

/-- The normalized graph estimate restores the exact physical-scale power for the actual bidegree monomial, in the original graph variables. -/
theorem block_bimonomial_scaled_graph_top_holder
    {p q n : ℕ} (hn : 1 ≤ n) (i : BlockBidegreeIndex p q n)
    {S : Set (Block q)} (hS : IsOpen S) (hconv : Convex ℝ S)
    {α M δ t : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 1 ≤ M)
    (hδ : 0 ≤ δ) (ht : 0 < t) (φ : Block q → Block p) (c : Block p)
    (hφ : ∀ j, HasFiniteHolderBounds n α M (fun x ↦ (t⁻¹ • φ (t • x)) j) S)
    (hc : ∀ j, |c j| ≤ M)
    (hd : ∀ j, HasFiniteHolderBounds n α δ (fun x ↦ (t⁻¹ • φ (t • x)) j-c j) S)
    (hL : ∀ j, HasFiniteHolderBounds n α M (fun x : Block q ↦ x j) S) :
    ContDiffOn ℝ n (fun x ↦ blockBimonomial i (φ x,x)) ((fun x ↦ t⁻¹ • x) ⁻¹' S) ∧
      ∀ x, t⁻¹ • x ∈ S → ∀ y, t⁻¹ • y ∈ S →
        ‖iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) x-
          iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) y‖ ≤
          (t^((blockBidegree i:ℝ)-(n:ℝ)-α)*
            ((2:ℝ)^(2*n+1)*((i.1.val.sum fun _ e ↦ e : ℕ):ℝ)*
              ((2:ℝ)^(2*n+1)*M)^(i.1.val.sum fun _ e ↦ e)*
              ((2:ℝ)^(2*n+1)*M)^(i.2.val.sum fun _ e ↦ e)*δ))*‖x-y‖^α := by
  let Φ := fun x ↦ t⁻¹ • φ (t • x)
  let F := fun x ↦ blockBimonomial i (Φ x,x)
  let f := fun x ↦ blockBimonomial i (φ x,x)
  have hnorm : (fun x ↦ (t^(blockBidegree i))⁻¹*f (t • x)) = F := by
    funext x
    have he : (φ (t • x),t • x) = t • (Φ x,x) := by
      simp [Φ,Prod.smul_mk,smul_smul,ht.ne']
    dsimp [f,F]
    rw [he,block_bimonomial_homogeneous]
    rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ ht.ne'),one_mul]
  have hfull := block_bimonomial_graph_holder_bound hn i hS hconv hα hα1 hM
    Φ id hφ hL
  have hsmall := block_bimonomial_graph_top_holder_small hn i hS hconv hα hα1 hM hδ
    Φ c hφ hc hd hL
  apply homogeneous_unnormalize_top_holder ht hS f
  · rw [hnorm]
    exact hfull.1
  · rw [hnorm]
    exact hsmall

/-- The physical mixed-monomial estimate follows directly from a uniformly bounded small-slope graph, after choosing a sufficiently small scale. -/
theorem small_slope_block_monomial_top_holder
    {p q n : ℕ} (hn : 1 ≤ n) (i : BlockBidegreeIndex p q n)
    {S : Set (Block q)} (hS : IsOpen S) (hconv : Convex ℝ S) (h0 : (0:Block q) ∈ S)
    {α K ε δ t R : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 < R)
    (hεR : ε*R ≤ δ) (hεδ : ε ≤ δ) (htK : t*K ≤ δ) (hpowK : t^α*K ≤ δ)
    (φ : Block q → Block p) (hφ : HasFiniteHolderBounds n α K φ S)
    (hslope : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ ε)
    (hanchor : ‖φ 0‖ ≤ t*R)
    (hm : ∀ z ∈ Metric.ball (0:Block q) R, t • z ∈ S) :
    ContDiffOn ℝ n (fun x ↦ blockBimonomial i (φ x,x))
      ((fun x ↦ t⁻¹ • x) ⁻¹' Metric.ball 0 R) ∧
      ∀ x, t⁻¹ • x ∈ Metric.ball (0:Block q) R →
      ∀ y, t⁻¹ • y ∈ Metric.ball (0:Block q) R →
        ‖iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) x-
          iteratedFDeriv ℝ n (fun x ↦ blockBimonomial i (φ x,x)) y‖ ≤
          (t^((blockBidegree i:ℝ)-(n:ℝ)-α)*
            ((2:ℝ)^(2*n+1)*((i.1.val.sum fun _ e ↦ e : ℕ):ℝ)*
              ((2:ℝ)^(2*n+1)*(R+1))^(i.1.val.sum fun _ e ↦ e)*
              ((2:ℝ)^(2*n+1)*(R+1))^(i.2.val.sum fun _ e ↦ e)*δ))*‖x-y‖^α := by
  let c := t⁻¹ • φ 0
  have hc : ‖c‖ ≤ R := by
    dsimp [c]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    calc
      t⁻¹*‖φ 0‖ ≤ t⁻¹*(t*R) := mul_le_mul_of_nonneg_left hanchor (by positivity)
      _ = R := by rw [← mul_assoc,inv_mul_cancel₀ ht.ne',one_mul]
  have H := rescaled_graph_holder_small hn hα.le hK hε ht ht1 hR
    hεR hεδ htK hpowK hS hconv h0 hφ hslope hm
  have he : (fun z ↦ t⁻¹ • (φ (t • z)-φ 0)) =
      fun z ↦ t⁻¹ • φ (t • z)-c := by funext z; simp [c,smul_sub]
  have hsum := H.add Metric.isOpen_ball (finiteHolderBounds_const n hn α (Metric.ball 0 R) c)
  have hfull : HasFiniteHolderBounds n α (R+1) (fun z ↦ t⁻¹ • φ (t • z))
      (Metric.ball (0:Block q) R) := by
    have he' : (fun z ↦ t⁻¹ • (φ (t • z)-φ 0)+c) = fun z ↦ t⁻¹ • φ (t • z) := by
      funext z
      simp [c,smul_sub]
    rw [he'] at hsum
    exact hsum.mono_bound (by linarith)
  have hid : HasFiniteHolderBounds n α (R+1) (id : Block q → Block q)
      (Metric.ball 0 R) :=
    (finiteHolderBounds_id_ball n hn α R).mono_bound (max_le (by linarith) (by linarith))
  apply block_bimonomial_scaled_graph_top_holder hn i Metric.isOpen_ball (convex_ball _ _)
    hα hα1 (by linarith) hδ ht φ c
  · intro j
    exact block_coordinate_holder_bound (by linarith) Metric.isOpen_ball hfull j
  · intro j
    exact (show |c j| ≤ ‖c‖ from PiLp.norm_apply_le c j).trans (by linarith)
  · intro j
    rw [he] at H
    exact block_coordinate_holder_bound hδ Metric.isOpen_ball H j
  · intro j
    exact block_coordinate_holder_bound (by linarith) Metric.isOpen_ball hid j

end HolomorphicAnosov.JourneLeafPolynomialApproximation
