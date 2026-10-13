import HolomorphicAnosov.Analysis.Regularity.JournePlaqueHigherHolder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- Exact derivative scaling for scalar multiplication in source and target, with the actual open preimage domain. -/
theorem scalar_rescale_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n j : ℕ} {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ n f S) (hj : j ≤ n)
    (r s : ℝ) {z : E} (hz : r • z ∈ S) :
    iteratedFDeriv ℝ j (fun z ↦ s • f (r • z)) z =
      (s*r^j) • iteratedFDeriv ℝ j f (r • z) := by
  let L : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
  have hopen : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hcomp : ContDiffOn ℝ n (f ∘ L) (L ⁻¹' S) := hf.comp_continuousLinearMap L
  have hat : ContDiffAt ℝ j (f ∘ L) z :=
    (hcomp.contDiffAt (hopen.mem_nhds hz)).of_le (by exact_mod_cast hj)
  have he := L.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn hopen.uniqueDiffOn
    hz (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen _ hopen hz,
    iteratedFDerivWithin_of_isOpen _ hS (show L z ∈ S from hz)] at he
  change iteratedFDeriv ℝ j (fun z ↦ s • (f ∘ L) z) z = _
  rw [iteratedFDeriv_const_smul_apply' hat, he]
  ext v
  change s • (iteratedFDeriv ℝ j f (r • z)) (fun i ↦ r • v i) =
    (s*r^j) • (iteratedFDeriv ℝ j f (r • z)) v
  rw [(iteratedFDeriv ℝ j f (r • z)).map_smul_univ]
  simp [smul_smul]

/-- The highest Hölder seminorm transforms with the full power n+α under scalar changes of the source and target. -/
theorem scalar_rescale_top_holder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α B : ℝ} {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ n f S)
    (hholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y‖ ≤ B*‖x-y‖^α)
    (r s : ℝ) {x y : E} (hx : r • x ∈ S) (hy : r • y ∈ S) :
    ‖iteratedFDeriv ℝ n (fun z ↦ s • f (r • z)) x-
      iteratedFDeriv ℝ n (fun z ↦ s • f (r • z)) y‖ ≤
      (|s| * |r|^n * |r|^α * B)*‖x-y‖^α := by
  rw [scalar_rescale_iteratedFDeriv hS hf le_rfl r s hx,
    scalar_rescale_iteratedFDeriv hS hf le_rfl r s hy,← smul_sub,norm_smul]
  calc
    _ ≤ ‖s*r^n‖*(B*‖r • x-r • y‖^α) :=
      mul_le_mul_of_nonneg_left (hholder _ hx _ hy) (norm_nonneg _)
    _ = _ := by
      rw [← smul_sub,norm_smul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
        norm_mul,norm_pow,Real.norm_eq_abs]
      simp only [Real.norm_eq_abs]
      ring

/-- Undo homogeneous normalization in a scalar function. -/
theorem homogeneous_unnormalize_top_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n d : ℕ} {α B t : ℝ} (ht : 0 < t)
    {S : Set E} (hS : IsOpen S) (f : E → ℝ)
    (hf : ContDiffOn ℝ n (fun x ↦ (t^d)⁻¹*f (t • x)) S)
    (hholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n (fun x ↦ (t^d)⁻¹*f (t • x)) x-
        iteratedFDeriv ℝ n (fun x ↦ (t^d)⁻¹*f (t • x)) y‖ ≤ B*‖x-y‖^α) :
    ContDiffOn ℝ n f ((fun x ↦ t⁻¹ • x) ⁻¹' S) ∧
      ∀ x, t⁻¹ • x ∈ S → ∀ y, t⁻¹ • y ∈ S →
        ‖iteratedFDeriv ℝ n f x-iteratedFDeriv ℝ n f y‖ ≤
          (t^((d:ℝ)-(n:ℝ)-α)*B)*‖x-y‖^α := by
  let F := fun x ↦ (t^d)⁻¹*f (t • x)
  have he : (fun x ↦ (t^d) • F (t⁻¹ • x)) = f := by
    funext x
    simp [F,smul_smul,ht.ne',pow_ne_zero _ ht.ne']
  have hcont : ContDiffOn ℝ n (fun x ↦ (t^d) • F (t⁻¹ • x))
      ((fun x ↦ t⁻¹ • x) ⁻¹' S) :=
    (hf.comp_continuousLinearMap (t⁻¹ • ContinuousLinearMap.id ℝ E)).const_smul (t^d)
  refine ⟨by simpa only [he] using hcont,?_⟩
  intro x hx y hy
  have H := scalar_rescale_top_holder hS hf hholder t⁻¹ (t^d) hx hy
  rw [he] at H
  have hpower : |t^d| * |t⁻¹|^n * |t⁻¹|^α = t^((d:ℝ)-(n:ℝ)-α) := by
    rw [abs_of_pos (pow_pos ht d),abs_of_pos (inv_pos.mpr ht),
      ← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_neg_one t,
      ← Real.rpow_mul ht.le,← Real.rpow_mul ht.le,
      ← Real.rpow_add ht,← Real.rpow_add ht]
    congr 1
    ring
  simpa only [hpower,mul_assoc] using H

/-- The positive-order derivatives of a graph normalized at scale t are the original derivatives multiplied by t^(j-1). -/
theorem rescaled_graph_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n j : ℕ} {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ n f S) (hj : j ≤ n) (hjpos : 1 ≤ j)
    (t : ℝ) {z : E} (hz : t • z ∈ S) :
    iteratedFDeriv ℝ j (fun z ↦ t⁻¹ • (f (t • z) - f 0)) z =
      (t⁻¹ * t^j) • iteratedFDeriv ℝ j f (t • z) := by
  let L : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E
  have hopen : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hcomp : ContDiffOn ℝ n (f ∘ L) (L ⁻¹' S) := hf.comp_continuousLinearMap L
  have hat : ContDiffAt ℝ j (f ∘ L) z :=
    (hcomp.contDiffAt (hopen.mem_nhds hz)).of_le (by exact_mod_cast hj)
  have hscale : iteratedFDeriv ℝ j (f ∘ L) z =
      t^j • iteratedFDeriv ℝ j f (t • z) := by
    have he := L.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn hopen.uniqueDiffOn
      hz (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen _ hopen hz,
      iteratedFDerivWithin_of_isOpen _ hS (show L z ∈ S from hz)] at he
    rw [he]
    ext v
    simpa [L, ContinuousMultilinearMap.compContinuousLinearMap_apply] using
      (iteratedFDeriv ℝ j f (t • z)).map_smul_univ (fun _ ↦ t) v
  change iteratedFDeriv ℝ j (fun z ↦ t⁻¹ • ((f ∘ L) z - f 0)) z = _
  have hsub : iteratedFDeriv ℝ j (fun x ↦ (f ∘ L) x - f 0) z =
      iteratedFDeriv ℝ j (f ∘ L) z - iteratedFDeriv ℝ j (fun _ : E ↦ f 0) z :=
    iteratedFDeriv_sub_apply hat (contDiffAt_const (c := f 0))
  rw [iteratedFDeriv_const_smul_apply' (hat.sub contDiffAt_const), hsub,
    iteratedFDeriv_const_of_ne (show j ≠ 0 by omega)]
  simp only [Pi.zero_apply, sub_zero, hscale, smul_smul]

/-- Journé's normalized graph remainder is small in the full C^{n,α} norm. (Journé, 1988) -/
theorem rescaled_graph_holder_small
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (hn : 1 ≤ n) {α K ε δ t R : ℝ}
    (_hα : 0 ≤ α) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (ht : 0 < t) (ht1 : t ≤ 1) (_hR : 0 < R)
    (hεR : ε*R ≤ δ) (hεδ : ε ≤ δ)
    (htK : t*K ≤ δ) (hpowK : t^α*K ≤ δ)
    {S : Set E} (hS : IsOpen S) (hconv : Convex ℝ S) (hzero : (0:E) ∈ S)
    {f : E → F} (hf : HasFiniteHolderBounds n α K f S)
    (hslope : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ ε)
    (hm : ∀ z ∈ Metric.ball (0:E) R, t • z ∈ S) :
    HasFiniteHolderBounds n α δ (fun z ↦ t⁻¹ • (f (t • z) - f 0))
      (Metric.ball (0:E) R) := by
  let L : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E
  have hcd : ContDiffOn ℝ n (fun z ↦ t⁻¹ • (f (t • z) - f 0))
      (Metric.ball (0:E) R) :=
    (((hf.1.comp_continuousLinearMap L).mono hm).sub contDiffOn_const).const_smul t⁻¹
  have hfactor (j : ℕ) : t⁻¹*t^(j+1) = t^j := by rw [pow_succ]; field_simp
  have hnorm (j : ℕ) (hj : j ≤ n) (hjpos : 1 ≤ j)
      (z : E) (hz : z ∈ Metric.ball (0:E) R) :
      ‖iteratedFDeriv ℝ j (fun z ↦ t⁻¹ • (f (t • z) - f 0)) z‖ =
        (t⁻¹*t^j)*‖iteratedFDeriv ℝ j f (t • z)‖ := by
    rw [rescaled_graph_iteratedFDeriv hS hf.1 hj hjpos t (hm z hz), norm_smul,
      Real.norm_of_nonneg (by positivity)]
  refine ⟨hcd, ?_, ?_⟩
  · intro j hj z hz
    rcases j with _ | j
    · rw [norm_iteratedFDeriv_zero, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hv := hconv.norm_image_sub_le_of_norm_fderiv_le
        (fun x hx ↦ (hf.1.differentiableOn (by simp; omega) x hx).differentiableAt
          (hS.mem_nhds hx)) hslope hzero (hm z hz)
      have hzR : ‖z‖ ≤ R := (by simpa using hz : ‖z‖ < R).le
      calc
        t⁻¹ * ‖f (t • z) - f 0‖ ≤ t⁻¹ * (ε * ‖t • z - 0‖) :=
          mul_le_mul_of_nonneg_left hv (by positivity)
        _ = ε*‖z‖ := by rw [sub_zero,norm_smul,Real.norm_of_nonneg ht.le]; field_simp
        _ ≤ ε*R := mul_le_mul_of_nonneg_left hzR hε
        _ ≤ δ := hεR
    · rw [hnorm (j+1) hj (by omega) z hz, hfactor]
      rcases j with _ | j
      · simp only [pow_zero, one_mul]
        change ‖iteratedFDeriv ℝ 1 f (t • z)‖ ≤ δ
        rw [norm_iteratedFDeriv_one]
        exact (hslope (t • z) (hm z hz)).trans hεδ
      · have hjt : t^(j+1) ≤ t := by
          calc
            t^(j+1) = t^j*t := pow_succ t j
            _ ≤ 1*t := mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le ht1) ht.le
            _ = t := one_mul t
        exact (mul_le_mul (hjt) (hf.2.1 (j+2) hj (t • z) (hm z hz))
          (norm_nonneg _) ht.le).trans htK
  · intro x hx y hy
    rw [rescaled_graph_iteratedFDeriv hS hf.1 le_rfl hn t (hm x hx),
      rescaled_graph_iteratedFDeriv hS hf.1 le_rfl hn t (hm y hy),
      ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hfactor1 : t⁻¹*t^n ≤ 1 := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
      rw [hfactor]
      exact pow_le_one₀ ht.le ht1
    have hdist : ‖t • x - t • y‖ ^ α = t^α * ‖x-y‖^α := by
      rw [← smul_sub,norm_smul,Real.norm_of_nonneg ht.le,Real.mul_rpow ht.le (norm_nonneg _)]
    calc
      (t⁻¹*t^n)*‖iteratedFDeriv ℝ n f (t • x)-iteratedFDeriv ℝ n f (t • y)‖
          ≤ (t⁻¹*t^n)*(K*‖t • x-t • y‖^α) :=
        mul_le_mul_of_nonneg_left (hf.2.2 _ (hm x hx) _ (hm y hy)) (by positivity)
      _ ≤ K*‖t • x-t • y‖^α := mul_le_of_le_one_left (by positivity) hfactor1
      _ = (t^α*K)*‖x-y‖^α := by rw [hdist]; ring
      _ ≤ δ*‖x-y‖^α := mul_le_mul_of_nonneg_right hpowK (by positivity)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
