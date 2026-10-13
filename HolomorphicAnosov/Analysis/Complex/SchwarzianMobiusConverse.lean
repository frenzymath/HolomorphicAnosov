import HolomorphicAnosov.Ghys.AffineSchwarzianQuadraticForm
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Local converse to vanishing of the Schwarzian

DAG: `analysis.schwarzian_mobius_converse_g14`.
Source: Lyubich, Conformal Geometry and Dynamics of Quadratic Polynomials,
§2.9.1 pp.96–97. The integrating-factor implementation of local ODE uniqueness
below is an agent-written expansion of the matching-two-jet argument.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology _root_.Topology
open scoped Matrix
namespace HolomorphicAnosov.Ghys

/-- A holomorphic function with nonzero derivative and vanishing Schwarzian has a
Möbius germ. Source: Lyubich §2.9.1 pp.96–97; agent-written implementation.

Proof: On a small convex ball put N=F''/F', b=N(z₀)/2 and q(z)=1-b(z-z₀).
The Schwarzian equation gives N'=N²/2. Hence D=Nq-2b solves D'=ND/2
and D(z₀)=0. A holomorphic primitive P of -N/2 makes exp(P)D constant,
so D=0. Hence (F'q-bF)'=F'(Nq-2b)=0 and
(Fq)'=F'q-bF=F'(z₀)-bF(z₀), giving the fractional-linear expression after integration.
Its matrix determinant is F'(z₀), which is nonzero. Shrink the ball so q never
vanishes. This argument includes b=0 and never divides by b or N. -/
theorem schwarzian_zero_mobius_germ {F : ℂ → ℂ} {z₀ : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hz : z₀ ∈ U) (hF : DifferentiableOn ℂ F U)
    (hne : ∀ z ∈ U, deriv F z ≠ 0) (hzero : ∀ z ∈ U, schwarzian F z = 0) :
    IsMobiusScalarGerm F z₀ := by
  let N : ℂ → ℂ := fun z ↦ deriv (deriv F) z / deriv F z
  have hNdiff : DifferentiableOn ℂ N U :=
    ((hF.deriv hU).deriv hU).div (hF.deriv hU) hne
  have hN {z : ℂ} (hz : z ∈ U) : HasDerivAt N ((1 / 2 : ℂ) * N z ^ 2) z := by
    have hd := (((hF.deriv hU).deriv hU).differentiableAt (hU.mem_nhds hz)).hasDerivAt.div
      ((hF.deriv hU).differentiableAt (hU.mem_nhds hz)).hasDerivAt (hne z hz)
    convert hd using 1
    dsimp only [N]
    have hs := hzero z hz
    dsimp only [schwarzian] at hs
    field_simp [hne z hz] at hs ⊢
    linear_combination -hs
  let b : ℂ := N z₀ / 2
  let q : ℂ → ℂ := fun z ↦ 1 - b * (z - z₀)
  have hq (z : ℂ) : HasDerivAt q (-b) z := by
    simpa [q] using (hasDerivAt_const z (1 : ℂ)).fun_sub
      (((hasDerivAt_id z).sub_const z₀).const_mul b)
  have hq0 : q z₀ = 1 := by simp [q]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hz) ((hq z₀).continuousAt.eventually_ne (show q z₀ ≠ 0 by simp [hq0])))
  let V := Metric.ball z₀ r
  have hV : IsOpen V := Metric.isOpen_ball
  have hc : Convex ℝ V := convex_ball z₀ r
  have hzV : z₀ ∈ V := Metric.mem_ball_self hr
  have hVU : V ⊆ U := fun _ h ↦ (hball h).1
  have hqne {z : ℂ} (hz : z ∈ V) : q z ≠ 0 := (hball hz).2
  have hlin (D a : ℂ → ℂ) (ha : DifferentiableOn ℂ a V)
      (hd : ∀ z ∈ V, HasDerivAt D (a z * D z) z) (hD0 : D z₀ = 0) :
      ∀ z ∈ V, D z = 0 := by
    obtain ⟨P, hP⟩ := hc.exists_forall_hasDerivWithinAt ha.neg
    have hp {z : ℂ} (hz : z ∈ V) : HasDerivAt P (-a z) z :=
      (hP z hz).hasDerivAt (hV.mem_nhds hz)
    have hproduct {z : ℂ} (hz : z ∈ V) :
        HasDerivAt (fun w ↦ Complex.exp (P w) * D w) 0 z := by
      convert (hp hz).cexp.mul (hd z hz) using 1; ring
    intro z hz
    have he := hV.is_const_of_deriv_eq_zero hc.isPreconnected
      (fun z hz ↦ (hproduct hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hproduct hz).deriv) hz hzV
    simp only [hD0, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (Complex.exp_ne_zero _)
  have hNq : ∀ z ∈ V, N z * q z = N z₀ := by
    have he := hlin (fun z ↦ N z * q z - N z₀) (fun z ↦ N z / 2)
      ((hNdiff.mono hVU).div_const 2) (fun z hz ↦ ?_) (by simp [hq0])
    · intro z hz
      exact sub_eq_zero.mp (he z hz)
    · convert ((hN (hVU hz)).mul (hq z)).sub_const (N z₀) using 1
      dsimp [b]
      ring
  have hFd {z : ℂ} (hz : z ∈ V) : HasDerivAt F (deriv F z) z :=
    (hF.differentiableAt (hU.mem_nhds (hVU hz))).hasDerivAt
  have hFdd {z : ℂ} (hz : z ∈ V) :
      HasDerivAt (deriv F) (N z * deriv F z) z := by
    convert ((hF.deriv hU).differentiableAt (hU.mem_nhds (hVU hz))).hasDerivAt using 1
    dsimp [N]
    field_simp [hne z (hVU hz)]
  have hsecond {z : ℂ} (hz : z ∈ V) :
      HasDerivAt (fun w ↦ deriv F w * q w - b * F w) 0 z := by
    convert ((hFdd hz).mul (hq z)).sub ((hFd hz).const_mul b) using 1
    have he := hNq z hz
    dsimp [b]
    linear_combination -(deriv F z) * he
  have hfirst : ∀ z ∈ V, deriv F z * q z - b * F z = deriv F z₀ - b * F z₀ := by
    intro z hz
    simpa [hq0] using hV.is_const_of_deriv_eq_zero hc.isPreconnected
      (fun w hw ↦ (hsecond hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hsecond hw).deriv) hz hzV
  let A : ℂ := deriv F z₀ - b * F z₀
  have hfinal {z : ℂ} (hz : z ∈ V) :
      HasDerivAt (fun w ↦ F w * q w - A * (w - z₀)) 0 z := by
    have hd := ((hFd hz).mul (hq z)).fun_sub
      (((hasDerivAt_id z).sub_const z₀).const_mul A)
    have he : deriv F z * q z + F z * (-b) - A * 1 = 0 := by
      dsimp only [A]
      linear_combination hfirst z hz
    rw [he] at hd
    exact hd
  have hformula : ∀ z ∈ V, F z * q z = A * (z - z₀) + F z₀ := by
    intro z hz
    have he := hV.is_const_of_deriv_eq_zero hc.isPreconnected
      (fun w hw ↦ (hfinal hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hfinal hw).deriv) hz hzV
    simp only [hq0, mul_one, sub_self, mul_zero, sub_zero] at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  let mat : Matrix (Fin 2) (Fin 2) ℂ := !![A, F z₀ - A * z₀; -b, 1 + b * z₀]
  have hdet : mat.det ≠ 0 := by
    have he : mat.det = deriv F z₀ := by simp [mat, Matrix.det_fin_two, A]; ring
    rw [he]
    exact hne z₀ hz
  let g : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero mat hdet
  refine ⟨ComplexMobiusTransformation.ofMatrix g, ?_⟩
  filter_upwards [hV.mem_nhds hzV] with z hz
  have hfin (v : ℂ) : complexProjectiveLineFinite v =
      OnePoint.equivProjectivization ℂ (v : OnePoint ℂ) := by
    simp only [complexProjectiveLineFinite, complexProjectiveLineChartInv,
      complexProjectiveLineMk, OnePoint.equivProjectivization_apply_coe]
    congr 1
    funext i
    fin_cases i <;> rfl
  change complexProjectiveLineFinite (F z) = g • complexProjectiveLineFinite z
  rw [hfin, hfin, ← OnePoint.equivProjectivization_smul]
  congr 1
  rw [OnePoint.smul_some_eq_ite]
  have hgq : g 1 0 * z + g 1 1 = q z := by simp [g, mat, q]; ring
  rw [hgq, ite_eq_right (hqne hz)]
  congr 1
  apply (eq_div_iff (hqne hz)).2
  have he := hformula z hz
  simpa [g, mat, mul_sub, sub_add_eq_add_sub, add_sub_assoc] using he

end HolomorphicAnosov.Ghys
