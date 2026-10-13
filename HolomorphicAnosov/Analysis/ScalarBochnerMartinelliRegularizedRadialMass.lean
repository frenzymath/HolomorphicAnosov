import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliRadialPrimitive

/-!
# Unit-scale radial mass for the Bochner–Martinelli regularization

Source: Demailly, *Complex Analytic and Differential Geometry*, I §3.D,
pp.25–26, equations (3.21)–(3.25). This public helper isolates the radial
mass calculation needed by the compact-support scalar Bochner–Martinelli formula.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- Unit-scale mass of the epsilon-regularized Bochner–Martinelli density.

The proof follows Demailly I §3.D pp.25–26: apply the radial Haar integral
identity in real dimension `2*n`, evaluate the radial integral using the
primitive `r^(2*n)/(2*n*(1+r^2)^n)`, and use the even-dimensional unit-ball
volume. The radial primitive is supplied by the public helper theorem.
-/
theorem scalar_bochnermartinelli_regularized_radial_mass
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ x : EuclideanSpace ℝ (Fin (2 * n)),
      (n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1) ∂volume =
      (Real.pi : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) := by
  have hrad := scalar_bochnermartinelli_radial_primitive hn
  let f : ℝ → ℝ := fun r => (n : ℝ) / (r ^ 2 + 1) ^ (n + 1)
  have : NeZero (2*n) := ⟨by omega⟩
  let : Nontrivial (EuclideanSpace ℝ (Fin (2*n))) := inferInstance
  have hradial : _ := MeasureTheory.integral_fun_norm_addHaar (E := EuclideanSpace ℝ (Fin (2*n))) (F := ℝ) (μ := volume) f
  have hvol : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin (2*n))) 1) =
      (Real.pi : ℝ)^n / (Nat.factorial n : ℝ) := by
    have : NeZero (2*n) := ⟨by omega⟩
    rw [Measure.real]
    rw [InnerProductSpace.volume_ball_of_dim_even (E := EuclideanSpace ℝ (Fin (2*n))) (k := n) (by simp) 0 1]
    have hp : 0 ≤ (Real.pi : ℝ)^n / (Nat.factorial n : ℝ) := by positivity
    simp [hp]
  rw [show (fun x : EuclideanSpace ℝ (Fin (2*n)) => (n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1)) = (fun x => f ‖x‖) by
    funext x; rfl]
  rw [hradial]
  rw [hvol] at hradial
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2*n))) = 2*n := by simp
  rw [hfin, hvol]
  simp only [smul_eq_mul, f]
  rw [show (fun y : ℝ => y ^ (2*n - 1) * ((n : ℝ) / (y ^ 2 + 1) ^ (n+1))) =
      (fun y => (n : ℝ) * (y ^ (2*n - 1) / (1 + y^2)^(n+1))) by
    funext y; field_simp; ring]
  rw [integral_const_mul, hrad]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hfact : (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n-1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
  rw [hfact]
  ring_nf
  simp [hn0]

end HolomorphicAnosov.Analysis
