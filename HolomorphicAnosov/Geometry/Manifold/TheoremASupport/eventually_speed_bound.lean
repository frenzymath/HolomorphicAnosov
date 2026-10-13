import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Zhang.CodimensionOne
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.eventually_sphere_speed_bound

namespace HolomorphicAnosov.TheoremAProof.Dimension
open Set Filter Manifold Bundle HolomorphicAnosov
open scoped Bundle ContDiff Manifold _root_.Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable [ProperSpace E]
open MeasureTheory
open scoped ENNReal
attribute [local instance] complex_isManifold_real
universe u
set_option maxHeartbeats 800000

theorem eventually_speed_bound
    (F : M → M) (hF : ContMDiff I I 1 F)
    (x : M) (q : ℝ) (hq : ‖mfderiv I I F x‖ < q) :
    ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      ‖mfderiv I I F y v‖ ≤ q * ‖v‖ := by
  let e := trivializationAt E (TangentSpace I (M := M)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  filter_upwards [eventually_sphere_speed_bound F hF x q hq,
    e.open_baseSet.mem_nhds hx] with y hS hy
  intro v
  by_cases hv : v = 0
  · simp [hv]
  let w := e.continuousLinearMapAt ℝ y v
  have hwv : e.symm y w = v := by
    rw [← e.symmL_apply (R := ℝ) hy]
    exact e.symmL_continuousLinearMapAt hy v
  have hw0 : w ≠ 0 := by
    intro hw
    have : v = 0 := by
      rw [← hwv, hw, ← e.symmL_apply (R := ℝ) hy, map_zero]
    exact hv this
  let u : E := (‖w‖⁻¹ : ℝ) • w
  have hu : u ∈ Metric.sphere (0 : E) 1 :=
    mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hw0)
  have H := (hS u hu).le
  change ‖mfderiv I I F y (e.symm y ((‖w‖⁻¹ : ℝ) • w))‖ ≤
    q * ‖e.symm y ((‖w‖⁻¹ : ℝ) • w)‖ at H
  rw [← e.symmL_apply (R := ℝ) hy] at H
  rw [map_smul, map_smul,
    norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
    norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg w))] at H
  have hsym : e.symmL ℝ y w = v := by rw [e.symmL_apply hy, hwv]
  rw [hsym] at H
  have H' : ‖w‖⁻¹ * ‖mfderiv I I F y v‖ ≤ ‖w‖⁻¹ * (q * ‖v‖) := by
    simpa only [mul_left_comm] using H
  exact le_of_mul_le_mul_left H' (inv_pos.mpr (norm_pos_iff.mpr hw0))


end
end HolomorphicAnosov.TheoremAProof.Dimension
