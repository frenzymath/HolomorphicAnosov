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
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.continuous_tangent_norm

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

theorem eventually_sphere_speed_bound
    (F : M → M) (hF : ContMDiff I I 1 F)
    (x : M) (q : ℝ) (hq : ‖mfderiv I I F x‖ < q) :
    let e := trivializationAt E (TangentSpace I (M := M)) x
    ∀ᶠ y in 𝓝 x, ∀ w ∈ Metric.sphere (0 : E) 1,
      ‖mfderiv I I F y (e.symm y w)‖ < q * ‖e.symm y w‖ := by
  let e := trivializationAt E (TangentSpace I (M := M)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  apply (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
  intro w hw
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hv0 : e.symm x w ≠ 0 := by
    rw [← e.symmL_apply (R := ℝ) hx]
    intro hzero
    apply hw0
    calc
      w = e.continuousLinearMapAt ℝ x (e.symmL ℝ x w) :=
        (e.continuousLinearMapAt_symmL (R := ℝ) hx w).symm
      _ = 0 := by rw [hzero, map_zero]
  have hV : ContinuousAt
      (fun p : M × E ↦ (⟨p.1, e.symm p.1 p.2⟩ : TangentBundle I M)) (x, w) :=
    e.continuousOn_symm.continuousAt
      ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hx, mem_univ w⟩)
  have hn : ContinuousAt (fun p : M × E ↦ ‖e.symm p.1 p.2‖) (x, w) :=
    (continuous_tangent_norm (I := I) (M := M)).continuousAt.comp hV
  have hfn : ContinuousAt
      (fun p : M × E ↦ ‖mfderiv I I F p.1 (e.symm p.1 p.2)‖) (x, w) :=
    (continuous_tangent_norm (I := I) (M := M)).continuousAt.comp
      ((hF.continuous_tangentMap le_rfl).continuousAt.comp hV)
  apply hfn.eventually_lt (continuousAt_const.mul hn)
  exact (mfderiv I I F x).le_opNorm (e.symm x w) |>.trans_lt
    (mul_lt_mul_of_pos_right hq (norm_pos_iff.mpr hv0))


end
end HolomorphicAnosov.TheoremAProof.Dimension
