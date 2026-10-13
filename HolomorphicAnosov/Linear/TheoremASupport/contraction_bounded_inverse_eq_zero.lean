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
import HolomorphicAnosov.Linear.TheoremASupport.iter_norm_bound

namespace HolomorphicAnosov.TheoremAProof
open Filter _root_.Topology

lemma contraction_bounded_inverse_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E ≃L[ℝ] E) (hT : ‖T.toContinuousLinearMap‖ < 1)
    (x : E) (C : ℝ) (hC : ∀ n : ℕ, ‖(T.symm : E → E)^[n] x‖ ≤ C) : x = 0 := by
  have hleft : Function.LeftInverse (T : E → E) (T.symm : E → E) := T.apply_symm_apply
  have hbound (n : ℕ) : ‖x‖ ≤ ‖T.toContinuousLinearMap‖ ^ n * C := by
    calc
      ‖x‖ = ‖(T : E → E)^[n] ((T.symm : E → E)^[n] x)‖ := by rw [hleft.iterate n x]
      _ ≤ ‖T.toContinuousLinearMap‖ ^ n * ‖(T.symm : E → E)^[n] x‖ := iter_norm_bound T _ n
      _ ≤ ‖T.toContinuousLinearMap‖ ^ n * C := mul_le_mul_of_nonneg_left (hC n) (pow_nonneg (norm_nonneg _) _)
  have hlim : Tendsto (fun n : ℕ => ‖T.toContinuousLinearMap‖ ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg T.toContinuousLinearMap) hT).mul_const C
  exact norm_eq_zero.mp (le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)) (norm_nonneg x))


end HolomorphicAnosov.TheoremAProof
