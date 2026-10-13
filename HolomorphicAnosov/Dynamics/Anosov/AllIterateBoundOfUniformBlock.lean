import HolomorphicAnosov.Dynamics.Anosov.DerivativeBlockResidueBound
import HolomorphicAnosov.Analysis.QuotientTimeToExponential
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov
universe u
namespace UniformIterateBounds
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)]

omit [IsManifold I ∞ X] in
/-- Internal assembly once the original compact block and residual bounds have been proved.
The hypotheses here are the explicit pending proof operands, NOT additional hypotheses of
Theorem 1.2. This lemma retains the original map, distribution and receiving metric fibre. -/
theorem all_iterate_bound_of_uniform_block
    (f : Diffeomorph I I X X ∞) (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I f x).toLinearMap = P (f x))
    (k : ℕ) (hk : 0 < k) (theta R : ℝ)
    (htheta : 0 < theta) (htheta1 : theta < 1) (hR : 0 < R)
    (hblock : ∀ x (v : TangentSpace I x), v ∈ P x →
      ‖mfderiv I I ((f : X → X)^[k]) x v‖ ≤ theta * ‖v‖)
    (hresidue : ∀ r, r < k → ∀ x (v : TangentSpace I x), v ∈ P x →
      ‖mfderiv I I ((f : X → X)^[r]) x v‖ ≤ R * ‖v‖) :
    ∃ C lam : ℝ, 0 < C ∧ 0 < lam ∧ lam < 1 ∧
      ∀ n x (v : TangentSpace I x), v ∈ P x →
        ‖mfderiv I I ((f : X → X)^[n]) x v‖ ≤ C * lam ^ n * ‖v‖ := by
  obtain ⟨C, lam, hC, hlam, hlam1, hnum⟩ :=
    HolomorphicAnosov.quotient_time_to_exponential k hk theta R htheta htheta1 hR
  refine ⟨C, lam, hC, hlam, hlam1, fun n x v hv ↦ ?_⟩
  exact (derivative_block_residue_bound f P hP k hk theta R htheta.le hR.le
    hblock hresidue n x v hv).trans (mul_le_mul_of_nonneg_right (hnum n) (norm_nonneg v))

end UniformIterateBounds
end HolomorphicAnosov
