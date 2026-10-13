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

omit [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [ProperSpace E] in
theorem riemannianEDist_map_le_of_speed_bound
    (F : M → M) (hF : ContMDiff I I 1 F)
    (K : ℝ≥0∞) (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hK : ∀ x (v : TangentSpace I x),
      ‖mfderiv I I F x v‖ₑ ≤ K * ‖v‖ₑ) (x y : M) :
    riemannianEDist I (F x) (F y) ≤ K * riemannianEDist I x y := by
  conv_rhs => rw [riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne hK0 hKtop]
  refine le_iInf fun hγ => ?_
  let η : Path (F x) (F y) := γ.map hF.continuous
  have hη : ContMDiff (𝓡∂ 1) I 1 η := hF.comp hγ
  calc
    riemannianEDist I (F x) (F y) ≤
        ∫⁻ t, ‖mfderiv (𝓡∂ 1) I η t 1‖ₑ := by
      rw [riemannianEDist]
      exact biInf_le _ hη
    _ ≤ ∫⁻ t, K * ‖mfderiv (𝓡∂ 1) I γ t 1‖ₑ := by
      apply lintegral_mono
      intro t
      change ‖mfderiv (𝓡∂ 1) I (F ∘ γ) t 1‖ₑ ≤ _
      rw [mfderiv_comp t (hF.mdifferentiable one_ne_zero (γ t))
        (hγ.mdifferentiable one_ne_zero t)]
      exact hK (γ t) _
    _ = K * ∫⁻ t, ‖mfderiv (𝓡∂ 1) I γ t 1‖ₑ :=
      lintegral_const_mul' K _ hKtop



end
end HolomorphicAnosov.TheoremAProof.Dimension
