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
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.smoothMetric_uniform_enorm_speed_bound
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.compact_surjective_strict_distance_subsingleton
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.riemannianEDist_map_le_of_speed_bound
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.finite_edist_of_preconnected

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

omit [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem smoothMetric_full_contraction_subsingleton
    [CompactSpace M] [ConnectedSpace M] [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (F : M → M) (hF : ContMDiff I I 1 F) (hsurj : Function.Surjective F)
    (hstrict :
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      ∀ x, ‖mfderiv I I F x‖ < 1) : Subsingleton M := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  obtain ⟨K, hK0, hK1, hK⟩ := smoothMetric_uniform_enorm_speed_bound g F hF hstrict
  have hKtop : K ≠ ⊤ := (hK1.trans (by simp)).ne
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hfinite : ∀ x y : M, edist x y ≠ ⊤ := finite_edist_of_preconnected
  let : MetricSpace M := EMetricSpace.toMetricSpace hfinite
  apply compact_surjective_strict_distance_subsingleton F hsurj
  intro x y hxy
  have he := riemannianEDist_map_le_of_speed_bound F hF K hK0.ne' hKtop hK x y
  change edist (F x) (F y) ≤ K * edist x y at he
  have hd := ENNReal.toReal_mono (ENNReal.mul_ne_top hKtop (hfinite x y)) he
  rw [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at hd
  have hKr : K.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hKtop (by simp)).mpr hK1
  exact hd.trans_lt (by nlinarith [dist_pos.mpr hxy])



end
end HolomorphicAnosov.TheoremAProof.Dimension
