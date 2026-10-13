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

theorem compact_surjective_strict_distance_subsingleton
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X → X) (hF : Function.Surjective F)
    (hstrict : ∀ x y, x ≠ y → dist (F x) (F y) < dist x y) :
    Subsingleton X := by
  constructor
  intro x y
  by_contra hxy
  obtain ⟨p, hp, hmax⟩ := isCompact_univ.exists_isMaxOn
    (s := (Set.univ : Set (X × X))) ⟨(x, y), Set.mem_univ _⟩
    (continuous_fst.dist continuous_snd).continuousOn
  obtain ⟨u, hu⟩ := hF p.1
  obtain ⟨v, hv⟩ := hF p.2
  have hpos : 0 < dist p.1 p.2 :=
    lt_of_lt_of_le (dist_pos.mpr hxy) (hmax (Set.mem_univ (x, y)))
  have huv : u ≠ v := by
    intro heq
    have : p.1 = p.2 := by rw [← hu, ← hv, heq]
    simp [this] at hpos
  have hlt := hstrict u v huv
  rw [hu, hv] at hlt
  exact (not_lt_of_ge (hmax (Set.mem_univ (u, v)))) hlt



end
end HolomorphicAnosov.TheoremAProof.Dimension
