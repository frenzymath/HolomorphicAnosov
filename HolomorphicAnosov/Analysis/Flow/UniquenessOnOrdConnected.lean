import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Analysis.Flow.LocalUniquenessWithin

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.SmoothLocalFlowProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

omit [FiniteDimensional ℝ E] in
/-- The exact interval-uniqueness clause of Andrews 6.1.1. Continuity makes
the coincidence set closed in the original interval; local chart uniqueness
makes it relatively open. Order-connectedness gives connectedness, including
singleton intervals and closed endpoints. -/
theorem uniqueness_on_ordConnected
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {J : Set ℝ} (hJ : OrdConnected J) {γ γ' : ℝ → N}
    (hγ : IsMIntegralCurveOn (I := I) γ V J)
    (hγ' : IsMIntegralCurveOn (I := I) γ' V J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (heq : γ t₀ = γ' t₀) : EqOn γ γ' J := by
  have : PreconnectedSpace J := Subtype.preconnectedSpace hJ.isPreconnected
  let C : Set J := {t | γ t = γ' t}
  have hclosed : IsClosed C := isClosed_eq
    (continuousOn_iff_continuous_domRestrict.mp hγ.continuousOn)
    (continuousOn_iff_continuous_domRestrict.mp hγ'.continuousOn)
  have hopen : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hl := local_uniqueness_within hV hJ hγ hγ' t.property ht
    exact (eventually_nhds_subtype_iff J t (fun s ↦ γ s = γ' s)).mpr hl
  have hC : C = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t₀, ht₀⟩, heq⟩
  intro t ht
  exact (show (⟨t, ht⟩ : J) ∈ C from hC.symm ▸ mem_univ _)

end HolomorphicAnosov.SmoothLocalFlowProof
