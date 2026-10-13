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

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology NNReal

namespace FirstVariationalDefect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint continuity of coefficients on an OPEN rectangle gives uniform continuity in the
initial parameter along the fixed compact time interval. The second point is allowed outside
the compact graph; this is the neighborhood form of compact uniform continuity. -/
theorem coefficients_uniform_near_initial
    (A : E × ℝ → E →L[ℝ] E) (U : Set E) (I : Set ℝ)
    (hU : IsOpen U) (hI : IsOpen I) (hA : ContinuousOn A (U ×ˢ I))
    (x : E) (hx : x ∈ U) (T : ℝ) (hseg : Icc 0 T ⊆ I) :
    ∀ ε > 0, ∃ δ > 0, ∀ z : E, dist z x < δ → ∀ t ∈ Icc 0 T,
      ‖A (z, t) - A (x, t)‖ < ε := by
  intro ε hε
  have hcompact : IsCompact (({x} : Set E) ×ˢ Icc 0 T) :=
    isCompact_singleton.prod isCompact_Icc
  have hcont : ∀ p ∈ ({x} : Set E) ×ˢ Icc 0 T, ContinuousAt A p := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    have hz' : z = x := hz
    subst z
    exact hA.continuousAt ((hU.prod hI).mem_nhds ⟨hx, hseg ht⟩)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp
    (hcompact.uniformContinuousAt_of_continuousAt A hcont (Metric.dist_mem_uniformity hε))
  refine ⟨δ, hδ, ?_⟩
  intro z hz t ht
  have hprod : dist (x, t) (z, t) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg), dist_comm] using hz
  have hh := hclose (a := (x, t)) (b := (z, t)) hprod ⟨rfl, ht⟩
  change dist (A (x, t)) (A (z, t)) < ε at hh
  simpa only [dist_eq_norm, norm_sub_rev] using hh

end FirstVariationalDefect
