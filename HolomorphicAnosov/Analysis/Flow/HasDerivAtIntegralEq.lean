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

/-- A continuous integral-equation witness has the claimed time derivative at each interior
time. This keeps the Picard solution itself, using equality on an open time neighborhood. -/
theorem hasDerivAt_of_integral_eq [CompleteSpace E]
    (γ g : ℝ → E) (I : Set ℝ) (hI : IsOpen I) (hg : ContinuousOn g I)
    (a t : ℝ) (ht : t ∈ I) (hseg : uIcc a t ⊆ I)
    (hsol : ∀ s ∈ I, γ s = γ a + ∫ r in a..s, g r) :
    HasDerivAt γ (g t) t := by
  have hint : IntervalIntegrable g MeasureTheory.volume a t :=
    (hg.mono hseg).intervalIntegrable
  have hd := intervalIntegral.integral_hasDerivAt_right hint
    (hg.stronglyMeasurableAtFilter hI t ht) (hg.continuousAt (hI.mem_nhds ht))
  apply (hd.const_add (γ a)).congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  exact hsol s hs

end FirstVariationalDefect
