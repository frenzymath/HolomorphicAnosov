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
import HolomorphicAnosov.Analysis.Flow.RealFlowLocalUniqueness

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.RealFlowUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- C¹ on the original open field domain gives local Lipschitz control at
EVERY actual common curve value. The coincidence set is closed by continuity
and relatively open by local ODE uniqueness, hence is the entire connected
interval. No finite-dimensional assumption is needed for this stronger kernel. -/
theorem eqOn_of_contDiffOn
    {F : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    {J : Set ℝ} (hJ : OrdConnected J) {f g : ℝ → E}
    (hf : ContinuousOn f J) (hg : ContinuousOn g J)
    (hdf : ∀ t ∈ J, HasDerivWithinAt f (F (f t)) J t)
    (hdg : ∀ t ∈ J, HasDerivWithinAt g (F (g t)) J t)
    (hfΩ : MapsTo f J Ω) (_hgΩ : MapsTo g J Ω)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (heq : f t₀ = g t₀) : EqOn f g J := by
  have : PreconnectedSpace J := Subtype.preconnectedSpace hJ.isPreconnected
  let C : Set J := {t | f t = g t}
  have hclosed : IsClosed C := isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hf)
    (continuousOn_iff_continuous_domRestrict.mp hg)
  have hopen : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨K, B, hB, hLip⟩ :=
      (hF.contDiffAt (hΩ.mem_nhds (hfΩ t.property))).exists_lipschitzOnWith
    have hl := local_uniqueness hJ hf hg hdf hdg t.property ht hB hLip
    exact (eventually_nhds_subtype_iff J t (fun s ↦ f s = g s)).mpr hl
  have hC : C = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t₀, ht₀⟩, heq⟩
  intro t ht
  exact (show (⟨t, ht⟩ : J) ∈ C from hC.symm ▸ mem_univ _)

end HolomorphicAnosov.RealFlowUniqueness
