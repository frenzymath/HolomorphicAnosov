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

namespace PicardVariationalWitnesses
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Mathlib's SAME fixed-point family, with its integral equation, buffer range, and joint
continuity retained together. The range estimate is obtained directly from its constructed
`FunSpace` curve, rather than asserted about an unrelated solution family. -/
theorem exists_picard_family_with_range
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E,
      ContinuousOn (fun p : E × ℝ ↦ α p.1 p.2) (closedBall x₀ r ×ˢ Icc tmin tmax) ∧
      ∀ x ∈ closedBall x₀ r,
        Continuous (α x) ∧ (∀ t : ℝ, α x t ∈ closedBall x₀ a) ∧
        (∀ t ∈ Icc tmin tmax, α x t = x + ∫ s in (t₀ : ℝ)..t, f s (α x s)) := by
  classical
  have hex (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose β hβ using hex
  let α : E → ℝ → E := fun x ↦
    if hx : x ∈ closedBall x₀ r then (β x hx).compProj else 0
  have heq (x) (hx : x ∈ closedBall x₀ r) : α x = (β x hx).compProj := by
    simp only [α, dite_eq_left hx]
  have hcont (x) (hx : x ∈ closedBall x₀ r) : Continuous (α x) := by
    rw [heq x hx]
    exact (β x hx).continuous_compProj
  obtain ⟨L', hdist⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (fun x ↦ α x t) (closedBall x₀ r) := by
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [heq x hx, heq y hy, FunSpace.compProj_of_mem ht, FunSpace.compProj_of_mem ht]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    have hd := hdist x y hx hy (β x hx) (β y hy) (hβ x hx) (hβ y hy)
    exact (ContinuousMap.dist_le_iff_of_nonempty.mp hd) ⟨t, ht⟩
  refine ⟨α, ?_, ?_⟩
  · exact continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
      (fun x hx ↦ (hcont x hx).continuousOn) hlip
  intro x hx
  refine ⟨hcont x hx, ?_, ?_⟩
  · intro t
    rw [heq x hx]
    exact (β x hx).compProj_mem_closedBall hf.mul_max_le
  intro t ht
  have hh := (FunSpace.isFixedPt_next_iff hf hx).mp (hβ x hx) ⟨t, ht⟩
  rw [heq x hx, FunSpace.compProj_of_mem ht]
  simpa only [picard_apply] using hh

end PicardVariationalWitnesses
