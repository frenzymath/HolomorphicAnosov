import HolomorphicAnosov.Paper.Zhang.DifferenceEvalLeC0

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- C⁰ convergence of connections implies convergence of their frame evaluations on each tangent
vector in a valid frame domain. (Zhang, Lemma 2.2, p. 5) -/
theorem tendsto_frame_eval_of_c0
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    {ι : Type*} {l : Filter ι} (Ds : ι → Connection U) (D : Connection U)
    (hb : ∀ n, BddAbove (differenceValues g (Ds n) D))
    (hc : Tendsto (fun n ↦ c0Distance g (Ds n) D) l (𝓝 0))
    (V : Opens X) (e : HolomorphicFrame U V) (x : X) (hx : x ∈ V)
    (v : TangentSpace (realModel d) x) :
    Tendsto (fun n ↦ (Ds n).form V e x v) l (𝓝 (D.form V e x v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ difference_eval_le_c0 g (Ds n) D (hb n) V e x hx v)
  simpa only [zero_mul] using hc.mul_const (Real.sqrt (g.inner x v v))

end HolomorphicAnosov
