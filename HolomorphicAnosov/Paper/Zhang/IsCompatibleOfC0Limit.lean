import HolomorphicAnosov.Paper.Zhang.TendstoFrameEvalOfC0

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- Compatibility of quotient-line connections is preserved under C⁰ convergence measured by the
given tangent metric. (Zhang, Lemma 2.2, p.5, after (6)) -/
theorem isCompatible_of_c0_limit
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (Ds : ι → Connection U) (D : Connection U)
    (hb : ∀ n, BddAbove (differenceValues g (Ds n) D))
    (hc : Tendsto (fun n ↦ c0Distance g (Ds n) D) l (𝓝 0))
    (hcomp : ∀ n, IsCompatible (Ds n)) : IsCompatible D := by
  constructor
  · intro V e x hx v
    have hv := tendsto_frame_eval_of_c0 g Ds D hb hc V e x hx
      (complexTangentToReal d x v)
    have hiv := tendsto_frame_eval_of_c0 g Ds D hb hc V e x hx
      (complexTangentToReal d x (Complex.I • v))
    apply tendsto_nhds_unique hiv
    exact (hv.const_mul Complex.I).congr'
      (Eventually.of_forall fun n ↦ ((hcomp n).1 V e x hx v).symm)
  · intro V e Y Z hY hZ hYU x hx
    let s := fun y ↦ projection U y (Z y)
    have hcv (v : TangentSpace (realModel d) x) :
        Tendsto (fun n ↦ e.coordinate x hx (covariantDerivative (Ds n) e s x hx v))
          l (𝓝 (e.coordinate x hx (covariantDerivative D e s x hx v))) := by
      simp only [covariantDerivative, LinearEquiv.apply_symm_apply]
      exact tendsto_const_nhds.add
        ((tendsto_frame_eval_of_c0 g Ds D hb hc V e x hx v).const_mul _)
    apply (e.coordinate x hx).injective
    have hlim := ((hcv (complexTangentToReal d x (Y x))).sub
      ((hcv (complexTangentToReal d x (Complex.I • Y x))).const_mul Complex.I)).const_mul
        (1 / 2 : ℂ)
    simp only [map_smul, map_sub, smul_eq_mul]
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    apply Eventually.of_forall
    intro n
    have hn := congrArg (e.coordinate x hx) ((hcomp n).2 V e Y Z hY hZ hYU x hx)
    simpa only [map_smul, map_sub, smul_eq_mul] using hn.symm

end HolomorphicAnosov
