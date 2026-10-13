import HolomorphicAnosov.Paper.Zhang.TendstoFrameEvalOfC0

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- A C⁰ limit of successive pullbacks of quotient-line connections is invariant under the
biholomorphism, provided the difference values are bounded. (Zhang, Lemma 2.2, p.5) -/
theorem isInvariant_of_c0_limit
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    (f : Biholomorph d d X X)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (Ds : ℕ → Connection U) (D : Connection U)
    (hb : ∀ n, BddAbove (differenceValues g (Ds n) D))
    (hc : Tendsto (fun n ↦ c0Distance g (Ds n) D) atTop (𝓝 0))
    (hp : ∀ n (V W : Opens X) (e : HolomorphicFrame U V)
      (e' : HolomorphicFrame U W) (x : X), x ∈ V → f x ∈ W →
        (Ds (n + 1)).form V e x =
          (imageFrameCoefficient f hU e e' x)⁻¹ •
            realDifferential (imageFrameCoefficient f hU e e') x +
          ((Ds n).form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x)) :
    IsInvariant D f hU := by
  intro V W e e' x hx hfx
  ext v
  have hleft := (tendsto_frame_eval_of_c0 g Ds D hb hc V e x hx v).comp
    (tendsto_add_atTop_nat 1)
  have hright := (tendsto_const_nhds (x :=
    (imageFrameCoefficient f hU e e' x)⁻¹ •
      realDifferential (imageFrameCoefficient f hU e e') x v)).add
    (tendsto_frame_eval_of_c0 g Ds D hb hc W e' (f x) hfx
      (mfderiv (realModel d) (realModel d) f x v))
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall fun n ↦
    (congrArg (fun A ↦ A v) (hp n V W e e' x hx hfx)).symm

end HolomorphicAnosov
