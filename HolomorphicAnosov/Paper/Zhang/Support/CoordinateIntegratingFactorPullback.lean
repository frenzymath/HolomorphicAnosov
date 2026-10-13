import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Pullback of coordinate integrating factors to the tangent bundle. (Zhang, Lemma 2.4, p. 7;
Demailly, V.3, p. 256) -/

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- The coordinate equation `dg = -gA` pulls back through a manifold chart to the integrating-factor
equation for the connection form on tangent fibres. (Zhang, Lemma 2.4, p. 7; Demailly, V.3, p.
256) -/
theorem coordinate_integrating_factor_pullback
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (nabla : QuotientLineConnection.Connection U)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ atlas (ComplexModel d) X)
    (g : ComplexModel d → ℂ) (x : X) (hx : x ∈ c.source)
    (hg : HasFDerivAt g
      (-(g (c x)) • QuotientLineConnection.coordinateForm nabla e c (c x)) (c x)) :
    QuotientLineConnection.realDifferential (d := d) (g ∘ c) x =
      -(g (c x)) • nabla.form V e x := by
  have hcm : c ∈ IsManifold.maximalAtlas (realModel d) ∞ X :=
    IsManifold.subset_maximalAtlas hc
  have hdc := (contMDiffAt_of_mem_maximalAtlas hcm hx).mdifferentiableAt (by simp)
  have hdci := (contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hx)).mdifferentiableAt
    (by simp)
  have hcomp := mfderiv_comp x hdci hdc
  have heq : (c.symm ∘ c : X → X) =ᶠ[nhds x] id := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    exact c.left_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  have hgcomp := mfderiv_comp x hg.differentiableAt.mdifferentiableAt hdc
  unfold QuotientLineConnection.realDifferential
  rw [hgcomp]
  rw [mfderiv_eq_fderiv, hg.fderiv]
  ext v
  change (-(g (c x))) *
    nabla.form V e (c.symm (c x))
      (mfderiv (realModel d) (realModel d) c.symm (c x)
        (mfderiv (realModel d) (realModel d) c x v)) =
    (-(g (c x))) * nabla.form V e x v
  rw [c.left_inv hx]
  have hcancel := congrArg (fun L ↦ L v) hcomp
  change v = mfderiv (realModel d) (realModel d) c.symm (c x)
    (mfderiv (realModel d) (realModel d) c x v) at hcancel
  exact congrArg (fun w : TangentSpace (realModel d) x ↦
    (-(g (c x))) * nabla.form V e x w) hcancel.symm

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
