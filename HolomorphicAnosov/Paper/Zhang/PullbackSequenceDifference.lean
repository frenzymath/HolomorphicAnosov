import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.PullbackScalarDifference

open Set TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- For a sequence of connections obtained by successive pullbacks under `f`, the
`n`th successive scalar difference is the pullback of the first difference under `f^[n]`.
(Zhang, Lemma 2.2, equation (6), p.5) -/
theorem pullback_sequence_difference
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ Nonempty (HolomorphicFrame U V))
    (f : Biholomorph d d X X)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (Ds : ℕ → Connection U)
    (hp : ∀ n (V W : Opens X) (e : HolomorphicFrame U V)
      (e' : HolomorphicFrame U W) (x : X), x ∈ V → f x ∈ W →
        (Ds (n + 1)).form V e x =
          (imageFrameCoefficient f hU e e' x)⁻¹ •
            realDifferential (imageFrameCoefficient f hU e e') x +
          ((Ds n).form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x))
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hα : ∀ (V : Opens X) (e : HolomorphicFrame U V) x, x ∈ V →
      (Ds 1).form V e x = (Ds 0).form V e x + α x) :
    ∀ n (V : Opens X) (e : HolomorphicFrame U V) x, x ∈ V →
      (Ds (n + 1)).form V e x = (Ds n).form V e x +
        (α (((f : X → X)^[n]) x)).comp
          (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x) := by
  have hf : ContMDiff (realModel d) (realModel d) ∞ (f : X → X) := f.toReal.contMDiff
  intro n
  induction n with
  | zero =>
    intro V e x hx
    change (Ds 1).form V e x = (Ds 0).form V e x +
      (α x).comp (mfderiv (realModel d) (realModel d) id x)
    rw [mfderiv_id, ContinuousLinearMap.comp_id]
    exact hα V e x hx
  | succ n ih =>
    intro V e x hx
    obtain ⟨W, hfx, ⟨e'⟩⟩ := hcover (f x)
    rw [hp (n + 1) V W e e' x hx hfx, hp n V W e e' x hx hfx, ih W e' (f x) hfx]
    ext v
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    rw [Function.iterate_succ, mfderiv_comp_apply x
      ((hf.iterate n).mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _) v]
    abel

end HolomorphicAnosov
