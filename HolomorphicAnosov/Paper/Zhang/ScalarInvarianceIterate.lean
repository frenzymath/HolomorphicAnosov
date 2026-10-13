import HolomorphicAnosov.Geometry.BiholomorphToReal

open scoped Manifold ContDiff Topology _root_.Topology
noncomputable section
universe u
namespace HolomorphicAnosov

/-- A scalar tangent form invariant under pullback by a biholomorphism is invariant
under pullback by every nonnegative iterate. (Zhang, Lemma 2.2, pp.4–5) -/
theorem scalar_invariance_iterate
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X)
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hα : ∀ x, α x = (α (f x)).comp
      (mfderiv (realModel d) (realModel d) f x))
    (n : ℕ) (x : X) (v : TangentSpace (realModel d) x) :
    α x v = α (((f : X → X)^[n]) x)
      (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x v) := by
  have hf : ContMDiff (realModel d) (realModel d) ∞ (f : X → X) := f.toReal.contMDiff
  induction n generalizing x with
  | zero =>
    change α x v = α x (mfderiv (realModel d) (realModel d) id x v)
    rw [mfderiv_id]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ]
    rw [mfderiv_comp_apply x
      ((hf.iterate n).mdifferentiable (by simp) _)
      (hf.mdifferentiable (by simp) _) v]
    calc
      α x v = α (f x) (mfderiv (realModel d) (realModel d) f x v) :=
        congrArg (fun A ↦ A v) (hα x)
      _ = _ := ih (f x) (mfderiv (realModel d) (realModel d) f x v)

end HolomorphicAnosov
