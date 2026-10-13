import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTangentEquation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLinearTangentZero

noncomputable section
namespace HolomorphicAnosov

/-- If centered invariant unit-Lipschitz graph families are differentiable at zero, their derivatives there vanish (HPS, Corollary 5.3, p.60, 62). -/
theorem parameter_graph_zero_derivative
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A ≃ A) (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : ∀ p, G p 0 = 0)
    (hDG : ∀ p, HasFDerivAt (G p) ((T₁ p).toContinuousLinearMap.prodMap (T₂ p)) 0)
    (a k : NNReal) (hgap : (a : ℝ) * k < 1)
    (hT₁ : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hT₂ : ∀ p, ‖T₂ p‖ ≤ k)
    (s : ∀ p, E₁ p → E₂ p) (t : ∀ p, E₂ p → E₁ p)
    (hs : ∀ p, s p 0 = 0 ∧ LipschitzWith 1 (s p) ∧ DifferentiableAt ℝ (s p) 0)
    (ht : ∀ p, t p 0 = 0 ∧ LipschitzWith 1 (t p) ∧ DifferentiableAt ℝ (t p) 0)
    (hsgraph : ∀ p x, (G p (x,s p x)).2 = s (h p) (G p (x,s p x)).1)
    (htgraph : ∀ p y, (G p (t p y,y)).1 = t (h p) (G p (t p y,y)).2) :
    ∀ p, fderiv ℝ (s p) 0 = 0 ∧ fderiv ℝ (t p) 0 = 0 := by
  have hse (p : A) : (T₂ p).comp (fderiv ℝ (s p) 0) =
      (fderiv ℝ (s (h p)) 0).comp (T₁ p).toContinuousLinearMap :=
    parameter_graph_tangent_equation (T₁ p).toContinuousLinearMap (T₂ p) (G p)
      (hG p) (hDG p) (s p) (s (h p)) (hs p).1 (hs p).2.2 (hs (h p)).2.2 (hsgraph p)
  have hte (p : A) : (T₁ p).toContinuousLinearMap.comp (fderiv ℝ (t p) 0) =
      (fderiv ℝ (t (h p)) 0).comp (T₂ p) := by
    have hpair := (ht p).2.2.hasFDerivAt.prodMk (hasFDerivAt_id (0 : E₂ p))
    have hd : HasFDerivAt (G p) ((T₁ p).toContinuousLinearMap.prodMap (T₂ p))
        (t p 0,0) := by simpa only [(ht p).1, show (0,0) = (0 : E₁ p × E₂ p) from rfl] using hDG p
    have hc := hd.comp (f := fun y ↦ (t p y,y)) 0 hpair
    have hleft : HasFDerivAt (fun y ↦ (G p (t p y,y)).1)
        ((T₁ p).toContinuousLinearMap.comp (fderiv ℝ (t p) 0)) 0 := by
      convert hc.fst using 1 <;> ext y <;> rfl
    have hsecond : HasFDerivAt (fun y ↦ (G p (t p y,y)).2) (T₂ p) 0 := by
      convert hc.snd using 1 <;> ext y <;> rfl
    have hright : HasFDerivAt (fun y ↦ t (h p) (G p (t p y,y)).2)
        ((fderiv ℝ (t (h p)) 0).comp (T₂ p)) 0 := by
      apply HasFDerivAt.comp 0 _ hsecond
      simpa only [(ht p).1, show (0,0) = (0 : E₁ p × E₂ p) from rfl,
        hG p, Prod.snd_zero] using (ht (h p)).2.2.hasFDerivAt
    have heq : (fun y ↦ (G p (t p y,y)).1) =
        (fun y ↦ t (h p) (G p (t p y,y)).2) := funext (htgraph p)
    rw [heq] at hleft
    exact hleft.unique hright
  obtain ⟨hszero,htzero⟩ := parameter_graph_linear_tangent_zero h T₁ T₂ a k hgap hT₁ hT₂
    (fun p ↦ fderiv ℝ (s p) 0) (fun p ↦ fderiv ℝ (t p) 0)
    (fun p ↦ by simpa using norm_fderiv_le_of_lipschitz ℝ (hs p).2.1)
    (fun p ↦ by simpa using norm_fderiv_le_of_lipschitz ℝ (ht p).2.1) hse hte
  exact fun p ↦ ⟨hszero p,htzero p⟩

end HolomorphicAnosov
