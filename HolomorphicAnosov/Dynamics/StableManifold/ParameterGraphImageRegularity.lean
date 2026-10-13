import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSmoothInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open scoped ContDiff ENat NNReal Topology _root_.Topology
namespace HolomorphicAnosov

/-- HPS, *Invariant Manifolds*, pp.54–55: the image graph transform preserves
finite C^r smoothness. For a C^r unit-slope graph s, the horizontal image H is
C^r and its difference from T is ε-Lipschitz. Wells's perturbation inverse
argument gives C^r smoothness of H⁻¹. The transformed graph has formula
u↦G₂(H⁻¹(u),s(H⁻¹(u))), hence is C^r by composition. Graph image equality
identifies any given output graph with this formula. This proves smoothness
of one transform step, not smoothness of its eventual fixed graph. -/
theorem parameter_graph_image_regularity
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (r : ℕ∞) (hr : 1 ≤ r) (hG : ContDiff ℝ (r : ℕ∞ω) G)
    (a ε : NNReal) (hT : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : (a : ℝ) * ε < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1,S z.2)))
    (s : X → Y) (hs : LipschitzWith 1 s) (hsc : ContDiff ℝ (r : ℕ∞ω) s)
    (H : X ≃ₜ U) (hH : ∀ x, H x = (G (x,s x)).1)
    (s' : U → V) (himage : G '' Set.range (fun x ↦ (x,s x)) =
      Set.range (fun u ↦ (u,s' u))) :
    ContDiff ℝ (r : ℕ∞ω) (H.symm : U → X) ∧ ContDiff ℝ (r : ℕ∞ω) s' := by
  have hpair : ContDiff ℝ (r : ℕ∞ω) (fun x ↦ (x,s x)) := contDiff_id.prodMk hsc
  have hHc : ContDiff ℝ (r : ℕ∞ω) (H : X → U) := by
    have he : (H : X → U) = fun x ↦ (G (x,s x)).1 := funext hH
    rw [he]
    exact (hG.comp hpair).fst
  have hpairlip : LipschitzWith 1 (fun x ↦ (x,s x)) := by
    simpa using LipschitzWith.id.prodMk hs
  have hHlip : LipschitzWith ε (fun x ↦ H x - T x) := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro x y
    have hb := (norm_fst_le _).trans ((hR.comp hpairlip).norm_sub_le x y)
    simpa only [hH, Function.comp_apply, Prod.fst_sub, NNReal.coe_mul, NNReal.coe_one, mul_one] using hb
  have hHi := parameter_graph_smooth_inverse T H r hr hHc a ε hT hsmall hHlip
  refine ⟨hHi,?_⟩
  have heq : s' = fun u ↦ (G (H.symm u,s (H.symm u))).2 := by
    funext u
    have hmem : G (H.symm u,s (H.symm u)) ∈ Set.range (fun v ↦ (v,s' v)) := by
      rw [← himage]
      exact ⟨(H.symm u,s (H.symm u)),⟨H.symm u,rfl⟩,rfl⟩
    obtain ⟨v,hv⟩ := hmem
    have hfst := congrArg Prod.fst hv
    have hvu : v = u := by
      simpa only [Prod.fst, ← hH, H.apply_symm_apply] using hfst
    have hsnd := congrArg Prod.snd hv
    simpa only [Prod.snd, hvu] using hsnd
  rw [heq]
  exact ((hG.comp hpair).snd).comp hHi

end HolomorphicAnosov
