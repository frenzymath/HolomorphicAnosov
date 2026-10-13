import HolomorphicAnosov.Analysis.Regularity.MontgomeryDirectionalDerivativeDenseJointContinuity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace HolomorphicAnosov.Analysis.Regularity
open Filter
open scoped Topology _root_.Topology ContDiff

/-- Montgomery's dense-parameter derivative lemma for a finite-dimensional vector-valued family. (Montgomery, 1945) -/
theorem montgomery_finiteDimensional_derivative_dense_joint_continuity
    {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (W : Set V) (hW : IsOpen W) (a : E) (R : ℝ)
    (g : V → E → F)
    (hg : ContinuousOn (fun p : V × E ↦ g p.1 p.2) (W ×ˢ Metric.ball a R))
    (hsmooth : ∀ v ∈ W, ∀ y ∈ Metric.ball a R, ContDiffAt ℝ 1 (g v) y)
    (y : E) (hy : y ∈ Metric.ball a R) :
    Dense {v : W | ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (g p.1) p.2) (v.val, y)} := by
  let b := Module.finBasis ℝ E
  let c := Module.finBasis ℝ F
  have hentry (i : Fin (Module.finrank ℝ F)) (j : Fin (Module.finrank ℝ E)) :=
    montgomery_directional_derivative_dense_joint_continuity W hW a R (b j)
      (fun p ↦ c.equivFunL (g p.1 p.2) i)
      (fun p ↦ c.equivFunL (fderiv ℝ (g p.1) p.2 (b j)) i)
      (((continuous_apply i).comp c.equivFunL.continuous).comp_continuousOn hg)
      (by
        intro v hv z hz
        have hline : HasDerivAt (fun t : ℝ ↦ z + t • b j) (b j) 0 := by
          have hd := (hasFDerivAt_const z (0 : ℝ)).add
            (ContinuousLinearMap.toSpanSingleton ℝ (b j)).hasFDerivAt
          simpa [Pi.add_def] using hd.hasDerivAt
        have hd := (hsmooth v hv z hz).differentiableAt_one.hasFDerivAt
          |>.comp_hasDerivAt_of_eq 0 hline (by simp)
        let l : F →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp c.equivFunL.toContinuousLinearMap
        simpa [l, Function.comp_def] using l.hasFDerivAt.comp_hasDerivAt 0 hd)
      (by
        intro v hv z hz
        have hd := (hsmooth v hv z hz).continuousAt_fderiv (by norm_num)
        exact ((continuous_apply i).continuousAt.comp (c.equivFunL.continuousAt.comp
          (hd.clm_apply continuousAt_const))).continuousWithinAt)
      y hy
  have : BaireSpace W := hW.baireSpace
  have hd := dense_iInter_of_Gδ
    (fun q : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ E) ↦ (hentry q.1 q.2).2)
    (fun q : Fin (Module.finrank ℝ F) × Fin (Module.finrank ℝ E) ↦ (hentry q.1 q.2).1)
  apply hd.mono
  intro v hv
  have hb (j : Fin (Module.finrank ℝ E)) : ContinuousAt
      (fun p : V × E ↦ fderiv ℝ (g p.1) p.2 (b j)) (v.val, y) := by
    have hc : ContinuousAt
        (fun p : V × E ↦ c.equivFunL (fderiv ℝ (g p.1) p.2 (b j))) (v.val, y) := by
      apply continuousAt_pi.mpr
      intro i
      have hh : ContinuousWithinAt
          (fun p : V × E ↦ c.equivFunL (fderiv ℝ (g p.1) p.2 (b j)) i)
          (W ×ˢ Metric.ball a R) (v.val, y) := Set.mem_iInter.mp hv (i, j)
      exact hh.continuousAt ((hW.prod Metric.isOpen_ball).mem_nhds ⟨v.property, hy⟩)
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      c.equivFunL.symm.continuousAt.comp hc
  change ContinuousAt (fun p : V × E ↦ fderiv ℝ (g p.1) p.2) (v.val, y)
  apply continuousAt_clm_apply.mpr
  intro z
  have hc : ContinuousAt
      (fun p : V × E ↦ ∑ j, b.repr z j • fderiv ℝ (g p.1) p.2 (b j)) (v.val, y) :=
    tendsto_finsetSum Finset.univ (fun j _ ↦ (hb j).const_smul (b.repr z j))
  simpa only [← map_smul, ← map_sum, b.sum_repr] using hc
end HolomorphicAnosov.Analysis.Regularity
