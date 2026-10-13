import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Linearization through maps avoiding zero near a regular point

Source: the local-degree linearization in Hatcher, *Algebraic Topology*,
§2.2 pp.134–136. The quantitative remainder argument is an agent-written
expansion of step 4 of `topo.disk_degree_local_homeomorphism_count`.
-/

noncomputable section
open Set Metric Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.Topology

/-- An invertible derivative gives a puncture-preserving homotopy on a sufficiently
small closed ball, from its linear model to the original displacement.

Proof: the remainder is little-o of the displacement from the basepoint. Since
the derivative is a continuous linear equivalence, it is also little-o of the
linear model. On some neighborhood its norm is at most one half of the linear
model's norm. Choose a positive closed ball inside that neighborhood and the
original open domain. The affine homotopy is linear model plus t times remainder.
At any point other than the basepoint the linear model has positive norm, whereas
the perturbation has at most half that norm for every t in [0,1]. Hence the homotopy
never vanishes there. Restricting the given continuous map to the ball makes this
a jointly continuous homotopy with the asserted exact endpoints. -/
theorem exists_derivative_punctured_disk_homotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E) (O : Set E) (hO : IsOpen O) (hg : ContinuousOn g O)
    (a : E) (ha : a ∈ O) (L : E ≃L[ℝ] E) (hL : HasFDerivAt g (L : E →L[ℝ] E) a) :
    ∃ (r : ℝ) (_hr : 0 < r) (hBO : closedBall a r ⊆ O),
      ∃ H : ContinuousMap.Homotopy
          (⟨fun z : closedBall a r ↦ L (z.val - a),
            L.continuous.comp (continuous_subtype_val.sub continuous_const)⟩ :
              C(closedBall a r, E))
          ⟨fun z ↦ g z.val - g a, (hg.mono hBO).domRestrict.sub continuous_const⟩,
        ∀ (t : unitInterval) (z : closedBall a r), z.val ≠ a → H (t, z) ≠ 0 := by
  have hsmall := (hL.isEquivalent_sub L.toHomeomorph.isEmbedding.isInducing).isLittleO.def
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hsmall.and (hO.mem_nhds ha))
  have hBO : closedBall a (r / 2) ⊆ O := by
    intro z hz
    exact (hball (lt_of_le_of_lt hz (show r / 2 < r by linarith))).2
  let F : C(closedBall a (r / 2), E) :=
    ⟨fun z ↦ L (z.val - a),
      L.continuous.comp (continuous_subtype_val.sub continuous_const)⟩
  let G : C(closedBall a (r / 2), E) :=
    ⟨fun z ↦ g z.val - g a, (hg.mono hBO).domRestrict.sub continuous_const⟩
  let H : F.Homotopy G :=
    { toFun := fun z ↦ F z.2 + (z.1 : ℝ) • (G z.2 - F z.2)
      continuous_toFun := by fun_prop
      map_zero_left := by intro z; simp
      map_one_left := by intro z; simp }
  refine ⟨r / 2, by linarith, hBO, H, ?_⟩
  intro t z hz hzero
  have hbound : ‖G z - F z‖ ≤ (1 / 2 : ℝ) * ‖F z‖ :=
    (hball (lt_of_le_of_lt z.property (show r / 2 < r by linarith))).1
  have hF : 0 < ‖F z‖ := norm_pos_iff.mpr (by
    intro he
    apply hz
    apply sub_eq_zero.mp
    exact L.injective (he.trans L.map_zero.symm))
  have hnorm : ‖(t : ℝ) • (G z - F z)‖ < ‖F z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    calc
      (t : ℝ) * ‖G z - F z‖ ≤ ‖G z - F z‖ :=
        mul_le_of_le_one_left (norm_nonneg _) t.property.2
      _ ≤ (1 / 2 : ℝ) * ‖F z‖ := hbound
      _ < ‖F z‖ := by linarith
  have heq : (t : ℝ) • (G z - F z) = -(F z) := eq_neg_of_add_eq_zero_right hzero
  rw [heq, norm_neg] at hnorm
  exact (lt_irrefl _) hnorm

end HolomorphicAnosov.Topology
