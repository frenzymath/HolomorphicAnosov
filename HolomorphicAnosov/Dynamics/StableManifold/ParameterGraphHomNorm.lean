import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operator norms in parameter-graph fibre charts

Source: Hirsch–Pugh–Shub, Invariant Manifolds (1977), p.35 and pp.61–62;
Mathlib continuous-linear-map composition estimates.
DAG node: `hps.parameter_graph_hom_norm_g12`.
-/

noncomputable section
namespace HolomorphicAnosov

/-- HPS p.35 and pp.61–62: operator norms in genuine fibre charts are
locally comparable. For source coordinates `e₁ : U ≃L X` and target
coordinates `e₂ : Y ≃L V`, the model operator is
`e₂ ∘ P ∘ e₁`; its norm is bounded by the product of the three operator
norms. Reversing the coordinate changes gives the converse bound. These
inequalities apply to differences of operators as well, and include
zero-dimensional models. -/
theorem parameter_graph_hom_norm_comparison
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : X →L[ℝ] Y) (e₁ : U ≃L[ℝ] X) (e₂ : Y ≃L[ℝ] V) :
    ‖e₂.toContinuousLinearMap.comp (P.comp e₁.toContinuousLinearMap)‖ ≤
        ‖e₂.toContinuousLinearMap‖ * ‖P‖ * ‖e₁.toContinuousLinearMap‖ ∧
    ‖P‖ ≤ ‖e₂.symm.toContinuousLinearMap‖ *
        ‖e₂.toContinuousLinearMap.comp (P.comp e₁.toContinuousLinearMap)‖ *
        ‖e₁.symm.toContinuousLinearMap‖ := by
  constructor
  · calc
      _ ≤ ‖e₂.toContinuousLinearMap‖ * ‖P.comp e₁.toContinuousLinearMap‖ :=
        e₂.toContinuousLinearMap.opNorm_comp_le _
      _ ≤ ‖e₂.toContinuousLinearMap‖ * (‖P‖ * ‖e₁.toContinuousLinearMap‖) :=
        mul_le_mul_of_nonneg_left (P.opNorm_comp_le _) (norm_nonneg _)
      _ = _ := by ring
  · let Q : U →L[ℝ] V := e₂.toContinuousLinearMap.comp (P.comp e₁.toContinuousLinearMap)
    let R : X →L[ℝ] V := Q.comp e₁.symm.toContinuousLinearMap
    have hcomp' : e₂.symm.toContinuousLinearMap.comp R = P := by
      ext x
      simp [R, Q]
    have hR : ‖R‖ ≤ ‖Q‖ * ‖e₁.symm.toContinuousLinearMap‖ := by
      exact Q.opNorm_comp_le _
    calc
      ‖P‖ = ‖e₂.symm.toContinuousLinearMap.comp R‖ := by rw [hcomp']
      _ ≤ ‖e₂.symm.toContinuousLinearMap‖ * ‖R‖ :=
        e₂.symm.toContinuousLinearMap.opNorm_comp_le _
      _ ≤ ‖e₂.symm.toContinuousLinearMap‖ *
          (‖Q‖ * ‖e₁.symm.toContinuousLinearMap‖) :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)
      _ = _ := by ring

/-- The original operator norm is continuous along a continuous Hom field.
Source: Mathlib `Continuous.norm`; HPS p.35 and pp.61–62.
For this statement the source and target normed spaces are fixed: composing
the supplied continuous operator field with the continuous norm proves the claim.
This does not assert continuity for an arbitrary varying family of fibre norms. -/
theorem parameter_graph_hom_norm_continuous
    {Z X Y : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (P : Z → X →L[ℝ] Y) (hP : Continuous P) :
    Continuous (fun z ↦ ‖P z‖) := hP.norm

end HolomorphicAnosov
