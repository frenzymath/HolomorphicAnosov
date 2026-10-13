import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Finite coefficient model for bounded-degree real multivariate polynomials

This module supplies the finite-dimensional coefficient carrier used by the
Campanato normalized-polynomial compactness argument. The polynomial subtype
itself remains algebraic; compactness is taken on its explicit finite real
coefficient carrier.
-/

noncomputable section

namespace HolomorphicAnosov.Analysis.Regularity

/-- A bounded-total-degree real polynomial space has a finite real coefficient
model with compact unit sphere and continuous evaluation into the sup-norm
space of continuous functions on the closed Euclidean unit ball.

Source: Campanato (1964), Lemma [2.I], printed pp.140–141, coefficient
normalization (2.3) and uniform convergence on compact sets. This is an
agent-written implementation of that finite-dimensional step, using an
arbitrary finite basis and the finite Pi norm rather than the monomial
Euclidean coefficient norm; this auxiliary normalization does not change
any polynomial, domain, or statement of the parent estimate.

Proof: the bounded-degree polynomial submodule is finite over ℝ. A finite
basis gives a linear equivalence from Fin d→ℝ, whose unit sphere is compact.
Evaluation of each polynomial on the closed Euclidean ball is continuous.
Evaluation is linear in the coefficient parameter; finite-dimensional
continuity makes this a continuous linear map into C(closedBall,ℝ).
DAG node: analysis.polynomial_coefficient_compact_model_g18. -/
theorem polynomial_coefficient_compact_model (N n : ℕ) :
    ∃ d : ℕ,
      ∃ e : (Fin d → ℝ) ≃ₗ[ℝ]
        ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n),
        IsCompact (Metric.sphere (0 : Fin d → ℝ) 1) ∧
        ∃ T : (Fin d → ℝ) →L[ℝ]
          C(↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) 1), ℝ),
          ∀ c x, T c x = MvPolynomial.eval (fun i ↦ x.val i) ((e c).val) := by
  let V := ↥(MvPolynomial.restrictTotalDegree (Fin N) ℝ n)
  let e : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] V := (Module.finBasis ℝ V).equivFun.symm
  refine ⟨Module.finrank ℝ V, ⟨e, isCompact_sphere _ _, ?_⟩⟩
  let E := EuclideanSpace ℝ (Fin N)
  let B := ↥(Metric.closedBall (0 : E) 1)
  let T : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] C(B, ℝ) :=
    { toFun := fun c ↦
        ⟨fun x ↦ MvPolynomial.eval (fun i ↦ x.val i) (e c).val,
          ((AnalyticOnNhd.eval_continuousLinearMap'
            (fun i : Fin N ↦ PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N ↦ ℝ) i)
            (e c).val).continuous).comp continuous_subtype_val⟩
      map_add' := by
        intro c c'
        ext x
        change MvPolynomial.eval _ (e (c + c')).val =
          MvPolynomial.eval _ (e c).val + MvPolynomial.eval _ (e c').val
        rw [map_add]
        change MvPolynomial.eval _ ((e c).val + (e c').val) = _
        exact MvPolynomial.eval_add
      map_smul' := by
        intro r c
        ext x
        change MvPolynomial.eval _ (e (r • c)).val =
          r • MvPolynomial.eval _ (e c).val
        rw [map_smul]
        change MvPolynomial.eval _ (r • (e c).val) = _
        exact MvPolynomial.eval₂Hom_smul (RingHom.id ℝ) _ r (e c).val }
  exact ⟨⟨T, T.continuous_of_finiteDimensional⟩, fun _ _ ↦ rfl⟩

end HolomorphicAnosov.Analysis.Regularity
