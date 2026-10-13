import HolomorphicAnosov.Topology.BoundedDisplacementFixedPoint
import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Topology.InvertibleLinearLocalDegree
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homotopy.Path
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# BoundedPiDisplacementFixedPoint

Source context: the bounded-displacement step of Franks (1969),
Lemma 1.2, pp. 118–119. This coordinate transport is agent-written;
Mathlib's WithLp.linearEquiv and finite-dimensional continuity provide
the canonical continuous linear equivalence used in the proof.

Let e map EuclideanSpace R (Fin n) to Fin n → R by the unchanged
coordinates. Both directions are continuous although the norms differ.
Set GE = e.symm ∘ G ∘ e, BE = e.symm ∘ B ∘ e, and
LE = e.symm ∘ L ∘ e. Then LE is a continuous linear equivalence and
LE(x) = x - BE(x), by linearity and the given formula for L.
Moreover GE(x)-BE(x) = e.symm(G(e(x))-B(e(x))), whose Euclidean norm
is at most norm(e.symm) K by the operator norm estimate. This is a
nonnegative uniform bound. Apply bounded_displacement_fixed_point to
GE, BE, LE and obtain GE(x) = x. Applying e gives G(e(x)) = e(x),
the desired fixed point in the original Pi space. No equality between
the Pi and Euclidean norms is used. The same construction works for n=0.
-/

universe u

noncomputable section

open scoped ContDiff

namespace HolomorphicAnosov.Topology

/-- The bounded-displacement argument transports through the actual linear
coordinate equivalence between the Pi norm and the Euclidean norm; no equality
of these norms is asserted. -/
theorem bounded_pi_displacement_fixed_point (n : ℕ)
    (G : C((Fin n → ℝ), (Fin n → ℝ)))
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hL : ∀ x, L x = x - B x)
    (K : ℝ) (hK : 0 ≤ K) (hG : ∀ x, ‖G x - B x‖ ≤ K) : ∃ x, G x = x := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  let GE : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x ↦ e.symm (G (e x)), e.symm.continuous.comp (G.continuous.comp e.continuous)⟩
  let BE := e.symm.toContinuousLinearMap.comp (B.comp e.toContinuousLinearMap)
  let LE := e.trans (L.trans e.symm)
  have hLE : ∀ x, LE x = x - BE x := by
    intro x
    change e.symm (L (e x)) = x - e.symm (B (e x))
    rw [hL, map_sub, e.symm_apply_apply]
  have hGE : ∀ x, ‖GE x - BE x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * K := by
    intro x
    change ‖e.symm (G (e x)) - e.symm (B (e x))‖ ≤ _
    rw [← map_sub]
    exact (e.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hG (e x)) (norm_nonneg _))
  obtain ⟨x, hx⟩ := bounded_displacement_fixed_point n GE BE LE hLE
    (‖e.symm.toContinuousLinearMap‖ * K) (mul_nonneg (norm_nonneg _) hK) hGE
  refine ⟨e x, ?_⟩
  have h := congrArg e hx
  change e (e.symm (G (e x))) = e x at h
  simpa using h


end HolomorphicAnosov.Topology
