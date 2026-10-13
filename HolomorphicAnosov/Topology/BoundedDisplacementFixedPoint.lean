import HolomorphicAnosov.Topology.BoundedEuclideanFixedPoint
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
# BoundedDisplacementFixedPoint

Source context: Franks (1969), Lemma 1.2, pp. 118–119. The
following bounded-correction reduction is agent-written, using Dold's
bounded-map existence argument in bounded_euclidean_fixed_point. It is
not asserted to be Franks's printed straight-line homotopy.

Let C(x) = L.symm(G(x) - B(x)), where L(x) = x - B(x). Continuity of
G, B, and L.symm makes C continuous. The operator norm inequality gives
norm(C(x)) ≤ norm(L.symm) norm(G(x)-B(x)) ≤ norm(L.symm) K for every x.
The final bound is nonnegative, since both factors are nonnegative.
Apply bounded_euclidean_fixed_point to C with this bound and obtain x
with C(x) = x. Applying L and cancelling the inverse gives
G(x)-B(x) = L(x) = x-B(x). Cancellation of B(x) yields G(x) = x.
The argument uses the given continuous inverse and works also in zero
dimension or when K is zero; it never divides by an operator norm.
-/

universe u

noncomputable section

open scoped ContDiff

namespace HolomorphicAnosov.Topology

/-- The bounded-correction fixed point is exactly a fixed point of the original
map whenever the ORIGINAL linear displacement I−B is invertible. -/
theorem bounded_displacement_fixed_point (n : ℕ)
    (G : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : ∀ x, L x = x - B x)
    (K : ℝ) (hK : 0 ≤ K) (hG : ∀ x, ‖G x - B x‖ ≤ K) : ∃ x, G x = x := by
  let correction : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x ↦ L.symm (G x - B x), L.symm.continuous.comp (G.continuous.sub B.continuous)⟩
  obtain ⟨x, hx⟩ := bounded_euclidean_fixed_point n correction (‖L.symm.toContinuousLinearMap‖ * K)
    (mul_nonneg (norm_nonneg _) hK) (fun x ↦
      (L.symm.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hG x) (norm_nonneg _)))
  have h := congrArg L hx
  change L (L.symm (G x - B x)) = L x at h
  rw [L.apply_symm_apply, hL] at h
  exact ⟨x, (sub_left_inj.mp h)⟩


end HolomorphicAnosov.Topology
