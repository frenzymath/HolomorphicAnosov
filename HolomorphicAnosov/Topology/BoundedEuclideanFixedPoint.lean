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
# BoundedEuclideanFixedPoint

Source: Dold (1965), definitions 1.1–1.2 and units 1.4, p. 1,
and homotopy invariance 1.7, p. 2. This bounded-map application is an
agent-written specialization of those laws; Franks (1969), Lemma 1.2,
pp. 118–119, provides the bounded-support existence context.

Put U = R^n and H(x,t) = t G(x) for 0 ≤ t ≤ 1. This map is jointly
continuous. If H(x,t) = x, then norm(x) = t norm(G(x)) ≤ K.
The total fixed set is a closed equality locus in U × [0,1], contained
in closedBall(0,K) × [0,1]; the latter is compact in finite dimension.
Thus the total fixed set is compact, and so are the endpoint fixed sets.
Dold's common-support homotopy law gives index(G) = index(constant 0).
The constant has its value inside U, so units gives index one. If G had
no fixed point, its support would be empty and the index would be zero,
a contradiction. This reasoning also covers K = 0 and n = 0; no positive
radius, isolated fixed points, or positive dimension is required.
-/

universe u

noncomputable section

open scoped ContDiff

namespace HolomorphicAnosov.Topology

/-- Dold's constant-map and compact-total-support homotopy laws give a fixed point
for a bounded continuous Euclidean self-map.  All fixed pairs of tG lie in one closed ball. -/
theorem bounded_euclidean_fixed_point (n : ℕ)
    (G : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (K : ℝ) (_hK : 0 ≤ K) (hG : ∀ x, ‖G x‖ ≤ K) : ∃ x, G x = x := by
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⊤
  let g : C(U, EuclideanSpace ℝ (Fin n)) := G.comp ⟨Subtype.val, continuous_subtype_val⟩
  let H : C(U × unitInterval, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun p ↦ (p.2 : ℝ) • g p.1,
      (continuous_subtype_val.comp continuous_snd).smul (g.continuous.comp continuous_fst)⟩
  let ball : Set U := Subtype.val ⁻¹' Metric.closedBall 0 K
  have hball : IsCompact ball := by
    have heq : ball = (fun x : EuclideanSpace ℝ (Fin n) ↦ (⟨x, by trivial⟩ : U)) ''
        Metric.closedBall 0 K := by
      ext x
      constructor
      · intro hx; exact ⟨x.val, hx, Subtype.ext rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact hy
    rw [heq]
    exact (isCompact_closedBall 0 K).image (continuous_id.subtype_mk _)
  have hclosed : IsClosed {p : U × unitInterval | H p = p.1.val} :=
    isClosed_eq H.continuous (continuous_subtype_val.comp continuous_fst)
  have hsupport : IsCompact {p : U × unitInterval | H p = p.1.val} := by
    apply (hball.prod isCompact_univ).of_isClosed_subset hclosed
    intro p hp
    constructor
    · change dist p.1.val 0 ≤ K
      rw [dist_zero_right]
      rw [← hp]
      change ‖(p.2 : ℝ) • g p.1‖ ≤ K
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.2.property.1]
      exact (mul_le_mul_of_nonneg_right p.2.property.2 (norm_nonneg _)).trans
        (by change 1 * ‖G p.1.val‖ ≤ K; simpa only [one_mul] using hG p.1.val)
    · trivial
  have laws := euclidean_fixed_point_index_basic_laws
  obtain ⟨h0, h1, hindex⟩ := laws.2.1 n U H hsupport
  have hzero : H.comp ⟨fun x : U ↦ (x, (0 : unitInterval)),
      continuous_id.prodMk continuous_const⟩ = ContinuousMap.const U 0 := by
    ext x; simp [H]
  have hone : H.comp ⟨fun x : U ↦ (x, (1 : unitInterval)),
      continuous_id.prodMk continuous_const⟩ = g := by
    ext x; simp [H]
  change IsCompact (euclideanFixedSet (H.comp _)) at h0
  change IsCompact (euclideanFixedSet (H.comp _)) at h1
  change euclideanFixedPointIndex (H.comp _) h0 = euclideanFixedPointIndex (H.comp _) h1 at hindex
  simp only [hzero, hone] at h0 h1 hindex
  obtain ⟨hc, hic⟩ := laws.2.2.2.1 n U 0 (by trivial)
  have hnonzero : euclideanFixedPointIndex g h1 ≠ 0 := by
    rw [← hindex, hic]; norm_num
  by_contra hno
  have hempty : euclideanFixedSet g = ∅ := by
    ext x
    simp only [euclideanFixedSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ hno ⟨x.val, h⟩
  exact hnonzero ((laws.1 n U g h1).2.1 hempty)


end HolomorphicAnosov.Topology
