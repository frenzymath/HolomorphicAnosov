import HolomorphicAnosov.Analysis.Distribution.MollifierRegularization

/-!
# Compact subsets stay inside small mollifier domains

Source: James R. Munkres, Topology, second edition (2000), §27, Theorem27.4 p.174 and
distance-function/positive-minimum proof of Lemma27.5 pp.175–176, specialized to the distance from
a compact subset of an open set to its complement.
DAG node: `analysis.dbar_helper_compact_eventually_subset_mollifier_domain_g6`.
-/

open Set TopologicalSpace
open scoped ENNReal

namespace HolomorphicAnosov.Analysis.Distribution

/--
For a compact subset K of an open Euclidean domain U, there is a positive real delta such that K
is contained in mollifierDomain U epsilon whenever epsilon is less than delta, including negative
epsilon.

Source: Munkres (2000), §27, Theorem27.4 p.174 and distance-function/positive-minimum proof of
Lemma27.5 pp.175–176, specialized to the distance from a compact subset of an open set to its
complement.

Proof: If K is empty choose delta one; all inclusions are vacuous. If the complement of U is empty
choose delta one; its extended distance is infinity. Otherwise use the real-valued distance to
that nonempty closed complement. Munkres proves continuity of a distance function by the triangle
inequality, positivity at an interior point by a ball inside the open set, and the
positive-minimum method on a compact set in the proof of Lemma27.5. Apply Theorem27.4 to this
single continuous distance function restricted to nonempty K and choose a minimizing point a. The
complement is closed and a belongs to U, so delta, its distance to the complement, is positive.
Every x in K has distance at least delta. Thus epsilon less than delta is strictly less than the
distance at x; conversion to nonnegative extended distance preserves this strict inequality, also
for negative epsilon because the distance is positive. Combine this bound with x in U, exactly the
two defining conditions of mollifierDomain. This uses the same written minimum argument with one
ambient complement distance, rather than the finite-cover average used for the general
Lebesgue-number conclusion.
-/
theorem compact_eventually_subset_mollifierDomain {m : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ > (0 : ℝ), ∀ ε : ℝ, ε < δ → K ⊆ mollifierDomain U ε := by
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · subst K
    exact ⟨1, zero_lt_one, by simp⟩
  rcases ((U : Set (EuclideanSpace ℝ (Fin m)))ᶜ).eq_empty_or_nonempty with hFull | hComplement
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε x hx
    refine ⟨hKU hx, ?_⟩
    simp only [hFull, Metric.infEDist_empty, ENNReal.ofReal_lt_top]
  obtain ⟨a, haK, hmin⟩ := hK.exists_isMinOn hNonempty
    (Metric.continuous_infDist_pt (U : Set _)ᶜ).continuousOn
  have hpositive : 0 < Metric.infDist a (U : Set _)ᶜ :=
    (U.isOpen.isClosed_compl.notMem_iff_infDist_pos hComplement).mp
      (by simpa using hKU haK)
  refine ⟨Metric.infDist a ((U : Set (EuclideanSpace ℝ (Fin m)))ᶜ), hpositive, ?_⟩
  intro ε hε x hx
  change x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x (U : Set _)ᶜ
  refine ⟨hKU hx, ?_⟩
  have hbound : ε < Metric.infDist x (U : Set _)ᶜ := hε.trans_le (hmin hx)
  have hlt : ENNReal.ofReal ε < ENNReal.ofReal (Metric.infDist x (U : Set _)ᶜ) :=
    (ENNReal.ofReal_lt_ofReal_iff (hpositive.trans_le (hmin hx))).mpr hbound
  exact hlt.trans_le ENNReal.ofReal_toReal_le


end HolomorphicAnosov.Analysis.Distribution
