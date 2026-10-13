import HolomorphicAnosov.Topology.GeometricFaceAffineSpanHomeomorph
import HolomorphicAnosov.Topology.StandardCoordinateSimplexBody
import HolomorphicAnosov.Topology.StandardCoordinateSimplexClosedConvexBounded
import Mathlib.Geometry.Convex.ConvexSpace.Topology

namespace HolomorphicAnosov

open Set Topology _root_.Topology Metric
open scoped BigOperators
noncomputable section

abbrev faceCoordV (d : ℕ) := Fin d → ℝ

def faceCoordDelta (d : ℕ) : Set (faceCoordV d) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}

abbrev faceBaryExt (d : ℕ) : faceCoordV d → (Fin (d + 1) → ℝ) :=
  fun u => Fin.cases (1 - ∑ i, u i) u

abbrev faceBaryExtF (d : ℕ) : faceCoordV d → (Fin (d + 1) →₀ ℝ) :=
  fun u => Finsupp.equivFunOnFinite.symm (faceBaryExt d u)

abbrev faceBaryDrop (d : ℕ) : (Fin (d + 1) →₀ ℝ) → faceCoordV d :=
  fun w i => w i.succ

lemma faceBaryExt_sum (d : ℕ) (u : faceCoordV d) :
    ∑ j, faceBaryExt d u j = 1 := by
  rw [Fin.sum_univ_succ]
  simp [faceBaryExt, Fin.cases]

lemma faceBaryExt_nonneg (d : ℕ) {u : faceCoordV d} (hu : u ∈ faceCoordDelta d)
    (j : Fin (d + 1)) : 0 ≤ faceBaryExt d u j := by
  refine Fin.cases ?_ (fun i => hu.1 i) j
  dsimp [faceBaryExt]
  linarith [hu.2]

lemma faceBaryExt_drop (d : ℕ) (u : faceCoordV d) :
    faceBaryDrop d (faceBaryExtF d u) = u := by
  funext i
  rfl

lemma faceBaryDrop_ext (d : ℕ) (w : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    faceBaryExtF d (faceBaryDrop d w.weights) = w.weights := by
  apply Finsupp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · dsimp [faceBaryExtF, faceBaryExt, faceBaryDrop]
    rw [← w.total_of_fintype, Fin.sum_univ_succ]
    ring
  · rfl

lemma faceBaryDrop_mem (d : ℕ) {w : Convexity.StdSimplex ℝ (Fin (d + 1))} :
    faceBaryDrop d w.weights ∈ faceCoordDelta d := by
  constructor
  · intro i
    exact w.weights_nonneg i.succ
  · rw [← w.total_of_fintype, Fin.sum_univ_succ]
    linarith [w.weights_nonneg 0]

def faceDeltaStdEquiv (d : ℕ) :
    {u : faceCoordV d // u ∈ faceCoordDelta d} ≃ Convexity.StdSimplex ℝ (Fin (d + 1)) where
  toFun u :=
    ⟨faceBaryExtF d u, by
      intro j
      simpa using faceBaryExt_nonneg d u.property j, by
      simpa [Finsupp.sum_fintype] using faceBaryExt_sum d u⟩
  invFun w := ⟨faceBaryDrop d w.weights, faceBaryDrop_mem d (w := w)⟩
  left_inv u := Subtype.ext (faceBaryExt_drop d u)
  right_inv w := by
    apply Convexity.StdSimplex.ext
    exact faceBaryDrop_ext d w

lemma continuous_faceDeltaStdEquiv_symm (d : ℕ) :
    Continuous (faceDeltaStdEquiv d).symm := by
  apply Continuous.subtype_mk
  · change Continuous (fun w : Convexity.StdSimplex ℝ (Fin (d + 1)) =>
      faceBaryDrop d w.weights)
    fun_prop

lemma compact_faceCoordDelta (d : ℕ) :
    CompactSpace {u : faceCoordV d // u ∈ faceCoordDelta d} := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  obtain ⟨_, hclosed, hbounded, _, _, _⟩ := standard_coordinate_simplex_body d
  exact ⟨hclosed, hbounded⟩

/-- The normalized `Fin d` coordinate simplex is homeomorphic to the standard barycentric simplex on `Fin (d+1)`, by adjoining the coefficient `1 - ∑ u`. -/
noncomputable def face_delta_std_homeomorph (d : ℕ) :
    {u : faceCoordV d // u ∈ faceCoordDelta d} ≃ₜ
      Convexity.StdSimplex ℝ (Fin (d + 1)) := by
  letI := compact_faceCoordDelta d
  exact (Continuous.homeoOfEquivCompactToT2 (f := (faceDeltaStdEquiv d).symm)
    (continuous_faceDeltaStdEquiv_symm d)).symm

end
end HolomorphicAnosov
