import HolomorphicAnosov.Topology.EuclideanPositiveSimplexEmbedding
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Separation.Hausdorff

noncomputable section

namespace HolomorphicAnosov

/-- The prescribed positive affine simplex is embedded, and its image contains an
ambient neighborhood of zero, in every dimension including zero.

Source: Hatcher, *Algebraic Topology*, local orientations pp.233–234 and the
ordered affine-simplex convention p.269. The displayed coordinates are the project's
explicit simplex choice; the following barycentric verification is agent-written.

For an image point z put c(z)=(1−Σz_j)/(n+1). Coordinate recovery gives t₀=c(z)
and t_(j+1)=z_j+c(z), so the simplex map is injective. Its domain is compact,
hence the continuous injection is a closed embedding. Conversely these formulas
define a simplex point whenever all their values are nonnegative: they sum to one.
All values are 1/(n+1)>0 at zero, and depend continuously on z. The finite intersection
where all values are strictly positive is an open neighborhood of zero contained in
the simplex image. In dimension zero the same formula gives its sole weight 1. -/
theorem euclideanPositiveSimplex_embedded_interior (n : ℕ) :
    Topology.IsClosedEmbedding (euclideanPositiveSimplex n) ∧
      (0 : EuclideanSpace ℝ (Fin n)) ∈ interior (Set.range (euclideanPositiveSimplex n)) := by
  classical
  refine ⟨euclideanPositiveSimplex_isClosedEmbedding n, ?_⟩
  let c : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦
    (1 - ∑ j : Fin n, z j) / (n + 1 : ℝ)
  let w : EuclideanSpace ℝ (Fin n) → Fin (n + 1) → ℝ := fun z ↦
    Fin.cases (c z) (fun j ↦ z j + c z)
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hw (i : Fin (n + 1)) : Continuous (fun z ↦ w z i) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hc
    · change Continuous (fun z ↦ z j + c z)
      fun_prop
  let U : Set (EuclideanSpace ℝ (Fin n)) := {z | ∀ i, 0 < w z i}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i ↦ isOpen_lt continuous_const (hw i))
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [w, c] <;> positivity
  have hsub : U ⊆ Set.range (euclideanPositiveSimplex n) := by
    intro z hz
    have hsum : ∑ i : Fin (n + 1), w z i = 1 := by
      simp only [w, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp [c]
      field_simp
      ring
    have hex : w z ∈ Set.range
        (fun t ↦ t.weights : Convexity.StdSimplex ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ)) := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      exact ⟨Set.mem_iInter.mpr (fun i ↦ (hz i).le), hsum⟩
    obtain ⟨t, ht⟩ := hex
    refine ⟨t, ?_⟩
    ext j
    change t.weights j.succ - t.weights 0 = z j
    have h0 := congrFun ht 0
    have hj := congrFun ht j.succ
    simp only [w, Fin.cases_zero, Fin.cases_succ] at h0 hj
    linarith
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hzero) hsub)

end HolomorphicAnosov
