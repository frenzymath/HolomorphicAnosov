import HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Radial collars of unions of simplex facets

DAG node: `topo.standard_simplex_face_union_collar_g20`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.22 p.124 and
Example 2.23 p.125. Explicit barycentric deformation supplies the good-pair
neighborhoods for the boundary and for unions of its facets.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- The topological boundary of the standard simplex, described by a zero
barycentric weight. -/
def standardSimplexBoundary (n : ℕ) : Set (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  {t | ∃ i, t.weights i = 0}

/-- The least weight among a nonempty family of simplex vertices. -/
def standardSimplexMinWeight (n : ℕ) (s : Finset (Fin (n + 2))) (hs : s.Nonempty)
    (x : Convexity.StdSimplex ℝ (Fin (n + 2))) : ℝ :=
  s.inf' hs (fun i ↦ x.weights i)

lemma standardSimplexMinWeight_nonneg (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    0 ≤ standardSimplexMinWeight n s hs x :=
  Finset.le_inf' _ _ (fun i _ ↦ x.weights_nonneg i)

lemma standardSimplexMinWeight_le (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (x : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (i : Fin (n + 2)) (hi : i ∈ s) :
    standardSimplexMinWeight n s hs x ≤ x.weights i := Finset.inf'_le _ hi

lemma standardSimplexMinWeight_continuous (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) : Continuous (standardSimplexMinWeight n s hs) :=
  Continuous.finset_inf'_apply hs (fun i _ ↦ Convexity.StdSimplex.continuous_weights_apply ℝ i)

/-- The union of the faces opposite the vertices in s. -/
def standardSimplexFaceUnion (n : ℕ) (s : Finset (Fin (n + 2))) :
    Set (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  {x | ∃ i ∈ s, x.weights i = 0}

lemma standardSimplexMinWeight_eq_zero_iff (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    standardSimplexMinWeight n s hs x = 0 ↔ x ∈ standardSimplexFaceUnion n s := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hs (fun i ↦ x.weights i)
    exact ⟨i, hi, he.symm.trans h⟩
  · rintro ⟨i, hi, he⟩
    exact le_antisymm (he ▸ standardSimplexMinWeight_le n s hs x i hi)
      (standardSimplexMinWeight_nonneg n s hs x)

/-- Remove the barycenter of the face spanned by s; this open set contains
all faces in the specified union. -/
def standardSimplexFaceUnionCollar (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) : Set (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  {x | (s.card : ℝ) * standardSimplexMinWeight n s hs x < 1}

lemma standardSimplexFaceUnionCollar_open (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) : IsOpen (standardSimplexFaceUnionCollar n s hs) :=
  isOpen_lt (continuous_const.mul (standardSimplexMinWeight_continuous n s hs)) continuous_const

lemma standardSimplexFaceUnion_subset_collar (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) : standardSimplexFaceUnion n s ⊆ standardSimplexFaceUnionCollar n s hs := by
  intro x hx
  change (s.card : ℝ) * standardSimplexMinWeight n s hs x < 1
  rw [(standardSimplexMinWeight_eq_zero_iff n s hs x).mpr hx]
  norm_num

lemma standardSimplexRadial_den_pos (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs) :
    0 < 1 - (s.card : ℝ) * (t : ℝ) * standardSimplexMinWeight n s hs x.val := by
  have hm := standardSimplexMinWeight_nonneg n s hs x.val
  have hc : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have ht := t.property.2
  have hx := x.property
  change (s.card : ℝ) * standardSimplexMinWeight n s hs x.val < 1 at hx
  nlinarith [mul_nonneg hc hm]

/-- Coordinates of radial deformation away from the barycenter of s. -/
def standardSimplexRadialWeight (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs)
    (i : Fin (n + 2)) : ℝ :=
  (x.val.weights i - if i ∈ s then (t : ℝ) * standardSimplexMinWeight n s hs x.val else 0) /
    (1 - (s.card : ℝ) * (t : ℝ) * standardSimplexMinWeight n s hs x.val)

lemma standardSimplexRadialWeight_nonneg (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs)
    (i : Fin (n + 2)) : 0 ≤ standardSimplexRadialWeight n s hs t x i := by
  apply div_nonneg _ (standardSimplexRadial_den_pos n s hs t x).le
  split_ifs with hi
  · have hm := standardSimplexMinWeight_nonneg n s hs x.val
    have hle := standardSimplexMinWeight_le n s hs x.val i hi
    have ht := t.property.2
    nlinarith
  · simp

lemma standardSimplexRadialWeight_sum (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs) :
    ∑ i, standardSimplexRadialWeight n s hs t x i = 1 := by
  simp only [standardSimplexRadialWeight, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib]
  rw [x.val.total_of_fintype]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [← div_eq_mul_inv]
  apply (div_eq_one_iff_eq (standardSimplexRadial_den_pos n s hs t x).ne').mpr
  ring

/-- The radial deformation as an actual standard-simplex point. -/
def standardSimplexRadial (n : ℕ) (s : Finset (Fin (n + 2))) (hs : s.Nonempty)
    (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs) :
    Convexity.StdSimplex ℝ (Fin (n + 2)) where
  weights := Finsupp.equivFunOnFinite.symm (standardSimplexRadialWeight n s hs t x)
  nonneg := standardSimplexRadialWeight_nonneg n s hs t x
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact standardSimplexRadialWeight_sum n s hs t x

lemma standardSimplexRadial_weights (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs)
    (i : Fin (n + 2)) :
    (standardSimplexRadial n s hs t x).weights i = standardSimplexRadialWeight n s hs t x i := rfl

lemma standardSimplexRadial_continuous (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) : Continuous (fun p : unitInterval × standardSimplexFaceUnionCollar n s hs ↦
      standardSimplexRadial n s hs p.1 p.2) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_def, standardSimplexRadial_weights, standardSimplexRadialWeight]
  have hw : Continuous (fun p : unitInterval × standardSimplexFaceUnionCollar n s hs ↦
      p.2.val.weights i) := (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
    (continuous_subtype_val.comp continuous_snd)
  have hm : Continuous (fun p : unitInterval × standardSimplexFaceUnionCollar n s hs ↦
      standardSimplexMinWeight n s hs p.2.val) :=
    (standardSimplexMinWeight_continuous n s hs).comp
      (continuous_subtype_val.comp continuous_snd)
  have ht : Continuous (fun p : unitInterval × standardSimplexFaceUnionCollar n s hs ↦
      (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  apply Continuous.div
  · split_ifs <;> fun_prop
  · exact continuous_const.sub ((continuous_const.mul ht).mul hm)
  · intro p
    exact (standardSimplexRadial_den_pos n s hs p.1 p.2).ne'

lemma standardSimplexRadial_zero (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (x : standardSimplexFaceUnionCollar n s hs) :
    standardSimplexRadial n s hs 0 x = x.val := by
  ext i
  simp [standardSimplexRadial_weights, standardSimplexRadialWeight]

lemma standardSimplexRadial_fixed (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs)
    (hx : x.val ∈ standardSimplexFaceUnion n s) :
    standardSimplexRadial n s hs t x = x.val := by
  ext i
  simp [standardSimplexRadial_weights, standardSimplexRadialWeight,
    (standardSimplexMinWeight_eq_zero_iff n s hs x.val).mpr hx]

lemma standardSimplexRadial_one_mem (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (x : standardSimplexFaceUnionCollar n s hs) :
    standardSimplexRadial n s hs 1 x ∈ standardSimplexFaceUnion n s := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hs (fun i ↦ x.val.weights i)
  refine ⟨i, hi, ?_⟩
  simp only [standardSimplexRadial_weights, standardSimplexRadialWeight, hi, ↓reduceIte,
    Set.Icc.coe_one, one_mul]
  change (x.val.weights i - s.inf' hs (fun i ↦ x.val.weights i)) / _ = 0
  rw [he, sub_self, zero_div]

/-- Radial deformation preserves the simplex boundary; a vanishing coordinate
outside the selected vertices stays zero, and one inside forces the minimum zero. -/
lemma standardSimplexRadial_mem_boundary (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs)
    (hx : x.val ∈ standardSimplexBoundary n) :
    standardSimplexRadial n s hs t x ∈ standardSimplexBoundary n := by
  obtain ⟨i, hi⟩ := hx
  by_cases his : i ∈ s
  · rw [standardSimplexRadial_fixed n s hs t x ⟨i, his, hi⟩]
    exact ⟨i, hi⟩
  · refine ⟨i, ?_⟩
    simp [standardSimplexRadial_weights, standardSimplexRadialWeight, his, hi]

lemma standardSimplexRadial_mem_collar (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) (t : unitInterval) (x : standardSimplexFaceUnionCollar n s hs) :
    standardSimplexRadial n s hs t x ∈ standardSimplexFaceUnionCollar n s hs := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hs (fun i ↦ x.val.weights i)
  have hm : x.val.weights i = standardSimplexMinWeight n s hs x.val := he.symm
  have hle := standardSimplexMinWeight_le n s hs (standardSimplexRadial n s hs t x) i hi
  have hc : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hlt : (s.card : ℝ) * (standardSimplexRadial n s hs t x).weights i < 1 := by
    rw [standardSimplexRadial_weights]
    unfold standardSimplexRadialWeight
    rw [ite_eq_left hi, hm, ← mul_div_assoc]
    apply (div_lt_one (standardSimplexRadial_den_pos n s hs t x)).mpr
    have hx := x.property
    change (s.card : ℝ) * standardSimplexMinWeight n s hs x.val < 1 at hx
    nlinarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hc) hlt

/-- The union of a nonempty family of faces is a strong deformation retract
of its open radial collar. The minimum coordinate reaches zero at time one,
and a point already on a selected face remains fixed at every time. -/
def standardSimplexFaceUnionRetract (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) :
    HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
      (standardSimplexFaceUnion n s) (standardSimplexFaceUnionCollar n s hs)
      (standardSimplexFaceUnion_subset_collar n s hs) where
  retraction := ⟨fun x ↦ ⟨standardSimplexRadial n s hs 1 x,
    standardSimplexRadial_one_mem n s hs x⟩,
    ((standardSimplexRadial_continuous n s hs).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  retraction_inclusion := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact standardSimplexRadial_fixed n s hs 1 _ x.property
  homotopy := {
    toFun := fun p ↦ ⟨standardSimplexRadial n s hs p.1 p.2,
      standardSimplexRadial_mem_collar n s hs p.1 p.2⟩
    continuous_toFun := (standardSimplexRadial_continuous n s hs).subtype_mk _
    map_zero_left := by intro x; apply Subtype.ext; exact standardSimplexRadial_zero n s hs x
    map_one_left := by intro x; rfl
    prop' := by
      intro t x hx
      apply Subtype.ext
      exact standardSimplexRadial_fixed n s hs t x hx }

/-- Forget the boundary condition on a point of the radial collar. -/
def standardSimplexBoundaryCollarForget (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) :
    C({x : standardSimplexBoundary n // x.val ∈ standardSimplexFaceUnionCollar n s hs},
      standardSimplexFaceUnionCollar n s hs) where
  toFun x := ⟨x.val.val, x.property⟩
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The radial deformation restricted to the boundary collar. -/
def standardSimplexBoundaryRadial (n : ℕ) (s : Finset (Fin (n + 2))) (hs : s.Nonempty) :
    C(unitInterval × {x : standardSimplexBoundary n // x.val ∈ standardSimplexFaceUnionCollar n s hs},
      standardSimplexBoundary n) where
  toFun p := ⟨standardSimplexRadial n s hs p.1 (standardSimplexBoundaryCollarForget n s hs p.2),
    standardSimplexRadial_mem_boundary n s hs p.1 _ p.2.val.property⟩
  continuous_toFun := ((standardSimplexRadial_continuous n s hs).comp
    (continuous_fst.prodMk
      ((standardSimplexBoundaryCollarForget n s hs).continuous.comp continuous_snd))).subtype_mk _

/-- The same radial collar deformation restricted to the boundary. -/
def standardSimplexBoundaryFaceUnionRetract (n : ℕ) (s : Finset (Fin (n + 2)))
    (hs : s.Nonempty) :
    HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
      (fun x : standardSimplexBoundary n ↦ x.val ∈ standardSimplexFaceUnion n s)
      (fun x : standardSimplexBoundary n ↦ x.val ∈ standardSimplexFaceUnionCollar n s hs)
      (fun _ hx ↦ standardSimplexFaceUnion_subset_collar n s hs hx) where
  retraction := ⟨fun x ↦ ⟨standardSimplexBoundaryRadial n s hs (1, x),
    standardSimplexRadial_one_mem n s hs _⟩,
      ((standardSimplexBoundaryRadial n s hs).continuous.comp
        (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  retraction_inclusion := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact standardSimplexRadial_fixed n s hs 1 _ x.property
  homotopy := {
    toFun := fun p ↦ ⟨standardSimplexBoundaryRadial n s hs p,
      standardSimplexRadial_mem_collar n s hs p.1 _⟩
    continuous_toFun := (standardSimplexBoundaryRadial n s hs).continuous.subtype_mk _
    map_zero_left := by
      intro x; apply Subtype.ext; apply Subtype.ext
      exact standardSimplexRadial_zero n s hs _
    map_one_left := by intro x; rfl
    prop' := by
      intro t x hx
      apply Subtype.ext; apply Subtype.ext
      exact standardSimplexRadial_fixed n s hs t _ hx }

lemma standardSimplexFaceUnion_closed (n : ℕ) (s : Finset (Fin (n + 2))) :
    IsClosed (standardSimplexFaceUnion n s) := by
  have h := isClosed_biUnion_finset (s := s)
    (f := fun i ↦ {x | (x : Convexity.StdSimplex ℝ (Fin (n + 2))).weights i = 0})
    (fun i _ ↦ isClosed_eq (Convexity.StdSimplex.continuous_weights_apply ℝ i) continuous_const)
  convert h using 1
  ext x
  simp [standardSimplexFaceUnion]

lemma standardSimplexBoundary_closed (n : ℕ) : IsClosed (standardSimplexBoundary n) := by
  simpa [standardSimplexFaceUnion, standardSimplexBoundary] using
    standardSimplexFaceUnion_closed n Finset.univ

lemma standardSimplexBoundary_nonempty (n : ℕ) : (standardSimplexBoundary n).Nonempty := by
  refine ⟨Convexity.StdSimplex.single 0, 1, ?_⟩
  simp [Convexity.StdSimplex.weights_single]

end HolomorphicAnosov
