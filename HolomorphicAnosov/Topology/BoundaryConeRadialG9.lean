import HolomorphicAnosov.Topology.BoundaryConeCarrierG9

/-!
# Radial coordinates on a literal boundary cone

Gallier--Xu Chapter 2, geometric realization, and Theorems 5.1--5.2,
pp.72--74. This explicit coordinate construction is an agent supplement to
the capping argument: base points lie on the original simplicial boundary
cycle and radial parameter one collapses to the fresh vertex.
-/
open Set
open scoped BigOperators Classical
namespace HolomorphicAnosov.Topology.GallierXu

/-- Barycentric radial coordinates: shrink the old coordinates by `1-t` and
put mass `t` at the fresh apex. -/
def boundaryConeRadial {N : ℕ} (x : Fin N → ℝ) (t : ℝ) : Fin (N + 1) → ℝ :=
  Fin.snoc (α := fun _ ↦ ℝ) (fun i ↦ (1 - t) * x i) t

/-- Every radial point above an original boundary-cycle point belongs to the
literal cone attachment. The boundary edge supporting the base point and
the fresh apex together support the radial point in one actual cone triangle. -/
theorem boundaryConeRadial_mem_carrier_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (x : ↥(carrier K)) (hx : x ∈ cycleCarrier l) {t : ℝ} (ht : t ∈ Icc 0 1) :
    boundaryConeRadial x.val t ∈ carrier (attachBoundaryCone K l) := by
  classical
  obtain ⟨u, v, hedge, a, b, ha, hb, hab, heq⟩ := hx
  have hzero (w : Fin N) (hu : w ≠ u) (hv : w ≠ v) : x.val w = 0 := by
    have he := congrFun heq w
    simpa [Pi.single_apply, hu, hv, Ne.symm hu, Ne.symm hv] using he.symm
  have hsimplex : boundaryConeRadial x.val t ∈
      {f : Fin (N + 1) → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1} := by
    refine ⟨?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [boundaryConeRadial] using ht.1
      | cast i =>
        simpa [boundaryConeRadial] using mul_nonneg (sub_nonneg.mpr ht.2) (x.property.1.1 i)
    · simp only [boundaryConeRadial, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        ← Finset.mul_sum, x.property.1.2, mul_one]
      ring
  obtain ⟨i, h | h⟩ := hedge
  all_goals
    refine ⟨hsimplex, boundaryConeTriangle l i, boundaryConeTriangle_face_g9 K l i, ?_⟩
    intro w hw
    cases w using Fin.lastCases with
    | last => exact (hw (boundaryConeTriangle_last_mem_g9 l i)).elim
    | cast w =>
      have hne₁ : w ≠ l.get i := by
        intro he
        apply hw
        simp [boundaryConeTriangle, he]
      have hne₂ : w ≠ l.get (finRotate l.length i) := by
        intro he
        apply hw
        simp [boundaryConeTriangle, he]
      rw [h.1] at hne₁
      rw [h.2] at hne₂
      simp only [boundaryConeRadial, Fin.snoc_castSucc]
      first | rw [hzero w hne₁ hne₂, mul_zero] | rw [hzero w hne₂ hne₁, mul_zero]

/-- The radial map is jointly continuous in the base coordinates and height. -/
theorem boundaryConeRadial_continuous_g9 {N : ℕ} :
    Continuous (fun p : (Fin N → ℝ) × ℝ ↦ boundaryConeRadial p.1 p.2) := by
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last => simpa [boundaryConeRadial] using
      (continuous_snd : Continuous (fun p : (Fin N → ℝ) × ℝ ↦ p.2))
  | cast i =>
    simp only [boundaryConeRadial, Fin.snoc_castSucc]
    exact (continuous_const.sub (continuous_snd : Continuous (fun p : (Fin N → ℝ) × ℝ ↦ p.2))).mul
      ((continuous_apply i).comp continuous_fst)

/-- Equality of radial points means equal heights and equal base points, except
at height one, where the entire boundary collapses to the apex. These are exactly
the equivalence classes of a cone on the original boundary cycle. -/
theorem boundaryConeRadial_eq_iff_g9 {N : ℕ} (x y : Fin N → ℝ) (t s : ℝ) :
    boundaryConeRadial x t = boundaryConeRadial y s ↔ t = s ∧ (t = 1 ∨ x = y) := by
  constructor
  · intro h
    have hts := congrFun h (Fin.last N)
    simp only [boundaryConeRadial, Fin.snoc_last] at hts
    refine ⟨hts, ?_⟩
    by_cases ht : t = 1
    · exact Or.inl ht
    · right
      subst s
      funext i
      have hi := congrFun h i.castSucc
      simp only [boundaryConeRadial, Fin.snoc_castSucc] at hi
      exact mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm ht)) hi
  · rintro ⟨rfl, ht | rfl⟩
    · simp [boundaryConeRadial, ht]
    · rfl

@[simp] lemma boundaryConeRadial_zero_g9 {N : ℕ} (x : Fin N → ℝ) :
    boundaryConeRadial x 0 = Fin.snoc (α := fun _ ↦ ℝ) x 0 := by
  simp [boundaryConeRadial]

@[simp] lemma boundaryConeRadial_apex_coordinate_g9 {N : ℕ} (x : Fin N → ℝ) (t : ℝ) :
    boundaryConeRadial x t (Fin.last N) = t := by
  simp [boundaryConeRadial]

/-- The continuous cone map from the actual boundary cycle times the unit interval
into the attached complex. At height zero it is the original boundary inclusion;
at height one all base points collapse to the fresh apex. -/
def boundaryConeRadialMap {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (l : List (Fin N)) :
    C(↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1, ↥(carrier (attachBoundaryCone K l))) where
  toFun p := ⟨boundaryConeRadial p.1.val.val p.2.val,
    boundaryConeRadial_mem_carrier_g9 K l p.1.val p.1.property p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact boundaryConeRadial_continuous_g9.comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd))

/-- The continuous cone map has precisely the apex-collapse fibers, including
points on the original boundary at height zero. -/
theorem boundaryConeRadialMap_eq_iff_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (p q : ↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1) :
    boundaryConeRadialMap K l p = boundaryConeRadialMap K l q ↔
      p.2 = q.2 ∧ ((p.2 : ℝ) = 1 ∨ p.1 = q.1) := by
  change (⟨boundaryConeRadial p.1.val.val p.2.val, _⟩ :
      ↥(carrier (attachBoundaryCone K l))) = ⟨boundaryConeRadial q.1.val.val q.2.val, _⟩ ↔ _
  simp only [boundaryConeRadial_eq_iff_g9, Subtype.ext_iff]

/-- At radial height zero the cap map is the literal coordinate inclusion of
the prescribed boundary, so there is no change of boundary parametrization. -/
theorem boundaryConeRadialMap_boundary_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (x : ↥(cycleCarrier (K := K) l)) :
    (boundaryConeRadialMap K l (x, ⟨0, by simp⟩)).val =
      Fin.snoc (α := fun _ ↦ ℝ) x.val.val 0 := by
  exact boundaryConeRadial_zero_g9 _

end HolomorphicAnosov.Topology.GallierXu

