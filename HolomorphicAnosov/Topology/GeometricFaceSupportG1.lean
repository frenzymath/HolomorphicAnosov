import HolomorphicAnosov.Topology.GeometricFaceBarycentricHomeomorph

/-! Barycentric support, proper-face boundaries, and disjoint intrinsic face interiors. -/

namespace HolomorphicAnosov
open Set Topology _root_.Topology
noncomputable section

/-- Barycentric coordinates of a point of a face, with the strict-interior criterion. (Hatcher) -/
theorem geometric_face_positive_weights (N : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s : Finset (EuclideanSpace ℝ (Fin N))) (hs : s ∈ P.faces)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ convexHull ℝ (s : Set _)) :
    ∃ w : EuclideanSpace ℝ (Fin N) → ℝ,
      (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y = 1) ∧
      (∑ y ∈ s, w y • y = x) ∧
      (x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set _)) ↔ ∀ y ∈ s, 0 < w y) := by
  classical
  let d := s.card - 1
  have hc : s.card = d + 1 := by
    have := Finset.card_pos.mpr (P.nonempty_of_mem_faces hs)
    dsimp [d]; omega
  let o : Fin (d + 1) ≃ s :=
    (Fintype.equivFinOfCardEq (show Fintype.card s = d + 1 by simpa using hc)).symm
  obtain ⟨β, hβ⟩ := geometric_face_std_barycentric_homeomorph N d P s hs hc
  have hi := geometric_face_stdSimplex_intrinsicInterior_bridge N d P s hs hc β hβ
  let a := β.symm ⟨x, hx⟩
  let w : EuclideanSpace ℝ (Fin N) → ℝ := fun y ↦
    if hy : y ∈ s then a.weights (o.symm ⟨y, hy⟩) else 0
  have hw (i : Fin (d+1)) : w (o i).val = a.weights i := by simp [w]
  have hsum : ∑ y ∈ s, w y = ∑ i, a.weights i := by
    rw [← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv o _ _ (fun i ↦ (hw i).symm)).symm
  have hvec : ∑ y ∈ s, w y • y = ∑ i, a.weights i • (o i).val := by
    rw [← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv o _ _ (fun i ↦ by rw [hw])).symm
  refine ⟨w, ?_, hsum.trans a.total_of_fintype, ?_, ?_⟩
  · intro y hy; simp only [w, dite_eq_left hy]; exact a.weights_nonneg _
  · rw [hvec]
    have ha := hβ a
    rw [Finset.affineCombination_eq_linear_combination _ _ _ a.total_of_fintype] at ha
    exact ha.symm.trans (congrArg Subtype.val (β.apply_symm_apply ⟨x, hx⟩))
  · have hxpos : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set _)) ↔
        ∀ i, 0 < a.weights i := by
      change (⟨x, hx⟩ : {z // z ∈ convexHull ℝ (s : Set _)}) ∈
        {z | z.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set _))} ↔ _
      rw [← hi]
      constructor
      · rintro ⟨b, hb, he⟩
        have : b = a := β.injective (he.trans (β.apply_symm_apply _).symm)
        simpa [this] using hb
      · intro ha; exact ⟨a, ha, β.apply_symm_apply _⟩
    rw [hxpos]
    constructor
    · intro ha y hy; simp only [w, dite_eq_left hy]; exact ha _
    · intro hw' i; simpa [hw] using hw' (o i).val (o i).property

/-- A subface is characterized by vanishing of the barycentric weights outside it. (Hatcher) -/
theorem geometric_face_subface_weights {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s t : Finset E) (hind : AffineIndependent ℝ ((↑) : s → E)) (ht : t ⊆ s)
    (w : E → ℝ) (hw : ∀ y ∈ s, 0 ≤ w y) (hsum : ∑ y ∈ s, w y = 1)
    (x : E) (hvec : ∑ y ∈ s, w y • y = x) :
    x ∈ convexHull ℝ (t : Set E) ↔ ∀ y ∈ s, y ∉ t → w y = 0 := by
  classical
  constructor
  · intro hx
    obtain ⟨v, hv, hvs, hvx⟩ := Finset.mem_convexHull'.mp hx
    let v' : E → ℝ := fun y ↦ if y ∈ t then v y else 0
    have hvs' : ∑ y ∈ s, v' y = 1 := by
      calc
        _ = ∑ y ∈ t, v' y := (Finset.sum_subset ht (by intro y _ hy; simp [v', hy])).symm
        _ = ∑ y ∈ t, v y := Finset.sum_congr rfl (by intro y hy; simp [v', hy])
        _ = 1 := hvs
    have hvx' : ∑ y ∈ s, v' y • y = x := by
      calc
        _ = ∑ y ∈ t, v' y • y :=
          (Finset.sum_subset ht (by intro y _ hy; simp [v', hy])).symm
        _ = ∑ y ∈ t, v y • y := Finset.sum_congr rfl (by intro y hy; simp [v', hy])
        _ = x := hvx
    have heq := hind.eq_of_sum_eq_sum_subtype (hsum.trans hvs'.symm) (hvec.trans hvx'.symm)
    intro y hy hyt
    simpa [v', hyt] using heq y hy
  · intro hz
    apply Finset.mem_convexHull'.mpr
    refine ⟨w, fun y hy ↦ hw y (ht hy), ?_, ?_⟩
    · exact (Finset.sum_subset ht (by intro y hy hyt; exact hz y hy hyt)).trans hsum
    · exact (Finset.sum_subset ht (by intro y hy hyt; simp [hz y hy hyt])).trans hvec

/-- The complement of the intrinsic interior in a face is its proper nonempty subfaces. (Hatcher) -/
theorem geometric_face_boundary_iff (N : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s : Finset (EuclideanSpace ℝ (Fin N))) (hs : s ∈ P.faces)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ convexHull ℝ (s : Set _)) :
    x ∉ intrinsicInterior ℝ (convexHull ℝ (s : Set _)) ↔
      ∃ t : Finset _, t.Nonempty ∧ t ⊂ s ∧ x ∈ convexHull ℝ (t : Set _) := by
  classical
  obtain ⟨w, hw, hsum, hvec, hi⟩ := geometric_face_positive_weights N P s hs x hx
  rw [hi]
  constructor
  · intro hn
    let t := s.filter (fun y ↦ 0 < w y)
    have hts : t ⊆ s := Finset.filter_subset _ _
    have ht : t.Nonempty := by
      by_contra he
      have hz : ∀ y ∈ s, w y = 0 := by
        intro y hy
        have : ¬ 0 < w y := by
          intro hp; exact he ⟨y, Finset.mem_filter.mpr ⟨hy, hp⟩⟩
        exact le_antisymm (le_of_not_gt this) (hw y hy)
      have : ∑ y ∈ s, w y = 0 := Finset.sum_eq_zero hz
      linarith
    have hproper : t ⊂ s := by
      refine ⟨hts, ?_⟩
      intro hst
      apply hn
      intro y hy
      exact (Finset.mem_filter.mp (hst hy)).2
    refine ⟨t, ht, hproper, (geometric_face_subface_weights s t (P.indep hs) hts
      w hw hsum x hvec).mpr ?_⟩
    intro y hy hyt
    have : ¬ 0 < w y := fun hp ↦ hyt (Finset.mem_filter.mpr ⟨hy, hp⟩)
    exact le_antisymm (le_of_not_gt this) (hw y hy)
  · rintro ⟨t, ht, hts, hxt⟩ hpos
    obtain ⟨y, hys, hyt⟩ := Finset.exists_of_ssubset hts
    have hz := (geometric_face_subface_weights s t (P.indep hs) hts.le
      w hw hsum x hvec).mp hxt y hys hyt
    linarith [hpos y hys]

/-- Distinct faces have disjoint intrinsic interiors. (Hatcher) -/
theorem geometric_face_interiors_disjoint (N : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s t : Finset (EuclideanSpace ℝ (Fin N))) (hs : s ∈ P.faces) (ht : t ∈ P.faces)
    (hne : s ≠ t) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))))
      (intrinsicInterior ℝ (convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin N))))) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  have hx : x ∈ convexHull ℝ ((s ∩ t : Finset _) : Set _) := by
    simpa using P.inter_subset_convexHull hs ht
      ⟨intrinsicInterior_subset hxs, intrinsicInterior_subset hxt⟩
  have hsub (a b : Finset _) (ha : a ∈ P.faces)
      (hia : x ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set _)))
      (hba : b ⊆ a) (hb : x ∈ convexHull ℝ (b : Set _)) : a ⊆ b := by
    obtain ⟨w, hw, hsum, hvec, hi⟩ :=
      geometric_face_positive_weights N P a ha x (intrinsicInterior_subset hia)
    intro y hy
    by_contra hyb
    have hz := (geometric_face_subface_weights a b (P.indep ha) hba
      w hw hsum x hvec).mp hb y hy hyb
    linarith [(hi.mp hia) y hy]
  exact hne (Finset.Subset.antisymm
    ((hsub s (s ∩ t) hs hxs Finset.inter_subset_left hx).trans Finset.inter_subset_right)
    ((hsub t (s ∩ t) ht hxt Finset.inter_subset_right hx).trans Finset.inter_subset_left))

end
end HolomorphicAnosov
