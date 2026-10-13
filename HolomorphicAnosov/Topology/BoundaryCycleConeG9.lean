import HolomorphicAnosov.Topology.BoundaryCycleEdgeCountG9

/-!
# A simplicial cone attached along a boundary cycle

The finite cone construction used in the capping argument for Gallier--Xu
Theorems 5.1--5.2, pp.72--74. The new vertex is `Fin.last N`; all original
vertices are retained by `Fin.castSucc`. This construction supplies actual
faces, independently of the later topological disk/sphere comparison.
-/

open scoped Classical
namespace HolomorphicAnosov.Topology.GallierXu

/-- The triangle over an original boundary edge, with one fresh cone vertex. -/
def boundaryConeTriangle {N : ℕ} (l : List (Fin N)) (i : Fin l.length) :
    Finset (Fin (N + 1)) :=
  insert (Fin.last N)
    (({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)).image Fin.castSucc)

/-- Attach all triangular cones over the prescribed cyclic edge list.
Downward closure includes the cone spokes and apex. Adding singletons retains
all original vertices even when the list is empty. No proof data is admitted. -/
def attachBoundaryCone {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (l : List (Fin N)) : AbstractSimplicialComplex (Fin (N + 1)) :=
  ((K.toPreAbstractSimplicialComplex.map Fin.castSucc) ⊔
    { faces := {s | s.Nonempty ∧ ∃ i : Fin l.length, s ⊆ boundaryConeTriangle l i}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        intro t hts ht
        obtain ⟨i, hi⟩ := hs.2
        exact ⟨ht, i, hts.trans hi⟩ }).addSingletons

lemma fin_last_not_mem_image_castSucc_g9 {N : ℕ} (s : Finset (Fin N)) :
    Fin.last N ∉ s.image Fin.castSucc := by
  rintro h
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
  have hval := congrArg Fin.val hv
  simp only [Fin.val_castSucc, Fin.val_last] at hval
  omega

lemma boundaryConeTriangle_last_mem_g9 {N : ℕ} (l : List (Fin N)) (i : Fin l.length) :
    Fin.last N ∈ boundaryConeTriangle l i := by
  simp [boundaryConeTriangle]

lemma boundaryConeTriangle_injective_g9 {N : ℕ} (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 3 ≤ l.length) :
    Function.Injective (boundaryConeTriangle l) := by
  intro i j hij
  apply cycle_edge_pair_injective_g9 l hnd hlen
  apply Finset.image_injective (Fin.castSucc_injective N)
  have h := congrArg (fun s : Finset (Fin (N + 1)) => s.erase (Fin.last N)) hij
  simp only [boundaryConeTriangle] at h
  simpa only [Finset.erase_insert_eq_erase, Finset.erase_eq_of_notMem (fin_last_not_mem_image_castSucc_g9 _)] using h

lemma boundaryConeTriangle_card_g9 {N : ℕ} (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 3 ≤ l.length) (i : Fin l.length) :
    (boundaryConeTriangle l i).card = 3 := by
  have hne : l.get i ≠ l.get (finRotate l.length i) := by
    intro h
    have hi := hnd.injective_get h
    exact finRotate_twice_ne_g9 hlen i (hi.trans (congrArg _ hi))
  rw [boundaryConeTriangle, Finset.card_insert_of_notMem (fin_last_not_mem_image_castSucc_g9 _),
    Finset.card_image_of_injective _ (Fin.castSucc_injective N), Finset.card_pair hne]

lemma boundaryConeTriangle_face_g9 {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (l : List (Fin N)) (i : Fin l.length) :
    boundaryConeTriangle l i ∈ (attachBoundaryCone K l).faces := by
  exact Or.inl (Or.inr ⟨⟨Fin.last N, boundaryConeTriangle_last_mem_g9 l i⟩, i, le_rfl⟩)

/-- Exactly one new triangle is attached for each edge of a simple cycle.
The fresh apex distinguishes new triangles from every original triangle.
This is the triangle-count part of the cone capping calculation in the
Gallier--Xu Euler argument (Theorems 5.1--5.2, pp.72--74). -/
theorem attachBoundaryCone_triangle_count_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 3 ≤ l.length) :
    (simplices (attachBoundaryCone K l) 2).card = (simplices K 2).card + l.length := by
  classical
  have hset : simplices (attachBoundaryCone K l) 2 =
      (simplices K 2).image (Finset.image Fin.castSucc) ∪
      Finset.univ.image (boundaryConeTriangle l) := by
    ext s
    simp only [simplices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · rintro ⟨hs, hcard⟩
      change ((_ ∨ _) ∨ _) at hs
      rcases hs with (hold | hcone) | hsingle
      · obtain ⟨t, ht, rfl⟩ := hold
        exact Or.inl ⟨t, ⟨ht, by simpa only [Finset.card_image_of_injective _ (Fin.castSucc_injective N)] using hcard⟩, rfl⟩
      · obtain ⟨_, i, hsub⟩ := hcone
        have heq : s = boundaryConeTriangle l i :=
          Finset.eq_of_subset_of_card_le hsub (by rw [boundaryConeTriangle_card_g9 l hnd hlen]; omega)
        exact Or.inr ⟨i, heq.symm⟩
      · obtain ⟨v, rfl⟩ := hsingle
        simp at hcard
    · rintro (⟨t, ⟨ht, hcard⟩, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨Or.inl (Or.inl ⟨t, ht, rfl⟩), ?_⟩
        simpa only [Finset.card_image_of_injective _ (Fin.castSucc_injective N)] using hcard
      · exact ⟨boundaryConeTriangle_face_g9 K l i, boundaryConeTriangle_card_g9 l hnd hlen i⟩
  have hd : Disjoint ((simplices K 2).image (Finset.image Fin.castSucc))
      (Finset.univ.image (boundaryConeTriangle l)) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
    have hm := boundaryConeTriangle_last_mem_g9 l i
    rw [hi] at hm
    exact fin_last_not_mem_image_castSucc_g9 t hm
  rw [hset, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (Finset.image_injective (Fin.castSucc_injective N)),
    Finset.card_image_of_injective _ (boundaryConeTriangle_injective_g9 l hnd hlen)]
  simp

/-- A cone spoke joins an original vertex to the fresh apex. -/
def boundaryConeSpoke {N : ℕ} (v : Fin N) : Finset (Fin (N + 1)) :=
  {Fin.last N, v.castSucc}

lemma boundaryConeSpoke_injective_g9 {N : ℕ} :
    Function.Injective (@boundaryConeSpoke N) := by
  intro u v huv
  have h := congrArg (fun s : Finset (Fin (N + 1)) => s.erase (Fin.last N)) huv
  have hu := fin_last_not_mem_image_castSucc_g9 ({u} : Finset (Fin N))
  have hv := fin_last_not_mem_image_castSucc_g9 ({v} : Finset (Fin N))
  simp only [Finset.image_singleton] at hu hv
  simpa only [boundaryConeSpoke, Finset.erase_insert_eq_erase,
    Finset.erase_eq_of_notMem hu, Finset.erase_eq_of_notMem hv,
    Finset.singleton_inj, Fin.castSucc_inj] using h

/-- If the cycle edges already belong to K, the new edges are precisely its
spokes. Thus a simple length-n boundary contributes n new edges. -/
theorem attachBoundaryCone_edge_count_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (hnd : l.Nodup)
    (hcycle : ∀ i : Fin l.length,
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces) :
    (simplices (attachBoundaryCone K l) 1).card = (simplices K 1).card + l.length := by
  classical
  have hset : simplices (attachBoundaryCone K l) 1 =
      (simplices K 1).image (Finset.image Fin.castSucc) ∪
      l.toFinset.image boundaryConeSpoke := by
    ext s
    simp only [simplices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨hs, hcard⟩
      change ((_ ∨ _) ∨ _) at hs
      rcases hs with (hold | hcone) | hsingle
      · obtain ⟨t, ht, rfl⟩ := hold
        exact Or.inl ⟨t, ⟨ht, by
          simpa only [Finset.card_image_of_injective _ (Fin.castSucc_injective N)] using hcard⟩, rfl⟩
      · obtain ⟨_, i, hsub⟩ := hcone
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
        have ha := hsub (by simp : a ∈ ({a, b} : Finset (Fin (N + 1))))
        have hb := hsub (by simp : b ∈ ({a, b} : Finset (Fin (N + 1))))
        simp only [boundaryConeTriangle, Finset.mem_insert, Finset.mem_image] at ha hb
        rcases ha with rfl | ⟨u, hu, rfl⟩
        · rcases hb with rfl | ⟨v, hv, rfl⟩
          · exact (hab rfl).elim
          · refine Or.inr ⟨v, ?_, rfl⟩
            simp only [Finset.mem_singleton] at hv
            rcases hv with rfl | rfl <;> exact List.get_mem ..
        · rcases hb with rfl | ⟨v, hv, rfl⟩
          · refine Or.inr ⟨u, ?_, ?_⟩
            · simp only [Finset.mem_singleton] at hu
              rcases hu with rfl | rfl <;> exact List.get_mem ..
            · simp [boundaryConeSpoke, Finset.pair_comm]
          · refine Or.inl ⟨{u, v}, ⟨?_, ?_⟩, by simp⟩
            · exact (K.isRelLowerSet_faces (hcycle i)).2
                (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_insert] using And.intro hu hv)
                (by simp)
            · exact Finset.card_pair (fun huv => hab (congrArg Fin.castSucc huv))
      · obtain ⟨v, rfl⟩ := hsingle
        simp at hcard
    · rintro (⟨t, ⟨ht, hcard⟩, rfl⟩ | ⟨v, hv, rfl⟩)
      · refine ⟨Or.inl (Or.inl ⟨t, ht, rfl⟩), ?_⟩
        simpa only [Finset.card_image_of_injective _ (Fin.castSucc_injective N)] using hcard
      · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hv
        refine ⟨Or.inl (Or.inr ⟨by simp [boundaryConeSpoke], i, ?_⟩), ?_⟩
        · simp [boundaryConeSpoke, boundaryConeTriangle, Finset.insert_subset_iff]
        · have hn := fin_last_not_mem_image_castSucc_g9 ({l.get i} : Finset (Fin N))
          simp only [Finset.image_singleton, Finset.mem_singleton] at hn
          exact Finset.card_pair hn
  have hd : Disjoint ((simplices K 1).image (Finset.image Fin.castSucc))
      (l.toFinset.image boundaryConeSpoke) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ht
    have hm : Fin.last N ∈ boundaryConeSpoke v := by simp [boundaryConeSpoke]
    rw [hv] at hm
    exact fin_last_not_mem_image_castSucc_g9 t hm
  rw [hset, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (Finset.image_injective (Fin.castSucc_injective N)),
    Finset.card_image_of_injective _ boundaryConeSpoke_injective_g9,
    List.toFinset_card_of_nodup hnd]

lemma simplices_zero_card_g9 {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) :
    (simplices K 0).card = N := by
  classical
  have hs : simplices K 0 = Finset.univ.image (fun v : Fin N => ({v} : Finset (Fin N))) := by
    ext s
    simp only [simplices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨_, hcard⟩
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨K.singleton_mem v, Finset.card_singleton v⟩
  rw [hs, Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_injective h)]
  simp

/-- Coning an existing simple boundary cycle increases the finite Euler count
by one: it adds one vertex, length(l) edges and length(l) triangles. This is
exactly the combinatorial capping step in the Gallier--Xu Euler comparison. -/
theorem attachBoundaryCone_euler_count_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 3 ≤ l.length)
    (hcycle : ∀ i : Fin l.length,
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces) :
    ((simplices (attachBoundaryCone K l) 0).card : ℤ) -
        ((simplices (attachBoundaryCone K l) 1).card : ℤ) +
        ((simplices (attachBoundaryCone K l) 2).card : ℤ) =
      ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
        ((simplices K 2).card : ℤ) + 1 := by
  rw [simplices_zero_card_g9, simplices_zero_card_g9,
    attachBoundaryCone_edge_count_g9 K l hnd hcycle,
    attachBoundaryCone_triangle_count_g9 K l hnd hlen]
  push_cast
  omega

/-- The two original boundary cycles capped by distinct fresh vertices. -/
def capTwoBoundaryCycles {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N)) : AbstractSimplicialComplex (Fin (N + 1 + 1)) :=
  attachBoundaryCone (attachBoundaryCone K (B 0)) ((B 1).map Fin.castSucc)

/-- The two literal cone caps add two to the Euler count of K. The statement
uses only the prescribed boundary cycles, not a topological classification. -/
theorem capTwoBoundaryCycles_euler_count_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin 2 → List (Fin N))
    (hB : BoundaryCycles K B) :
    ((simplices (capTwoBoundaryCycles K B) 0).card : ℤ) -
        ((simplices (capTwoBoundaryCycles K B) 1).card : ℤ) +
        ((simplices (capTwoBoundaryCycles K B) 2).card : ℤ) =
      ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
        ((simplices K 2).card : ℤ) + 2 := by
  have hcycle (j : Fin 2) (i : Fin (B j).length) :
      ({(B j).get i, (B j).get (finRotate (B j).length i)} : Finset (Fin N)) ∈ K.faces := by
    exact ((hB.2.2 _ _).mpr ⟨j, i, Or.inl ⟨rfl, rfl⟩⟩).2.1
  have hcycle' (i : Fin ((B 1).map Fin.castSucc).length) :
      ({((B 1).map Fin.castSucc).get i,
        ((B 1).map Fin.castSucc).get (finRotate ((B 1).map Fin.castSucc).length i)} :
        Finset (Fin (N + 1))) ∈ (attachBoundaryCone K (B 0)).faces := by
    let j : Fin (B 1).length := ⟨i.val, by simpa using i.isLt⟩
    have hc : (({(B 1).get j, (B 1).get (finRotate (B 1).length j)} :
        Finset (Fin N)).image Fin.castSucc) ∈ (attachBoundaryCone K (B 0)).faces :=
      Or.inl (Or.inl ⟨_, hcycle 1 j, rfl⟩)
    simpa [j, finRotate_apply, Fin.val_add] using hc
  have hfirst := attachBoundaryCone_euler_count_g9 K (B 0)
    (hB.1 0).1 (hB.1 0).2 (hcycle 0)
  have hsecond := attachBoundaryCone_euler_count_g9 (attachBoundaryCone K (B 0))
    ((B 1).map Fin.castSucc) ((hB.1 1).1.map (Fin.castSucc_injective N))
    (by simpa using (hB.1 1).2) hcycle'
  change _ = _ at hfirst
  change ((simplices (capTwoBoundaryCycles K B) 0).card : ℤ) -
    ((simplices (capTwoBoundaryCycles K B) 1).card : ℤ) +
    ((simplices (capTwoBoundaryCycles K B) 2).card : ℤ) = _ at hsecond
  omega

end HolomorphicAnosov.Topology.GallierXu


