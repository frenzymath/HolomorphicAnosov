import HolomorphicAnosov.Geometry.LyubichReflectionWordTransportG11
import HolomorphicAnosov.Geometry.LyubichReflectionBoundaryG11
import HolomorphicAnosov.Geometry.LyubichReflectionChartCoveringG11
import HolomorphicAnosov.Geometry.IdealTriangleSideBoundaryG6

noncomputable section

/-! Physical side pairs, compatible reflected charts, and slit-plane covering families for the reflection tiling. (Lyubich, §2.4.13.) -/

namespace HolomorphicAnosov
open Set IdealDiskTriangle
open scoped ComplexConjugate

/-- A reflection word carries a complete geodesic to the complete geodesic with the transported ideal endpoints. -/
theorem MarkedIdealDiskTriangle.itineraryMap_openSide_image
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    T.itineraryMap w '' IdealDiskTriangle.openSide a b =
      IdealDiskTriangle.openSide (T.itineraryMap w a) (T.itineraryMap w b) := by
  induction w with
  | nil => simp [itineraryMap]
  | cons i w ih =>
    rw [T.itineraryMap_cons, Set.image_comp, ih,
      reflection_openSide_image (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i)
        (itineraryMap_unitCircle w ha) (itineraryMap_unitCircle w hb)
        (fun h ↦ hab (itineraryMap_injOn_closedDisk w ha.le hb.le h))]
    rfl

/-- The literal interior of a word triangle. -/
def MarkedIdealDiskTriangle.wordTile (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) : Set ℂ := T.itineraryMap w '' T.interiorSet

/-- The literal transported side of color i in a word triangle. -/
def MarkedIdealDiskTriangle.wordSide (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) (i : Fin 3) : Set ℂ := T.itineraryMap w '' T.openSide i (i + 1)

/-- The marked word interior agrees with the physical tiling interior. -/
theorem MarkedIdealDiskTriangle.wordTile_native (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) : T.wordTile w = openTriangle (T.wordTriangle w).val.val := by
  change T.itineraryMap w '' T.interiorSet = _
  rw [← T.native_openTriangle_eq]
  exact T.itinerary_native_openTriangle w

/-- The marked word side agrees with the complete physical geodesic. -/
theorem MarkedIdealDiskTriangle.wordSide_native (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) (i : Fin 3) :
    T.wordSide w i = IdealDiskTriangle.openSide
      (T.itineraryMap w (T.vertex i)) (T.itineraryMap w (T.vertex (i + 1))) := by
  unfold wordSide
  rw [T.openSide_eq_native i (i + 1) (fun h ↦ T.vertex_ne_next i (congrArg T.vertex h))]
  exact T.itineraryMap_openSide_image w (T.norm_vertex i) (T.norm_vertex (i + 1))
    (T.vertex_ne_next i)

/-- Every transported side is a side of its physical word triangle. -/
theorem MarkedIdealDiskTriangle.wordSide_hasSide (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) (i : Fin 3) :
    hasSide (T.wordTriangle w).val.val (T.wordSide w i) :=
  ⟨_,T.wordTriangle_mem w i,_,T.wordTriangle_mem w (i + 1),
    T.wordTriangle_side_ne w i,T.wordSide_native w i⟩

/-- The same side belongs to the neighboring word triangle. -/
theorem MarkedIdealDiskTriangle.wordSide_neighbor_hasSide (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) (i : Fin 3) :
    hasSide (T.wordTriangle (w ++ [i])).val.val (T.wordSide w i) :=
  ⟨_,(T.wordTriangle_append_side_mem w i).1,_,(T.wordTriangle_append_side_mem w i).2,
    T.wordTriangle_side_ne w i,T.wordSide_native w i⟩

/-- Every physical triangle is represented by a literal generator word. -/
theorem MarkedIdealDiskTriangle.exists_wordTriangle
    (T : MarkedIdealDiskTriangle) (A : ReachedTriangle T.vertexTriple) :
    ∃ w : List (Fin 3), A = T.wordTriangle w := by
  obtain ⟨w,hw⟩ := T.reachable_vertices_eq_itinerary A.property
  exact ⟨w,Subtype.ext (Subtype.ext hw)⟩

/-- Different physical word triangles have disjoint interiors. -/
theorem MarkedIdealDiskTriangle.wordTile_disjoint
    (T : MarkedIdealDiskTriangle) (u v : List (Fin 3))
    (hne : T.wordTriangle u ≠ T.wordTriangle v) : Disjoint (T.wordTile u) (T.wordTile v) := by
  obtain ⟨_,_,_,hdisj,_⟩ := reflection_tiling T.vertexTriple
  rw [T.wordTile_native, T.wordTile_native]
  exact hdisj _ _ hne

/-- A reached side never meets any physical tile interior. -/
theorem MarkedIdealDiskTriangle.wordSide_disjoint_wordTile
    (T : MarkedIdealDiskTriangle) (u v : List (Fin 3)) (i : Fin 3) :
    Disjoint (T.wordSide u i) (T.wordTile v) := by
  apply Set.disjoint_left.mpr
  intro z hzS hzI
  have hzd : ‖z‖ < 1 := by
    obtain ⟨x,hx,rfl⟩ := hzI
    exact lyubich_itinerary_map_disk_preserving T v hx.1
  obtain ⟨_,_,_,_,hpoint,_⟩ := reflection_tiling T.vertexTriple
  rcases hpoint ⟨z,hzd⟩ with h | h
  · exact h.2 ⟨⟨T.wordSide u i,T.wordTriangle u,T.wordSide_hasSide u i⟩,hzS⟩
  · exact h.2 ⟨T.wordTriangle v,(T.wordTile_native v) ▸ hzI⟩

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set IdealDiskTriangle

/-- Every physical word seam is thin in the plane. -/
theorem MarkedIdealDiskTriangle.wordSide_interior_empty
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    interior (T.wordSide w i) = ∅ := by
  rw [T.wordSide_native]
  apply Set.eq_empty_of_subset_empty
  calc
    interior (IdealDiskTriangle.openSide _ _) ⊆ interior {z | sideEquation
        (T.itineraryMap w (T.vertex i)) (T.itineraryMap w (T.vertex (i + 1))) z = 0} :=
      interior_mono (fun _ hz ↦ hz.2)
    _ = ∅ := interior_sideEquation_zero_eq_empty (itineraryMap_unitCircle w (T.norm_vertex i))

/-- A complete physical word side is nonempty; its first ideal endpoint belongs to its closure. -/
theorem MarkedIdealDiskTriangle.wordSide_nonempty
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    (T.wordSide w i).Nonempty := by
  rw [T.wordSide_native]
  exact Set.Nonempty.of_closure ⟨_,left_mem_closure_openSide
    (itineraryMap_unitCircle w (T.norm_vertex i))
    (itineraryMap_unitCircle w (T.norm_vertex (i + 1))) (T.wordTriangle_side_ne w i)⟩

/-- The three colors are distinct sides of the initial marked triangle. -/
theorem MarkedIdealDiskTriangle.initial_sides_disjoint
    (T : MarkedIdealDiskTriangle) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (T.openSide i (i + 1)) (T.openSide j (j + 1)) := by
  rw [T.openSide_eq_native i (i + 1) (fun h ↦ T.vertex_ne_next i (congrArg T.vertex h)),
    T.openSide_eq_native j (j + 1) (fun h ↦ T.vertex_ne_next j (congrArg T.vertex h))]
  have hd (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      Disjoint (IdealDiskTriangle.openSide (T.vertex a) (T.vertex b))
        (IdealDiskTriangle.openSide (T.vertex a) (T.vertex c)) :=
    openSide_disjoint_of_common_endpoint (T.norm_vertex a) (T.norm_vertex b) (T.norm_vertex c)
      (T.distinct.ne hab) (T.distinct.ne hac) (T.distinct.ne hbc)
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num
  all_goals first
    | rw [IdealDiskTriangle.openSide_comm (T.vertex 0) (T.vertex 1)]
      exact hd _ _ _ (by decide) (by decide) (by decide)
    | rw [IdealDiskTriangle.openSide_comm (T.vertex 1) (T.vertex 2)]
      exact hd _ _ _ (by decide) (by decide) (by decide)
    | rw [IdealDiskTriangle.openSide_comm (T.vertex 2) (T.vertex 0)]
      exact hd _ _ _ (by decide) (by decide) (by decide)

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set IdealDiskTriangle

/-- Every reached physical side has an original color and a word representative. -/
theorem MarkedIdealDiskTriangle.exists_wordSide
    (T : MarkedIdealDiskTriangle) (S : ReachedSide T.vertexTriple) :
    ∃ w : List (Fin 3), ∃ i : Fin 3, S.val = T.wordSide w i := by
  classical
  obtain ⟨A,p,hp,q,hq,hpq,hS⟩ := S.property
  obtain ⟨w,rfl⟩ := T.exists_wordTriangle A
  obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp₀
  obtain ⟨q₀,hq₀,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hq₀
  have hab : a ≠ b := fun h ↦ hpq (by rw [h])
  obtain ⟨i,hi | hi⟩ := fin_three_pair_cyclic a b hab
  · refine ⟨w,i,?_⟩
    rw [hS,hi.1,hi.2,T.wordSide_native]
  · refine ⟨w,i,?_⟩
    rw [hS,hi.1,hi.2,T.wordSide_native,IdealDiskTriangle.openSide_comm]

/-- Exactly the word triangle and its appended-side neighbor are incident to a word side. -/
theorem MarkedIdealDiskTriangle.wordSide_incidence
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    T.wordTriangle w ≠ T.wordTriangle (w ++ [i]) ∧
      ∀ A : ReachedTriangle T.vertexTriple,
        hasSide A.val.val (T.wordSide w i) ↔
          A = T.wordTriangle w ∨ A = T.wordTriangle (w ++ [i]) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hrefl,_⟩ := reflection_tiling T.vertexTriple
  obtain ⟨B,hB,hne,_,_,_,_,_,_,hinc⟩ := hrefl (T.wordTriangle w)
    _ (T.wordTriangle_mem w i) _ (T.wordTriangle_mem w (i + 1)) (T.wordTriangle_side_ne w i)
  have he : B = T.wordTriangle (w ++ [i]) :=
    Subtype.ext (Subtype.ext (hB.trans (T.wordTriangle_append_vertices w i).symm))
  subst B
  exact ⟨hne,fun A ↦ by rw [T.wordSide_native]; exact hinc A⟩

/-- Appending a side generator preserves the represented physical side and its original color. -/
theorem MarkedIdealDiskTriangle.wordSide_append_self
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    T.wordSide (w ++ [i]) i = T.wordSide w i := by
  unfold wordSide
  rw [T.itineraryMap_append,Set.image_comp]
  congr 1
  have hfix : Set.EqOn (T.itineraryMap [i]) id (T.openSide i (i + 1)) := by
    intro z hz
    change idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)) z = z
    exact idealDiskSideReflection_fixed_openSide (T.norm_vertex i) (T.norm_vertex (i + 1))
      (T.vertex_ne_next i) ((T.openSide_eq_native i (i + 1)
        (fun h ↦ T.vertex_ne_next i (congrArg T.vertex h))) ▸ hz)
  simpa only [Set.image_id] using hfix.image_eq

/-- At one word triangle, two different side colors are disjoint. -/
theorem MarkedIdealDiskTriangle.wordSides_disjoint
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (T.wordSide w i) (T.wordSide w j) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have he : x = y := T.itineraryMap_injOn w hx.1 hy.1 (hxz.trans hyz.symm)
  exact Set.disjoint_left.mp (T.initial_sides_disjoint hij) hx (he.symm ▸ hy)

/-- Each physical side has a unique original color. -/
theorem MarkedIdealDiskTriangle.wordSide_color_unique
    (T : MarkedIdealDiskTriangle)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
        IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (u v : List (Fin 3)) (i j : Fin 3) (he : T.wordSide u i = T.wordSide v j) : i = j := by
  have hcase := (T.wordSide_incidence u i).2 (T.wordTriangle v)
  have hvs : hasSide (T.wordTriangle v).val.val (T.wordSide u i) :=
    he.symm ▸ T.wordSide_hasSide v j
  have same (a c : List (Fin 3)) (hc : T.wordTriangle a = T.wordTriangle c)
      (k : Fin 3) : T.wordSide a k = T.wordSide c k := by
    obtain ⟨hm,_⟩ := T.word_transport_unique hreflection a c
      (congrArg (fun X : ReachedTriangle T.vertexTriple ↦ X.val.val) hc)
    exact (hm.mono (fun z hz ↦ hz.1.le)).image_eq
  have equal_colors (a : List (Fin 3)) (hside : T.wordSide a i = T.wordSide a j) : i = j := by
    by_contra hij
    obtain ⟨z,hz⟩ := T.wordSide_nonempty a i
    exact Set.disjoint_left.mp (T.wordSides_disjoint a hij) hz (hside ▸ hz)
  rcases hcase.mp hvs with hv | hv
  · apply equal_colors u
    exact he.trans (same v u hv j)
  · apply equal_colors (u ++ [i])
    exact (T.wordSide_append_self u i).trans (he.trans (same v (u ++ [i]) hv j))

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set IdealDiskTriangle
open scoped ComplexConjugate

/-- The open pair centered on a colored word side. -/
def MarkedIdealDiskTriangle.wordPair (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) (i : Fin 3) : Set ℂ :=
  T.wordTile w ∪ T.wordSide w i ∪ T.wordTile (w ++ [i])

/-- A common interior point identifies the two physical word triangles. -/
theorem MarkedIdealDiskTriangle.wordTriangle_eq_of_tile_meet
    (T : MarkedIdealDiskTriangle) (u v : List (Fin 3)) {z : ℂ}
    (hu : z ∈ T.wordTile u) (hv : z ∈ T.wordTile v) :
    T.wordTriangle u = T.wordTriangle v := by
  by_contra h
  exact Set.disjoint_left.mp (T.wordTile_disjoint u v h) hu hv

/-- Two word charts agree at every common interior point. -/
theorem MarkedIdealDiskTriangle.wordChart_overlap
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
        IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (u v : List (Fin 3)) :
    EqOn (T.itineraryChart F u) (T.itineraryChart F v) (T.wordTile u ∩ T.wordTile v) := by
  intro z hz
  have he := T.wordTriangle_eq_of_tile_meet u v hz.1 hz.2
  obtain ⟨hm,hp⟩ := T.word_transport_unique hreflection u v
    (congrArg (fun X : ReachedTriangle T.vertexTriple ↦ X.val.val) he)
  have hFD : F.source ⊆ {z : ℂ | ‖z‖ < 1} := fun _ hx ↦ (hFs ▸ hx).1
  have hmF : EqOn (T.itineraryMap u) (T.itineraryMap v) F.source := by
    intro x hx
    exact hm (show ‖x‖ ≤ 1 from (hFD hx).le)
  obtain ⟨_,heq⟩ := T.itineraryChart_eqOn_of_transport_eq F hFD u v
    hmF hp
  apply heq
  rw [T.itineraryChart_source F hFD u,hFs]
  exact hz.1

/-- Literal pair charts cover every disk point represented by a physical triangle or side. -/
theorem MarkedIdealDiskTriangle.wordPairs_cover
    (T : MarkedIdealDiskTriangle) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ w : List (Fin 3), ∃ i : Fin 3, z ∈ T.wordPair w i := by
  obtain ⟨_,_,_,_,hpoint,_⟩ := reflection_tiling T.vertexTriple
  rcases hpoint ⟨z,hz⟩ with h | h
  · obtain ⟨A,hA,_⟩ := h.1
    obtain ⟨w,rfl⟩ := T.exists_wordTriangle A
    refine ⟨w,0,Or.inl (Or.inl ?_)⟩
    exact (T.wordTile_native w).symm ▸ hA
  · obtain ⟨S,hS,_⟩ := h.1
    obtain ⟨w,i,he⟩ := T.exists_wordSide S
    exact ⟨w,i,Or.inl (Or.inr (he ▸ hS))⟩

/-- On a common tile interior every pair chart agrees with the literal word chart, independently of which of its two halves contains the point. -/
theorem MarkedIdealDiskTriangle.pairChart_tile_formula
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
        IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (w : List (Fin 3)) (i : Fin 3) (D : OpenPartialHomeomorph ℂ ℂ)
    (hDs : D.source = T.wordPair w i)
    (hD₁ : EqOn D (T.itineraryChart F w) (T.wordTile w))
    (hD₂ : EqOn D (T.itineraryChart F (w ++ [i])) (T.wordTile (w ++ [i])))
    (v : List (Fin 3)) : EqOn D (T.itineraryChart F v) (D.source ∩ T.wordTile v) := by
  intro z hz
  have hp : z ∈ T.wordPair w i := hDs ▸ hz.1
  rcases hp with (hp | hp) | hp
  · exact (hD₁ hp).trans (T.wordChart_overlap F hFs hreflection w v ⟨hp,hz.2⟩)
  · exact (Set.disjoint_left.mp (T.wordSide_disjoint_wordTile w v i) hp hz.2).elim
  · exact (hD₂ hp).trans (T.wordChart_overlap F hFs hreflection (w ++ [i]) v ⟨hp,hz.2⟩)

/-- Compatible actual reflected pair charts glue on the whole disk and retain every literal interior word formula. -/
theorem MarkedIdealDiskTriangle.glue_actual_word_pairs
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
        IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (D : List (Fin 3) → Fin 3 → OpenPartialHomeomorph ℂ ℂ)
    (hDs : ∀ w i, (D w i).source = T.wordPair w i)
    (hDD : ∀ w i, (D w i).source ⊆ {z : ℂ | ‖z‖ < 1})
    (hDh : ∀ w i, DifferentiableOn ℂ (D w i) (D w i).source)
    (hDi : ∀ w i, DifferentiableOn ℂ (D w i).symm (D w i).target)
    (hD₁ : ∀ w i, EqOn (D w i) (T.itineraryChart F w) (T.wordTile w))
    (hD₂ : ∀ w i, EqOn (D w i) (T.itineraryChart F (w ++ [i])) (T.wordTile (w ++ [i]))) :
    ∃ lam : ℂ → ℂ, DifferentiableOn ℂ lam {z : ℂ | ‖z‖ < 1} ∧
      (∀ w i, EqOn (D w i) lam (D w i).source) ∧
      (∀ w, EqOn (T.itineraryChart F w) lam (T.wordTile w)) ∧
      (∀ z, ‖z‖ < 1 → ∃ e : OpenPartialHomeomorph ℂ ℂ,
        z ∈ e.source ∧ e.source ⊆ {z : ℂ | ‖z‖ < 1} ∧ EqOn e lam e.source ∧
        DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target) := by
  let e : List (Fin 3) × Fin 3 → OpenPartialHomeomorph ℂ ℂ := fun a ↦ D a.1 a.2
  have hc : ∀ a b, EqOn (e a) (e b) ((e a).source ∩ (e b).source) := by
    apply charts_compatible_of_tile_interiors e T.wordTile
      (fun w ↦ T.itineraryChart F w) (fun a ↦ T.wordSide a.1 a.2)
    · rintro ⟨w,i⟩ z hz
      have hp : z ∈ T.wordPair w i := hDs w i ▸ hz
      rcases hp with (hp | hp) | hp
      · exact Or.inl (mem_iUnion.mpr ⟨w,hp⟩)
      · exact Or.inr hp
      · exact Or.inl (mem_iUnion.mpr ⟨w ++ [i],hp⟩)
    · rintro ⟨w,i⟩
      exact T.wordSide_interior_empty w i
    · rintro ⟨w,i⟩ v
      exact T.pairChart_tile_formula F hFs hreflection w i (D w i)
        (hDs w i) (hD₁ w i) (hD₂ w i) v
  obtain ⟨lam,hlam,heq,hlocal⟩ := exists_word_glued_reflection_map e
    (fun a ↦ hDD a.1 a.2) (by
      intro z hz
      obtain ⟨w,i,hi⟩ := T.wordPairs_cover hz
      exact ⟨(w,i),(hDs w i).symm ▸ hi⟩) hc
    (fun a ↦ hDh a.1 a.2) (fun a ↦ hDi a.1 a.2)
  refine ⟨lam,hlam,fun w i ↦ heq (w,i),?_,hlocal⟩
  intro w z hz
  have hs : z ∈ (D w 0).source := (hDs w 0).symm ▸ Or.inl (Or.inl hz)
  exact (hD₁ w 0 hz).symm.trans (heq (w,0) hs)

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set IdealDiskTriangle

/-- A physical side pair consists of the side and the interiors of its incident triangles. -/
theorem MarkedIdealDiskTriangle.wordPair_intrinsic (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) (i : Fin 3) :
    T.wordPair w i = T.wordSide w i ∪ {z | ∃ A : ReachedTriangle T.vertexTriple,
      hasSide A.val.val (T.wordSide w i) ∧ z ∈ openTriangle A.val.val} := by
  ext z
  constructor
  · rintro ((hz | hz) | hz)
    · exact Or.inr ⟨T.wordTriangle w,T.wordSide_hasSide w i,(T.wordTile_native w) ▸ hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨T.wordTriangle (w ++ [i]),T.wordSide_neighbor_hasSide w i,
        (T.wordTile_native (w ++ [i])) ▸ hz⟩
  · rintro (hz | ⟨A,hA,hz⟩)
    · exact Or.inl (Or.inr hz)
    · rcases (T.wordSide_incidence w i).2 A |>.mp hA with h | h
      · subst A
        exact Or.inl (Or.inl ((T.wordTile_native w).symm ▸ hz))
      · subst A
        exact Or.inr ((T.wordTile_native (w ++ [i])).symm ▸ hz)

/-- Equal physical sides have equal paired open neighborhoods. -/
theorem MarkedIdealDiskTriangle.wordPair_eq_of_side_eq (T : MarkedIdealDiskTriangle)
    (u v : List (Fin 3)) (i j : Fin 3) (h : T.wordSide u i = T.wordSide v j) :
    T.wordPair u i = T.wordPair v j := by
  rw [T.wordPair_intrinsic,T.wordPair_intrinsic,h]

/-- Two reached side representatives through one disk point are equal. -/
theorem MarkedIdealDiskTriangle.wordSide_eq_of_meet (T : MarkedIdealDiskTriangle)
    (u v : List (Fin 3)) (i j : Fin 3) {z : ℂ}
    (hu : z ∈ T.wordSide u i) (hv : z ∈ T.wordSide v j) :
    T.wordSide u i = T.wordSide v j := by
  have hzd : ‖z‖ < 1 := by
    obtain ⟨x,hx,rfl⟩ := hu
    exact lyubich_itinerary_map_disk_preserving T u hx.1
  let S : ReachedSide T.vertexTriple := ⟨T.wordSide u i,T.wordTriangle u,T.wordSide_hasSide u i⟩
  let R : ReachedSide T.vertexTriple := ⟨T.wordSide v j,T.wordTriangle v,T.wordSide_hasSide v j⟩
  obtain ⟨_,_,_,_,hp,_⟩ := reflection_tiling T.vertexTriple
  rcases hp ⟨z,hzd⟩ with h | h
  · exact (h.2 ⟨S,hu⟩).elim
  · exact congrArg Subtype.val (h.1.unique hu hv : S = R)

/-- A pair containing an interior point is incident to that point's triangle. -/
theorem MarkedIdealDiskTriangle.wordPair_tile_incident (T : MarkedIdealDiskTriangle)
    (u v : List (Fin 3)) (i : Fin 3) {z : ℂ}
    (hu : z ∈ T.wordPair u i) (hv : z ∈ T.wordTile v) :
    hasSide (T.wordTriangle v).val.val (T.wordSide u i) := by
  rcases hu with (hu | hu) | hu
  · have h := T.wordTriangle_eq_of_tile_meet u v hu hv
    exact h ▸ T.wordSide_hasSide u i
  · exact (Set.disjoint_left.mp (T.wordSide_disjoint_wordTile u v i) hu hv).elim
  · have h := T.wordTriangle_eq_of_tile_meet (u ++ [i]) v hu hv
    exact h ▸ T.wordSide_neighbor_hasSide u i

section PhysicalColor
variable (T : MarkedIdealDiskTriangle)
variable (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
  ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
    IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
    idealDiskSideReflection p q = idealDiskSideReflection a b)
include hreflection

/-- The side of a fixed color is intrinsic to a physical triangle. -/
theorem MarkedIdealDiskTriangle.wordSide_eq_of_triangle_eq
    (u v : List (Fin 3)) (i : Fin 3) (h : T.wordTriangle u = T.wordTriangle v) :
    T.wordSide u i = T.wordSide v i := by
  obtain ⟨hm,_⟩ := T.word_transport_unique hreflection u v
    (congrArg (fun A : ReachedTriangle T.vertexTriple ↦ A.val.val) h)
  exact (hm.mono (fun z hz ↦ hz.1.le)).image_eq

/-- Every incident triangle sees a physical side with that side's own color. -/
theorem MarkedIdealDiskTriangle.wordSide_at_incident_color
    (u v : List (Fin 3)) (i : Fin 3)
    (h : hasSide (T.wordTriangle v).val.val (T.wordSide u i)) :
    T.wordSide u i = T.wordSide v i := by
  rcases (T.wordSide_incidence u i).2 (T.wordTriangle v) |>.mp h with h | h
  · exact T.wordSide_eq_of_triangle_eq hreflection u v i h.symm
  · exact (T.wordSide_append_self u i).symm.trans
      (T.wordSide_eq_of_triangle_eq hreflection (u ++ [i]) v i h.symm)

/-- Distinct physical sides of one color have disjoint paired neighborhoods. -/
theorem MarkedIdealDiskTriangle.wordPairs_disjoint
    (u v : List (Fin 3)) (i : Fin 3) (hne : T.wordSide u i ≠ T.wordSide v i) :
    Disjoint (T.wordPair u i) (T.wordPair v i) := by
  apply Set.disjoint_left.mpr
  intro z hu hv
  have common (w : List (Fin 3)) (hw : z ∈ T.wordTile w) : False := by
    exact hne ((T.wordSide_at_incident_color hreflection u w i
      (T.wordPair_tile_incident u w i hu hw)).trans
      (T.wordSide_at_incident_color hreflection v w i
        (T.wordPair_tile_incident v w i hv hw)).symm)
  rcases hu with (hu | hu) | hu
  · exact common u hu
  · rcases hv with (hv | hv) | hv
    · exact common v hv
    · exact hne (T.wordSide_eq_of_meet u v i i hu hv)
    · exact common (v ++ [i]) hv
  · exact common (u ++ [i]) hu
end PhysicalColor

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate

/-- The real seam values associated with one marked side. -/
def MarkedIdealDiskTriangle.seamValues (T : MarkedIdealDiskTriangle)
    (b : ℂ → OnePoint ℂ) (i : Fin 3) : Set ℂ := sphereFiniteValue b '' T.openSide i (i + 1)

/-- The slit plane for a side color consists of both half-planes and that side's real boundary values. -/
def MarkedIdealDiskTriangle.slitTarget (T : MarkedIdealDiskTriangle)
    (b : ℂ → OnePoint ℂ) (i : Fin 3) : Set ℂ :=
  {w | 0 < w.im} ∪ T.seamValues b i ∪ {w | w.im < 0}

/-- Boundary values on each open side are real and avoid the punctures. -/
theorem MarkedIdealDiskTriangle.seamValues_real_unpunctured
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet) (hFt : F.target = {w : ℂ | 0 < w.im})
    (hclosure : closure T.interiorSet = T.closedSet)
    (b : ℂ → OnePoint ℂ) (hbcont : ContinuousOn b T.closedSet)
    (hbinj : InjOn b T.closedSet)
    (hbeq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) T.interiorSet)
    (hb0 : b (T.vertex 0) = ((0 : ℂ) : OnePoint ℂ))
    (hb1 : b (T.vertex 1) = ((1 : ℂ) : OnePoint ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty)
    (i : Fin 3) {w : ℂ} (hw : w ∈ T.seamValues b i) :
    w.im = 0 ∧ w ≠ 0 ∧ w ≠ 1 := by
  obtain ⟨z,hz,rfl⟩ := hw
  obtain ⟨v,hv,hv0,hv1⟩ := T.sphere_extension_disk_value b hbinj hb0 hb1 hb2
    (T.openSide_subset_closedSet i (i + 1) hz) hz.1
  have hfinite : b z ≠ OnePoint.infty := hv ▸ OnePoint.coe_ne_infty v
  have he : sphereFiniteValue b z = v :=
    OnePoint.coe_injective ((sphereFiniteValue_coe b hfinite).trans hv)
  refine ⟨?_,he ▸ hv0,he ▸ hv1⟩
  apply chart_sphere_extension_frontier_real F hFt b
    (by simpa only [hFs,hclosure] using hbcont)
    (by simpa only [hFs] using hbeq)
  · rw [hFs]
    exact T.openSide_subset_frontier hclosure (hFs ▸ F.open_source) i (i + 1) hz
  · exact (sphereFiniteValue_coe b hfinite).symm

/-- Conjugation preserves a slit plane whose joining seam is real. -/
theorem conjugation_iterate_slitTarget (J : Set ℂ)
    (hJ : ∀ w ∈ J, w.im = 0) (n : ℕ) :
    (conj^[n]) '' ({w : ℂ | 0 < w.im} ∪ J ∪ {w : ℂ | w.im < 0}) =
      {w : ℂ | 0 < w.im} ∪ J ∪ {w : ℂ | w.im < 0} := by
  have hconj : conj '' ({w : ℂ | 0 < w.im} ∪ J ∪ {w : ℂ | w.im < 0}) =
      {w : ℂ | 0 < w.im} ∪ J ∪ {w : ℂ | w.im < 0} := by
    have hm : MapsTo conj ({w : ℂ | 0 < w.im} ∪ J ∪ {w : ℂ | w.im < 0})
        ({w : ℂ | 0 < w.im} ∪ J ∪ {w : ℂ | w.im < 0}) := by
      intro w hw
      rcases hw with (hw | hw) | hw
      · exact Or.inr (show -w.im < 0 from neg_neg_of_pos hw)
      · rw [Complex.conj_eq_iff_im.mpr (hJ w hw)]
        exact Or.inl (Or.inr hw)
      · exact Or.inl (Or.inl (show 0 < -w.im from neg_pos.mpr hw))
    exact Set.Subset.antisymm (by rintro _ ⟨w,hw,rfl⟩; exact hm hw)
      (fun w hw ↦ ⟨conj w,hm hw,Complex.conj_conj w⟩)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ,Set.image_comp,hconj,ih]

/-- All literal adjacent word pairs carry biholomorphic charts over the slit plane of their side color, with both interior word formulas and the real seam formula. -/
theorem MarkedIdealDiskTriangle.exists_word_pair_charts
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet) (hFt : F.target = {w : ℂ | 0 < w.im})
    (hFhol : DifferentiableOn ℂ F F.source)
    (hclosure : closure T.interiorSet = T.closedSet)
    (b : ℂ → OnePoint ℂ) (hbcont : ContinuousOn b T.closedSet)
    (hbinj : InjOn b T.closedSet)
    (hbeq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) T.interiorSet)
    (hb0 : b (T.vertex 0) = ((0 : ℂ) : OnePoint ℂ))
    (hb1 : b (T.vertex 1) = ((1 : ℂ) : OnePoint ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty) :
    ∃ D : List (Fin 3) → Fin 3 → OpenPartialHomeomorph ℂ ℂ,
      (∀ w i, (D w i).source = T.wordPair w i) ∧
      (∀ w i, (D w i).source ⊆ {z : ℂ | ‖z‖ < 1}) ∧
      (∀ w i, (D w i).target = T.slitTarget b i) ∧
      (∀ w i, DifferentiableOn ℂ (D w i) (D w i).source) ∧
      (∀ w i, DifferentiableOn ℂ (D w i).symm (D w i).target) ∧
      (∀ w i, EqOn (D w i) (T.itineraryChart F w) (T.wordTile w)) ∧
      (∀ w i, EqOn (D w i) (T.itineraryChart F (w ++ [i])) (T.wordTile (w ++ [i]))) ∧
      ∀ w i z, z ∈ T.openSide i (i + 1) →
        D w i (T.itineraryMap w z) = sphereFiniteValue b z := by
  classical
  have he (i : Fin 3) := T.exists_side_pair_chart F hFs hFt hFhol hclosure
    b hbcont hbinj hbeq hb0 hb1 hb2 i (i + 1) (i + 2)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  choose E hEs hEh hEi hEF hER hEb hEt using he
  let D := fun w i ↦ T.itineraryChart (E i) w
  have hD (w : List (Fin 3)) (i : Fin 3) := T.transported_side_pair_chart F (E i) hFs
    (hEh i) (hEi i) (sphereFiniteValue b) i (hEs i) (hEF i) (hER i) (hEb i) w
  have himage (w : List (Fin 3)) (i : Fin 3) :
      T.itineraryMap w '' (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)) '' T.interiorSet) =
        T.wordTile (w ++ [i]) := by
    rw [wordTile,T.itineraryMap_append,Set.image_comp]
    rfl
  have hreal (i : Fin 3) (z : ℂ) (hz : z ∈ T.seamValues b i) : z.im = 0 :=
    (T.seamValues_real_unpunctured F hFs hFt hclosure b hbcont hbinj hbeq hb0 hb1 hb2 i hz).1
  refine ⟨D,?_,fun w i ↦ (hD w i).2.1,?_,fun w i ↦ (hD w i).2.2.2.1,
    fun w i ↦ (hD w i).2.2.2.2.1,fun w i ↦ (hD w i).2.2.2.2.2.1,?_,?_⟩
  · intro w i
    rw [(hD w i).1,hEs i,Set.image_union,Set.image_union,himage]
    rfl
  · intro w i
    rw [(hD w i).2.2.1,hEt i]
    exact conjugation_iterate_slitTarget (T.seamValues b i) (hreal i) w.length
  · intro w i
    rw [← himage]
    exact (hD w i).2.2.2.2.2.2.1
  · intro w i z hz
    rw [(hD w i).2.2.2.2.2.2.2 z hz]
    exact Function.iterate_fixed (Complex.conj_eq_iff_im.mpr (hreal i _ ⟨z,hz,rfl⟩)) _

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set

/-- Side values of different colors are disjoint, and their slit planes cover exactly the twice-punctured plane. -/
theorem MarkedIdealDiskTriangle.slitTarget_cover
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet) (hFt : F.target = {w : ℂ | 0 < w.im})
    (hclosure : closure T.interiorSet = T.closedSet)
    (b : ℂ → OnePoint ℂ) (hbcont : ContinuousOn b T.closedSet)
    (hbinj : InjOn b T.closedSet)
    (hbeq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) T.interiorSet)
    (hb0 : b (T.vertex 0) = ((0 : ℂ) : OnePoint ℂ))
    (hb1 : b (T.vertex 1) = ((1 : ℂ) : OnePoint ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty)
    (hsurj : ∀ w : ℂ, 0 ≤ w.im → ∃ z ∈ T.closedSet, b z = (w : OnePoint ℂ)) :
    (∀ i j : Fin 3, j ≠ i → Disjoint (T.seamValues b j) (T.slitTarget b i)) ∧
      {w : ℂ | w ≠ 0 ∧ w ≠ 1} = ⋃ i : Fin 3, T.slitTarget b i := by
  have hv (i : Fin 3) {w : ℂ} (hw : w ∈ T.seamValues b i) :=
    T.seamValues_real_unpunctured F hFs hFt hclosure b hbcont hbinj hbeq hb0 hb1 hb2 i hw
  have hginj : InjOn (sphereFiniteValue b) (T.closedSet ∩ {z : ℂ | ‖z‖ < 1}) := by
    apply sphereFiniteValue_injOn b (hbinj.mono inter_subset_left)
    intro z hz
    obtain ⟨v,hv,_,_⟩ := T.sphere_extension_disk_value b hbinj hb0 hb1 hb2 hz.1 hz.2
    exact hv ▸ OnePoint.coe_ne_infty v
  constructor
  · intro i j hji
    apply Set.disjoint_left.mpr
    intro w hw hwV
    have hreal := (hv j hw).1
    rcases hwV with (hpos | hseam) | hneg
    · have : 0 < w.im := hpos
      linarith
    · obtain ⟨x,hx,hxw⟩ := hw
      obtain ⟨y,hy,hyw⟩ := hseam
      have he : x = y := hginj ⟨T.openSide_subset_closedSet j (j + 1) hx,hx.1⟩
        ⟨T.openSide_subset_closedSet i (i + 1) hy,hy.1⟩ (hxw.trans hyw.symm)
      exact Set.disjoint_left.mp (T.initial_sides_disjoint hji) hx (he.symm ▸ hy)
    · have : w.im < 0 := hneg
      linarith
  · ext w
    constructor
    · intro hw
      rcases lt_trichotomy 0 w.im with hpos | hzero | hneg
      · exact mem_iUnion.mpr ⟨0,Or.inl (Or.inl hpos)⟩
      · obtain ⟨z,⟨i,j,hij,hz⟩,hzw,_⟩ := T.real_value_preimage_on_side F hFs hFt
          b hbinj hbeq hb0 hb1 hb2 hsurj hzero.symm hw.1 hw.2
        obtain ⟨k,hk | hk⟩ := fin_three_pair_cyclic i j hij
        · refine mem_iUnion.mpr ⟨k,Or.inl (Or.inr ⟨z,?_,?_⟩)⟩
          · simpa only [hk.1,hk.2] using hz
          · exact OnePoint.coe_injective
              ((sphereFiniteValue_coe b (hzw ▸ OnePoint.coe_ne_infty w)).trans hzw)
        · refine mem_iUnion.mpr ⟨k,Or.inl (Or.inr ⟨z,?_,?_⟩)⟩
          · rw [T.openSide_eq_native i j hij,IdealDiskTriangle.openSide_comm,
              ← T.openSide_eq_native j i hij.symm] at hz
            simpa only [hk.1,hk.2] using hz
          · exact OnePoint.coe_injective
              ((sphereFiniteValue_coe b (hzw ▸ OnePoint.coe_ne_infty w)).trans hzw)
      · exact mem_iUnion.mpr ⟨0,Or.inr hneg⟩
    · intro hw
      obtain ⟨i,(hw | hw) | hw⟩ := mem_iUnion.mp hw
      · constructor <;> intro he <;> subst w <;> norm_num at hw
      · exact (hv i hw).2
      · constructor <;> intro he <;> subst w <;> norm_num at hw

/-- A side color indexed by physical sets, with duplicate word descriptions identified by the subtype equality. -/
def MarkedIdealDiskTriangle.ColoredWordSide (T : MarkedIdealDiskTriangle) (i : Fin 3) :=
  {S : Set ℂ // ∃ w : List (Fin 3), S = T.wordSide w i}

noncomputable def MarkedIdealDiskTriangle.ColoredWordSide.word
    {T : MarkedIdealDiskTriangle} {i : Fin 3} (S : T.ColoredWordSide i) : List (Fin 3) :=
  S.property.choose

theorem MarkedIdealDiskTriangle.ColoredWordSide.word_spec
    {T : MarkedIdealDiskTriangle} {i : Fin 3} (S : T.ColoredWordSide i) :
    S.val = T.wordSide S.word i := S.property.choose_spec

instance (T : MarkedIdealDiskTriangle) (i : Fin 3) : Nonempty (T.ColoredWordSide i) :=
  ⟨⟨T.wordSide [] i,[],rfl⟩⟩

/-- The actual word pair charts give the global covering: for each side color their physical paired neighborhoods are disjoint sheets. -/
theorem MarkedIdealDiskTriangle.covering_of_actual_word_pairs
    (T : MarkedIdealDiskTriangle)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
        IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (b : ℂ → OnePoint ℂ) (lam : ℂ → ℂ)
    (D : List (Fin 3) → Fin 3 → OpenPartialHomeomorph ℂ ℂ)
    (hDs : ∀ w i, (D w i).source = T.wordPair w i)
    (hDD : ∀ w i, (D w i).source ⊆ {z : ℂ | ‖z‖ < 1})
    (hDt : ∀ w i, (D w i).target = T.slitTarget b i)
    (hDeq : ∀ w i, EqOn (D w i) lam (D w i).source)
    (hDseam : ∀ w i z, z ∈ T.openSide i (i + 1) →
      D w i (T.itineraryMap w z) = sphereFiniteValue b z)
    (hsep : ∀ i j : Fin 3, j ≠ i → Disjoint (T.seamValues b j) (T.slitTarget b i))
    (hΩ : {w : ℂ | w ≠ 0 ∧ w ≠ 1} = ⋃ i : Fin 3, T.slitTarget b i) :
    IsCoveringMapOn (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val)
      {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∧
      range (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val) = {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
  classical
  let E := fun i (S : T.ColoredWordSide i) ↦ D S.word i
  have hrepresent (i : Fin 3) (w : List (Fin 3)) :
      ∃ S : T.ColoredWordSide i, (E i S).source = T.wordPair w i := by
    let S : T.ColoredWordSide i := ⟨T.wordSide w i,w,rfl⟩
    refine ⟨S,(hDs S.word i).trans ?_⟩
    exact T.wordPair_eq_of_side_eq S.word w i i S.word_spec.symm
  apply covering_of_colored_chart_sheets lam {z : ℂ | ‖z‖ < 1}
    {w : ℂ | w ≠ 0 ∧ w ≠ 1} (isOpen_lt continuous_norm continuous_const)
    E (T.slitTarget b) (fun i ↦ ⋃ w : List (Fin 3), T.wordSide w i) (T.seamValues b)
    (fun i S ↦ hDD S.word i) (fun i S ↦ hDt S.word i) (fun i S ↦ hDeq S.word i)
  · intro i S R hne
    change Disjoint (D S.word i).source (D R.word i).source
    rw [hDs,hDs]
    apply T.wordPairs_disjoint hreflection
    intro he
    exact hne (Subtype.ext (S.word_spec.trans (he.trans R.word_spec.symm)))
  · intro i z hz hnot
    obtain ⟨_,_,_,_,hp,_⟩ := IdealDiskTriangle.reflection_tiling T.vertexTriple
    rcases hp ⟨z,hz⟩ with hp | hp
    · obtain ⟨A,hA,_⟩ := hp.1
      obtain ⟨w,rfl⟩ := T.exists_wordTriangle A
      obtain ⟨S,hS⟩ := hrepresent i w
      exact (hnot ⟨S,hS.symm ▸ Or.inl (Or.inl ((T.wordTile_native w).symm ▸ hA))⟩).elim
    · obtain ⟨S,hS,_⟩ := hp.1
      obtain ⟨w,j,he⟩ := T.exists_wordSide S
      have hside : z ∈ T.wordSide w j := he ▸ hS
      refine ⟨j,?_,mem_iUnion.mpr ⟨w,hside⟩⟩
      intro hji
      subst j
      obtain ⟨R,hR⟩ := hrepresent i w
      exact hnot ⟨R,hR.symm ▸ Or.inl (Or.inr hside)⟩
  · intro i z hz
    obtain ⟨w,⟨x,hx,rfl⟩⟩ := mem_iUnion.mp hz
    have hs : T.itineraryMap w x ∈ (D w i).source :=
      (hDs w i).symm ▸ Or.inl (Or.inr ⟨x,hx,rfl⟩)
    rw [← hDeq w i hs,hDseam w i x hx]
    exact ⟨x,hx,rfl⟩
  · exact hsep
  · exact hΩ
  · intro z hz
    obtain ⟨w,i,hi⟩ := T.wordPairs_cover hz
    have hs : z ∈ (D w i).source := (hDs w i).symm ▸ hi
    rw [← hDeq w i hs,hΩ]
    exact mem_iUnion.mpr ⟨i,(hDt w i) ▸ (D w i).map_source hs⟩

end HolomorphicAnosov
