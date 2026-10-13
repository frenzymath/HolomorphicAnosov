import HolomorphicAnosov.Topology.TrianglePresentationFaithfulG6
import HolomorphicAnosov.Topology.GallierXuFaceMapEdgeFibres
import HolomorphicAnosov.Topology.GallierXuSupportClassification
import HolomorphicAnosov.Topology.GallierXuIntervalLinkAdapter
import HolomorphicAnosov.Topology.GallierXuFanTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set
namespace HolomorphicAnosov.Topology.GallierXu

/-- Every consecutive interval-list edge is also an edge of the cyclic list. -/
lemma pathEdge_cycleEdge {N : ℕ} (l : List (Fin N)) {a b : Fin N}
    (h : pathEdge l a b) : cycleEdge l a b := by
  obtain ⟨i, hi, h⟩ := h
  refine ⟨⟨i, by omega⟩, ?_⟩
  have he : finRotate l.length ⟨i, by omega⟩ = ⟨i+1, hi⟩ := by
    apply Fin.ext
    simp [finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt hi]
  rw [he]
  exact h


/-- In a list of at least two link vertices, every entry has a consecutive
neighbor. Use its successor unless it is last, in which case use its predecessor. -/
lemma link_list_neighbors {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (v : Fin N) (l : List (Fin N)) (hlen : 2 ≤ l.length)
    (hpath : ∀ a b, pathEdge l a b → linkEdge K v a b) :
    ∀ a ∈ l, ∃ b, linkEdge K v a b := by
  intro a ha
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  subst a
  by_cases h : i.val + 1 < l.length
  · refine ⟨l.get ⟨i.val + 1, h⟩, hpath _ _ ?_⟩
    exact ⟨i.val, h, Or.inl ⟨rfl, rfl⟩⟩
  · have hi0 : 0 < i.val := by omega
    have hm : i.val - 1 + 1 < l.length := by omega
    refine ⟨l.get ⟨i.val - 1, by omega⟩, hpath _ _ ?_⟩
    refine ⟨i.val - 1, hm, Or.inr ⟨rfl, ?_⟩⟩
    apply congrArg l.get
    apply Fin.ext
    dsimp
    omega


/-- Exact geometric-to-generated fibres for injective original triangle charts.

Source: Lee Proposition 6.14 p.173, with Gallier–Xu's prescribed side parameters
(Proposition 3.2 p.31) and the given circle-or-interval vertex links.
Read the actual triangle occurrences for x and y from their image descriptions.
Their common barycentric point is supported in the intersection of these two
triangles. If the occurrences are the same, their words occupy the same unique
presentation index (triangleWord records all three vertices), and face
injectivity gives x=y. Otherwise their intersection has at most two vertices.
A point in a standard simplex cannot have empty support. If its support has
two vertices u,v, it is originalEdgePoint u v t for a unique t in (0,1).
The pair u,v is an edge in each incident triangle; every unordered triangle
edge occurs among the three cyclic sides. The side-value formulas and face
injectivity identify x and y with these canonical side representatives, so
they are directly edge-identified. If support is a single vertex v, the point
is its singleton coordinate vector. The prescribed circle or interval link
at v orders all incident triangles in a connected fan. Consecutive triangles
share an original edge through v; its endpoint parameter is 0 or 1 according
to min/max order. The side formulas and face injectivity identify those two
vertex representatives by a literal generator. Compose these finitely many
generators along the link fan. This also covers boundary vertices, whose
links are intervals; no closed-surface hypothesis is required. -/
theorem triangle_face_map_fibre_inclusion {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hlinks : SurfaceLinks K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hface : ∀ f : Fin (trianglePresentation K o).length,
      Function.Injective (fun z : Disk ↦ q (f, z)) ∧
      ∃ s : Triangle K, triangleWord s (o s) = (trianglePresentation K o).get f ∧
        Set.range (fun z : Disk ↦ q (f, z)) =
          {x : ↥(carrier K) | ∀ v ∉ s.val, (x : Fin N → ℝ) v = 0})
    (hside : ∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t) :
    ∀ x y, q x = q y →
      Relation.EqvGen (edgeIdentification (trianglePresentation K o)) x y := by
  classical
  let P := trianglePresentation K o
  let R := Relation.EqvGen (edgeIdentification P)
  have rtrans {a b c : FaceDisks P} (hab : R a b) (hbc : R b c) : R a c :=
    Relation.EqvGen.trans a b c hab hbc
  let Side (f : Fin P.length) (u v : Fin N) :=
    ∃ i : Fin (P.get f).length, ((P.get f).get i).1 = edgeLabel u v
  have getSide (s : Triangle K) (f : Fin P.length)
      (hs : triangleWord s (o s) = P.get f) {u v : Fin N}
      (hu : u ∈ s.val) (hv : v ∈ s.val) (hne : u ≠ v) : Side f u v := by
    have h := triangle_pair_side s (o s) hu hv hne
    rw [hs] at h
    exact h
  have hinj : ∀ f, Function.Injective (fun z : Disk ↦ q (f, z)) := fun f ↦ (hface f).1
  have sameEdge {x y : FaceDisks P} {u v : Fin N} (hne : u ≠ v)
      (hx : Side x.1 u v) (hy : Side y.1 u v) (heq : q x = q y)
      (hz : ∀ w, w ∉ ({u,v} : Finset (Fin N)) → (q x : Fin N → ℝ) w = 0) : R x y := by
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    obtain ⟨t, ht, hx⟩ := simplex_two_vertex_support_unordered (q x).property.1 hne hz
    exact Relation.EqvGen.rel _ _
      (face_map_edge_value_identification K o q hinj hside heq i j hne ht hi hj hx)
  have vertex {x y : FaceDisks P} (v : Fin N)
      (hx : (q x : Fin N → ℝ) = Pi.single v 1)
      (hy : (q y : Fin N → ℝ) = Pi.single v 1)
      (s t : Triangle K) (hs : triangleWord s (o s) = P.get x.1)
      (ht : triangleWord t (o t) = P.get y.1) (hvs : v ∈ s.val) (hvt : v ∈ t.val) : R x y := by
    obtain ⟨l, hnodup, hmem, hshape⟩ := hlinks v
    have hlen : 2 ≤ l.length := by rcases hshape with h | h <;> omega
    have hpath : ∀ a b, pathEdge l a b → linkEdge K v a b := by
      intro a b hab
      rcases hshape with h | h
      · exact (h.2 a b).mpr (pathEdge_cycleEdge l hab)
      · exact (h.2 a b).mpr hab
    have parameter (a : Fin N) (hav : v ≠ a) :
        ∃ r ∈ Icc (0:ℝ) 1, (q x : Fin N → ℝ) = originalEdgePoint v a r := by
      apply simplex_two_vertex_support_unordered (q x).property.1 hav
      intro w hw
      rw [hx]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
      simp [hw.1]
    have compare {z z' : FaceDisks P} {a : Fin N} (hav : v ≠ a)
        (hz : (q z : Fin N → ℝ) = Pi.single v 1)
        (hz' : (q z' : Fin N → ℝ) = Pi.single v 1)
        (hza : Side z.1 v a) (hz'a : Side z'.1 v a) : R z z' := by
      apply sameEdge hav hza hz'a (Subtype.ext (hz.trans hz'.symm))
      intro w hw
      rw [hz]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
      simp [hw.1]
    have fromTriangle (T : Triangle K) (a : Fin N) (hvT : v ∈ T.val)
        (haT : a ∈ T.val) (hav : v ≠ a) :
        ∃ z : FaceDisks P, triangleWord T (o T) = P.get z.1 ∧
          (q z : Fin N → ℝ) = Pi.single v 1 := by
      obtain ⟨f, hf⟩ := triangle_word_occurs K o T
      obtain ⟨i, hi⟩ := getSide T f hf hvT haT hav
      obtain ⟨r, hr, hxr⟩ := parameter a hav
      exact ⟨(f, sidePointDisk f i r), hf, (hside f i v a r hav hr hi).trans
        (hxr.symm.trans hx)⟩
    have hex (a : Fin N) (ha : a ∈ l) :
        ∃ z : FaceDisks P, Side z.1 v a ∧ (q z : Fin N → ℝ) = Pi.single v 1 := by
      obtain ⟨b, hab⟩ := link_list_neighbors K v l hlen hpath a ha
      let T : Triangle K := ⟨{v,a,b}, hab.2.2.2, by
        simp [Finset.card_insert_of_notMem, hab.1,
          hab.2.1.symm, hab.2.2.1.symm]⟩
      obtain ⟨z, hz, hvz⟩ := fromTriangle T a (by simp [T]) (by simp [T]) hab.2.1.symm
      exact ⟨z, getSide T z.1 hz (by simp [T]) (by simp [T]) hab.2.1.symm, hvz⟩
    let rep (a : Fin N) : FaceDisks P := if ha : a ∈ l then (hex a ha).choose else x
    have hrep (a : Fin N) (ha : a ∈ l) :
        Side (rep a).1 v a ∧ (q (rep a) : Fin N → ℝ) = Pi.single v 1 := by
      simpa only [rep, dite_eq_left ha] using (hex a ha).choose_spec
    have bridge {a b : Fin N} (hab : pathEdge l a b) : R (rep a) (rep b) := by
      have hl := hpath a b hab
      have ha : a ∈ l := (hmem a).mpr ⟨hl.2.1, (linkEdge_edge_faces K v a b hl).1⟩
      have hb : b ∈ l := (hmem b).mpr ⟨hl.2.2.1, (linkEdge_edge_faces K v a b hl).2⟩
      let T : Triangle K := ⟨{v,a,b}, hl.2.2.2, by
        simp [Finset.card_insert_of_notMem, hl.1,
          hl.2.1.symm, hl.2.2.1.symm]⟩
      obtain ⟨z, hz, hvz⟩ := fromTriangle T a (by simp [T]) (by simp [T]) hl.2.1.symm
      have hza := getSide T z.1 hz (by simp [T]) (by simp [T]) hl.2.1.symm
      have hzb := getSide T z.1 hz (by simp [T]) (by simp [T]) hl.2.2.1.symm
      exact rtrans (compare hl.2.1.symm (hrep a ha).2 hvz (hrep a ha).1 hza)
        (compare hl.2.2.1.symm hvz (hrep b hb).2 hzb (hrep b hb).1)
    obtain ⟨a, has, hav⟩ := Finset.exists_mem_ne (by rw [s.property.2]; norm_num) v
    obtain ⟨b, hbt, hbv⟩ := Finset.exists_mem_ne (by rw [t.property.2]; norm_num) v
    have ha : a ∈ l := (hmem a).mpr ⟨hav, (K.isRelLowerSet_faces s.property.1).2
      (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption) ⟨v, by simp⟩⟩
    have hb : b ∈ l := (hmem b).mpr ⟨hbv, (K.isRelLowerSet_faces t.property.1).2
      (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption) ⟨v, by simp⟩⟩
    exact rtrans (compare hav.symm hx (hrep a ha).2 (getSide s x.1 hs hvs has hav.symm)
      (hrep a ha).1)
      (rtrans (eqvGen_of_interval_fan_transport (by omega) (edgeIdentification P) rep bridge ha hb)
        (compare hbv.symm (hrep b hb).2 hy (hrep b hb).1
          (getSide t y.1 ht hvt hbt hbv.symm)))
  intro x y hxy
  obtain ⟨s, hs, hrs⟩ := (hface x.1).2
  obtain ⟨t, ht, hrt⟩ := (hface y.1).2
  have hxs : ∀ v ∉ s.val, (q x : Fin N → ℝ) v = 0 := by
    have h : q x ∈ Set.range (fun z : Disk ↦ q (x.1,z)) := ⟨x.2, rfl⟩
    rwa [hrs] at h
  have hyt : ∀ v ∉ t.val, (q x : Fin N → ℝ) v = 0 := by
    have h : q y ∈ Set.range (fun z : Disk ↦ q (y.1,z)) := ⟨y.2, rfl⟩
    rw [hrt] at h
    rwa [hxy]
  by_cases hst : s = t
  · have hf : x.1 = y.1 := (triangle_presentation_nodup K o).get_inj_iff.mp
      (hs.symm.trans (hst ▸ ht))
    have heq : x = y := by
      rcases x with ⟨f,z⟩
      rcases y with ⟨g,w⟩
      dsimp at hf
      subst g
      exact Prod.ext rfl (hinj f hxy)
    subst y
    exact Relation.EqvGen.refl x
  · rcases support_single_or_pair_of_distinct_triangles (q x).property.1 hst hxs hyt with
      ⟨v, hvs, hvt, hx⟩ | ⟨u,v,huv,hus,hvs,hut,hvt,hz⟩
    · exact vertex v hx (by rw [← hxy]; exact hx) s t hs ht hvs hvt
    · exact sameEdge huv (getSide s x.1 hs hus hvs huv) (getSide t y.1 ht hut hvt huv) hxy hz

end HolomorphicAnosov.Topology.GallierXu
