import HolomorphicAnosov.Geometry.LyubichReflectionLocalChartsG11
import HolomorphicAnosov.Geometry.IdealTriangleReflectionTiling
import HolomorphicAnosov.Geometry.IdealDiskSideReflectionEndpoints
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCarrierG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCoordinatesG6
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.Convex.StrictConvexSpace

noncomputable section

/-! Word transport and reflected triangles in the ideal-disk tiling. (Lyubich, §2.4.13; Epstein–Petronio, Thm 5.5.) -/

namespace HolomorphicAnosov
open scoped ComplexConjugate
open IdealDiskTriangle

/-- Circular reflection preserves the closed disk, including its boundary. -/
theorem reflection_norm_le_one {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ ≤ 1) :
    ‖idealDiskSideReflection p q z‖ ≤ 1 := by
  rcases hz.eq_or_lt with hz | hz
  · exact (IdealDiskTriangle.reflection_unit hp hq hpq hz).le
  · exact (idealDiskSideReflection_mem_disk_g6 hp hq hpq hz).le

/-- The explicit reflection is involutive on the complete closed disk. -/
theorem reflection_involutive_closed {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ ≤ 1) :
    idealDiskSideReflection p q (idealDiskSideReflection p q z) = z := by
  have hd := IdealDiskTriangle.reflection_denominator_closed hp hq hpq hz
  have hd' := IdealDiskTriangle.reflection_denominator_closed hp hq hpq
    (reflection_norm_le_one hp hq hpq hz)
  have hau : p * conj p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
  have hbu : q * conj q = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq]; norm_num
  unfold idealDiskSideReflection at hd' ⊢
  apply (div_eq_iff hd').mpr
  simp only [map_div₀, map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj]
  have hdc : 2 - (conj p + conj q) * z ≠ 0 := by
    simpa only [map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj] using
      (map_ne_zero (starRingEnd ℂ)).mpr hd
  field_simp
  have hst := (ideal_reflection_coefficients_g6 hp hq).2
  have hstc := congrArg (starRingEnd ℂ) hst
  simp only [map_mul, map_add, Complex.conj_conj] at hstc hst
  linear_combination -2 * hst - 2 * z^2 * hstc +
    4 * z * (q * conj q) * hau + 4 * z * hbu


end HolomorphicAnosov

namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- Conjugating a circular reflection by another circular reflection moves its two endpoints by the same map. -/
theorem reflection_covariance {p q a b z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) (hz : ‖z‖ ≤ 1) :
    idealDiskSideReflection (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)
      (idealDiskSideReflection p q z) =
      idealDiskSideReflection p q (idealDiskSideReflection a b z) := by
  have hra := IdealDiskTriangle.reflection_unit hp hq hpq ha
  have hrb := IdealDiskTriangle.reflection_unit hp hq hpq hb
  have hrab : idealDiskSideReflection p q a ≠ idealDiskSideReflection p q b :=
    fun he ↦ hab (IdealDiskTriangle.reflection_inj_closed hp hq hpq ha.le hb.le he)
  have hrz := reflection_norm_le_one hp hq hpq hz
  have habz := reflection_norm_le_one ha hb hab hz
  have hda := IdealDiskTriangle.reflection_denominator_closed hp hq hpq ha.le
  have hdb := IdealDiskTriangle.reflection_denominator_closed hp hq hpq hb.le
  have hdz := IdealDiskTriangle.reflection_denominator_closed hp hq hpq hz
  have hdi := IdealDiskTriangle.reflection_denominator_closed ha hb hab hz
  have hdl := IdealDiskTriangle.reflection_denominator_closed hra hrb hrab hrz
  have hdr := IdealDiskTriangle.reflection_denominator_closed hp hq hpq habz
  have hunit (u : ℂ) (hu : ‖u‖ = 1) : conj u = u⁻¹ := by
    have hmul : u * conj u = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
    exact eq_inv_of_mul_eq_one_right hmul
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (hp ▸ one_ne_zero)
  have hq0 : q ≠ 0 := norm_ne_zero_iff.mp (hq ▸ one_ne_zero)
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (hb ▸ one_ne_zero)
  have hdcz : 2 - (conj p + conj q) * z ≠ 0 := by
    simpa only [map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj] using
      (map_ne_zero (starRingEnd ℂ)).mpr hdz
  have hdci : 2 - (conj a + conj b) * z ≠ 0 := by
    simpa only [map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj] using
      (map_ne_zero (starRingEnd ℂ)).mpr hdi
  unfold idealDiskSideReflection at hdl hdr ⊢
  simp only [map_div₀, map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj] at hdl hdr ⊢
  apply (div_eq_div_iff hdl hdr).mpr
  field_simp [hda, hdb, hdcz, hdci]
  simp only [hunit p hp, hunit q hq, hunit a ha, hunit b hb] at hda hdb hdcz hdci ⊢
  field_simp at hda hdb hdcz hdci
  have hdn := (div_ne_zero_iff.mp hdci).1
  ring_nf at hdn
  field_simp [hdn]
  ring_nf
  field_simp (disch := first | assumption | (solve | norm_num) | (convert hdn using 1; ring))
  ring

end HolomorphicAnosov

namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- Every finite itinerary preserves the closed disk. -/
theorem itineraryMap_closedDisk {T : MarkedIdealDiskTriangle} (w : List (Fin 3))
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖T.itineraryMap w z‖ ≤ 1 := by
  induction w with
  | nil => simpa [MarkedIdealDiskTriangle.itineraryMap] using hz
  | cons i w ih =>
    rw [MarkedIdealDiskTriangle.itineraryMap_cons, Function.comp_apply]
    apply reflection_norm_le_one (T.norm_vertex i) (T.norm_vertex (i + 1))
      (T.vertex_ne_next i)
    exact ih

/-- The itinerary maps are injective on the closed disk. -/
theorem itineraryMap_injOn_closedDisk {T : MarkedIdealDiskTriangle} (w : List (Fin 3)) :
    Set.InjOn (T.itineraryMap w) {z : ℂ | ‖z‖ ≤ 1} := by
  induction w with
  | nil => exact fun _ _ _ _ he ↦ he
  | cons i w ih =>
    intro x hx y hy he
    rw [T.itineraryMap_cons] at he
    apply ih hx hy
    exact IdealDiskTriangle.reflection_inj_closed (T.norm_vertex i) (T.norm_vertex (i + 1))
      (T.vertex_ne_next i) (itineraryMap_closedDisk w hx) (itineraryMap_closedDisk w hy) he

end HolomorphicAnosov
namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- Finite reflection words preserve unit endpoints. -/
theorem itineraryMap_unitCircle {T : MarkedIdealDiskTriangle} (w : List (Fin 3))
    {z : ℂ} (hz : ‖z‖ = 1) : ‖T.itineraryMap w z‖ = 1 := by
  induction w with
  | nil => exact hz
  | cons i w ih =>
    rw [T.itineraryMap_cons, Function.comp_apply]
    exact IdealDiskTriangle.reflection_unit (T.norm_vertex i) (T.norm_vertex (i + 1))
      (T.vertex_ne_next i) ih

/-- Finite word transport commutes with side reflection on endpoints and disk points. -/
theorem itineraryMap_reflection_covariance (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) {a b z : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : a ≠ b) (hz : ‖z‖ ≤ 1) :
    idealDiskSideReflection (T.itineraryMap w a) (T.itineraryMap w b) (T.itineraryMap w z) =
      T.itineraryMap w (idealDiskSideReflection a b z) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [T.itineraryMap_cons, Function.comp_apply]
    rw [reflection_covariance (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i)
      (itineraryMap_unitCircle w ha) (itineraryMap_unitCircle w hb)
      (fun he ↦ hab (itineraryMap_injOn_closedDisk w ha.le hb.le he))
      (itineraryMap_closedDisk w hz), ih]

/-- Covariance sends a physical reflection step to a physical reflection step. -/
theorem reflectionStep_image {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    {V W : Finset ℂ} (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hstep : reflectionStep V W) :
    reflectionStep (V.image (idealDiskSideReflection p q)) (W.image (idealDiskSideReflection p q)) := by
  classical
  obtain ⟨a, haV, b, hbV, hab, rfl⟩ := hstep
  refine ⟨_, Finset.mem_image_of_mem _ haV, _, Finset.mem_image_of_mem _ hbV,
    fun he ↦ hab (IdealDiskTriangle.reflection_inj_closed hp hq hpq (hV a haV).le (hV b hbV).le he), ?_⟩
  unfold reflectedVertices
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro z hz
  dsimp only [Function.comp_apply]
  exact (reflection_covariance hp hq hpq (hV a haV) (hV b hbV) hab (hV z hz).le).symm

end HolomorphicAnosov

namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- A physical reflection step preserves unit-circle membership of every vertex. -/
theorem reflectionStep_unit_vertices {V W : Finset ℂ}
    (hV : ∀ z ∈ V, ‖z‖ = 1) (hVW : reflectionStep V W) :
    ∀ z ∈ W, ‖z‖ = 1 := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := hVW
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact IdealDiskTriangle.reflection_unit (hV a ha) (hV b hb) hab (hV w hw)

/-- All finite reachable vertex sets remain on the unit circle. -/
theorem reachable_unit_vertices {V W : Finset ℂ}
    (hV : ∀ z ∈ V, ‖z‖ = 1) (hVW : reachable V W) :
    ∀ z ∈ W, ‖z‖ = 1 := by
  induction hVW with
  | refl => exact hV
  | @tail A B hVA hAB ih => exact reflectionStep_unit_vertices ih hAB

/-- An arbitrary reflection transports a complete finite physical itinerary from V to W into one from r(V) to r(W). -/
theorem reachable_reflection_image {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    {V W : Finset ℂ} (hV : ∀ z ∈ V, ‖z‖ = 1) (hVW : reachable V W) :
    reachable (V.image (idealDiskSideReflection p q)) (W.image (idealDiskSideReflection p q)) := by
  induction hVW with
  | refl => exact Relation.ReflTransGen.refl
  | @tail A B hVA hAB ih =>
    exact ih.tail (reflectionStep_image hp hq hpq (reachable_unit_vertices hV hVA) hAB)

/-- Every original-generator word yields a physically reachable vertex set. -/
theorem MarkedIdealDiskTriangle.itinerary_vertices_reachable
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) :
    reachable (Finset.univ.image T.vertex) ((Finset.univ.image T.vertex).image (T.itineraryMap w)) := by
  classical
  let V := Finset.univ.image T.vertex
  have hV : ∀ z ∈ V, ‖z‖ = 1 := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact T.norm_vertex i
  induction w with
  | nil => simpa [itineraryMap, V, reachable] using (Relation.ReflTransGen.refl : reachable V V)
  | cons i w ih =>
    rw [T.itineraryMap_cons, ← Finset.image_image]
    have hfirst : reachable V (V.image (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1)))) :=
      Relation.ReflTransGen.single ⟨T.vertex i, Finset.mem_image_of_mem _ (Finset.mem_univ i),
        T.vertex (i + 1), Finset.mem_image_of_mem _ (Finset.mem_univ (i + 1)), T.vertex_ne_next i, rfl⟩
    exact hfirst.trans (reachable_reflection_image (T.norm_vertex i) (T.norm_vertex (i + 1))
      (T.vertex_ne_next i) hV ih)

end HolomorphicAnosov
namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- A side reflection is independent of the order of its endpoints. -/
theorem reflection_swap (p q : ℂ) : idealDiskSideReflection p q = idealDiskSideReflection q p := by
  funext z
  unfold idealDiskSideReflection
  congr 1 <;> ring

/-- Every unordered pair of distinct marks is a cyclic side. -/
theorem fin_three_pair_cyclic (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, (i = k ∧ j = k + 1) ∨ (j = k ∧ i = k + 1) := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

/-- A physical step from a word's vertex set is represented by appending one of the original three side generators. -/
theorem MarkedIdealDiskTriangle.reflectionStep_itinerary_vertices
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) {W : Finset ℂ}
    (hstep : reflectionStep ((Finset.univ.image T.vertex).image (T.itineraryMap w)) W) :
    ∃ i : Fin 3, W = (Finset.univ.image T.vertex).image (T.itineraryMap (w ++ [i])) := by
  classical
  obtain ⟨a, haV, b, hbV, hab, rfl⟩ := hstep
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp haV
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha₀
  obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hbV
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb₀
  have hij : i ≠ j := fun he ↦ hab (by rw [he])
  obtain ⟨k, hk | hk⟩ := fin_three_pair_cyclic i j hij
  all_goals
    refine ⟨k, ?_⟩
    unfold reflectedVertices
    rw [Finset.image_image]
    apply Finset.image_congr
    intro z hz
    have hz1 : ‖z‖ = 1 := by
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hz
      exact T.norm_vertex l
    change idealDiskSideReflection (T.itineraryMap w (T.vertex i))
      (T.itineraryMap w (T.vertex j)) (T.itineraryMap w z) = T.itineraryMap (w ++ [k]) z
    rw [itineraryMap_reflection_covariance T w (T.norm_vertex i) (T.norm_vertex j)
      (T.distinct.ne hij) hz1.le, T.itineraryMap_append]
    simp only [Function.comp_apply, T.itineraryMap_cons]
    change T.itineraryMap w (idealDiskSideReflection (T.vertex i) (T.vertex j) z) =
      T.itineraryMap w (idealDiskSideReflection (T.vertex k) (T.vertex (k + 1)) z)
  · rw [hk.1, hk.2]
  · rw [hk.1, hk.2, reflection_swap]

/-- Every physically reachable vertex set is represented by an original side-generator word. -/
theorem MarkedIdealDiskTriangle.reachable_vertices_eq_itinerary
    (T : MarkedIdealDiskTriangle) {W : Finset ℂ}
    (hW : reachable (Finset.univ.image T.vertex) W) :
    ∃ w : List (Fin 3), W = (Finset.univ.image T.vertex).image (T.itineraryMap w) := by
  induction hW with
  | refl => exact ⟨[], by simp [itineraryMap]⟩
  | @tail A B hVA hAB ih =>
    obtain ⟨w, rfl⟩ := ih
    obtain ⟨i, hi⟩ := T.reflectionStep_itinerary_vertices w hAB
    exact ⟨w ++ [i], hi⟩

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set IdealDiskTriangle
open scoped ComplexConjugate

/-- Reflecting any unit-circle triple in any disk geodesic produces another unit-circle triple; injectivity preserves its exact cardinality. -/
def reflectedVertexTriple (V : VertexTriple) {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) : VertexTriple :=
  ⟨V.val.image (idealDiskSideReflection p q), by
    constructor
    · rw [Finset.card_image_of_injOn, V.property.1]
      intro x hx y hy he
      exact IdealDiskTriangle.reflection_inj_closed hp hq hpq
        (V.property.2 x hx).le (V.property.2 y hy).le he
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact IdealDiskTriangle.reflection_unit hp hq hpq (V.property.2 w hw)⟩

/-- The exact cardinality three persists along physical itineraries. -/
theorem reachable_three_vertices (V : VertexTriple) {W : Finset ℂ}
    (hW : reachable V.val W) : W.card = 3 := by
  induction hW with
  | refl => exact V.property.1
  | @tail A B hVA hAB ih =>
    let VA : VertexTriple := ⟨A, ih, reachable_unit_vertices V.property.2 hVA⟩
    obtain ⟨p, hpA, q, hqA, hpq, rfl⟩ := hAB
    exact (reflectedVertexTriple VA (VA.property.2 p hpA) (VA.property.2 q hqA) hpq).property.1

/-- Reflection in an original side maps every reachable carrier to the corresponding reflected carrier. (Epstein–Petronio, Definitions 4.2 and 4.5.) -/
theorem reflection_reachable_carrier_image (V : VertexTriple) {p q : ℂ}
    (hpV : p ∈ V.val) (hqV : q ∈ V.val) (hpq : p ≠ q)
    {W : Finset ℂ} (hW : reachable V.val W) :
    idealDiskSideReflection p q '' triangle W =
      triangle (W.image (idealDiskSideReflection p q)) := by
  classical
  let r := idealDiskSideReflection p q
  have hp := V.property.2 p hpV
  have hq := V.property.2 q hqV
  induction hW with
  | refl => exact idealDiskSideReflection_triangle_image_g6 V hp hq hpq hpV hqV
  | @tail A B hVA hAB ih =>
    let VA : VertexTriple := ⟨A, reachable_three_vertices V hVA,
      reachable_unit_vertices V.property.2 hVA⟩
    obtain ⟨a, haA, b, hbA, hab, rfl⟩ := hAB
    have ha := VA.property.2 a haA
    have hb := VA.property.2 b hbA
    let RA := reflectedVertexTriple VA hp hq hpq
    have hrab : r a ≠ r b := fun he ↦ hab (IdealDiskTriangle.reflection_inj_closed hp hq hpq ha.le hb.le he)
    have hstep := idealDiskSideReflection_triangle_image_g6 VA ha hb hab haA hbA
    have hrstep := idealDiskSideReflection_triangle_image_g6 RA
      (IdealDiskTriangle.reflection_unit hp hq hpq ha) (IdealDiskTriangle.reflection_unit hp hq hpq hb) hrab
      (Finset.mem_image_of_mem _ haA) (Finset.mem_image_of_mem _ hbA)
    have himg : r '' (idealDiskSideReflection a b '' triangle A) =
        idealDiskSideReflection (r a) (r b) '' (r '' triangle A) := by
      rw [← Set.image_comp, ← Set.image_comp]
      apply Set.EqOn.image_eq
      intro z hz
      exact (reflection_covariance hp hq hpq ha hb hab hz.1.le).symm
    have hverts : (reflectedVertices A a b).image r =
        reflectedVertices RA.val (r a) (r b) := by
      unfold reflectedVertices
      rw [Finset.image_image]
      change A.image _ = (A.image r).image _
      rw [Finset.image_image]
      apply Finset.image_congr
      intro z hz
      exact (reflection_covariance hp hq hpq ha hb hab (VA.property.2 z hz).le).symm
    rw [← hstep, himg, ih]
    exact hrstep.trans (congrArg triangle hverts.symm)

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set IdealDiskTriangle

/-- An open partial homeomorphism carrying one set onto another carries its interior onto the other's interior, when both sets lie in its domains. -/
theorem partialHomeomorph_image_interior
    (e : OpenPartialHomeomorph ℂ ℂ) {S T : Set ℂ}
    (hS : S ⊆ e.source) (hT : T ⊆ e.target) (he : e '' S = T) :
    e '' interior S = interior T := by
  have hh : e.IsImage S T := by
    intro x hx
    rw [← he]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact e.injOn (hS hy) hx hxy ▸ hy
    · exact fun hs ↦ Set.mem_image_of_mem e hs
  have hi := hh.interior.image_eq
  rw [Set.inter_eq_right.mpr (Set.Subset.trans interior_subset hS),
    Set.inter_eq_right.mpr (Set.Subset.trans interior_subset hT)] at hi
  exact hi

/-- Generator reflections transport the literal open interiors of all reached triangle carriers. -/
theorem reflection_reachable_openTriangle_image (V : VertexTriple) {p q : ℂ}
    (hpV : p ∈ V.val) (hqV : q ∈ V.val) (hpq : p ≠ q)
    {W : Finset ℂ} (hW : reachable V.val W) :
    idealDiskSideReflection p q '' openTriangle W =
      openTriangle (W.image (idealDiskSideReflection p q)) := by
  let e := idealDiskSideReflectionPartial p q (V.property.2 p hpV) (V.property.2 q hqV) hpq
  exact partialHomeomorph_image_interior e (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.1)
    (reflection_reachable_carrier_image V hpV hqV hpq hW)

/-- A word transports the initial native carrier to the carrier indexed by its vertex image. -/
theorem MarkedIdealDiskTriangle.itinerary_native_carrier (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) :
    T.itineraryMap w '' triangle (Finset.univ.image T.vertex) =
      triangle ((Finset.univ.image T.vertex).image (T.itineraryMap w)) := by
  classical
  let V : VertexTriple := ⟨Finset.univ.image T.vertex, by
    constructor
    · rw [Finset.card_image_of_injective _ T.distinct]; rfl
    · intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact T.norm_vertex i⟩
  induction w with
  | nil => simp [itineraryMap]
  | cons i w ih =>
    rw [T.itineraryMap_cons, Set.image_comp, ih, ← Finset.image_image]
    exact reflection_reachable_carrier_image V
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      (Finset.mem_image_of_mem _ (Finset.mem_univ (i + 1))) (T.vertex_ne_next i)
      (T.itinerary_vertices_reachable w)

/-- A word transports the initial native open interior to the native open interior indexed by its vertex image. -/
theorem MarkedIdealDiskTriangle.itinerary_native_openTriangle (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) :
    T.itineraryMap w '' openTriangle (Finset.univ.image T.vertex) =
      openTriangle ((Finset.univ.image T.vertex).image (T.itineraryMap w)) := by
  classical
  let V : VertexTriple := ⟨Finset.univ.image T.vertex, by
    constructor
    · rw [Finset.card_image_of_injective _ T.distinct]; rfl
    · intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact T.norm_vertex i⟩
  induction w with
  | nil => simp [itineraryMap]
  | cons i w ih =>
    rw [T.itineraryMap_cons, Set.image_comp, ih, ← Finset.image_image]
    exact reflection_reachable_openTriangle_image V
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      (Finset.mem_image_of_mem _ (Finset.mem_univ (i + 1))) (T.vertex_ne_next i)
      (T.itinerary_vertices_reachable w)

end HolomorphicAnosov


/-! Word transport and reflected triangles in the ideal-disk tiling. (Lyubich, §2.4.13; Epstein–Petronio, Thm 5.5.) -/

namespace HolomorphicAnosov

/-- Ordered product of edge transports along a graph walk. -/
def treeWalkProduct {V A : Type*} [Group A] {G : SimpleGraph V}
    (e : V → V → A) {u v : V} : G.Walk u v → A
  | .nil => 1
  | @SimpleGraph.Walk.cons _ _ _ w _ _ p => e u w * treeWalkProduct e p

/-- Every walk in an acyclic graph has the same edge transport as a simple path between its endpoints. -/
theorem treeWalkProduct_exists_path {V A : Type*} [Group A] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (e : V → V → A)
    (hinv : ∀ u v, G.Adj u v → e u v * e v u = 1)
    {u v : V} (p : G.Walk u v) :
    ∃ q : G.Walk u v, q.IsPath ∧ treeWalkProduct e p = treeWalkProduct e q := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp, rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨q, hq, heq⟩ := ih
    let h0 := h
    by_cases hu : u ∈ q.support
    · have hs := hG.eq_snd_of_adj_start hq h.symm hu
      cases q with
      | nil =>
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
        exact (h.ne hu).elim
      | cons h' q' =>
        simp only [SimpleGraph.Walk.snd_cons] at hs
        subst u
        refine ⟨q', (SimpleGraph.Walk.cons_isPath_iff h' q').mp hq |>.1, ?_⟩
        simp only [treeWalkProduct] at heq ⊢
        rw [heq, ← mul_assoc, hinv _ _ h0, one_mul]
    · refine ⟨.cons h q, (SimpleGraph.Walk.cons_isPath_iff h q).mpr ⟨hq, hu⟩, ?_⟩
      simp only [treeWalkProduct, heq]

/-- Edge transports satisfying reversal cancellation have identical products along any two walks with common endpoints in an acyclic graph. -/
theorem treeWalkProduct_eq {V A : Type*} [Group A] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (e : V → V → A)
    (hinv : ∀ u v, G.Adj u v → e u v * e v u = 1)
    {u v : V} (p q : G.Walk u v) : treeWalkProduct e p = treeWalkProduct e q := by
  obtain ⟨p', hp', hep⟩ := treeWalkProduct_exists_path hG e hinv p
  obtain ⟨q', hq', heq⟩ := treeWalkProduct_exists_path hG e hinv q
  have he : p' = q' :=
    Subtype.ext_iff.mp ((hG.subsingleton_path u v).elim ⟨p', hp'⟩ ⟨q', hq'⟩)
  rw [hep, he, ← heq]

end HolomorphicAnosov

noncomputable section
namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- The closed disk on which every reflected word acts, including the ideal vertices. -/
def closedReflectionDisk : Set ℂ := {z : ℂ | ‖z‖ ≤ 1}

/-- The closed-disk permutation defined by one literal side reflection. -/
def reflectionDiskPerm (p q : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    Equiv.Perm closedReflectionDisk where
  toFun z := ⟨idealDiskSideReflection p q z, reflection_norm_le_one hp hq hpq z.property⟩
  invFun z := ⟨idealDiskSideReflection p q z, reflection_norm_le_one hp hq hpq z.property⟩
  left_inv z := Subtype.ext (reflection_involutive_closed hp hq hpq z.property)
  right_inv z := Subtype.ext (reflection_involutive_closed hp hq hpq z.property)

/-- The geometric and value permutations contributed by one side crossing. -/
def reflectionCrossingPerm (p q : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    Equiv.Perm closedReflectionDisk × Equiv.Perm ℂ :=
  (reflectionDiskPerm p q hp hq hpq, Complex.conjCLE.toEquiv)

/-- Reversing a side crossing cancels both its geometric reflection and its value conjugation. -/
theorem reflectionCrossingPerm_mul_self (p q : ℂ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    reflectionCrossingPerm p q hp hq hpq * reflectionCrossingPerm p q hp hq hpq = 1 := by
  apply Prod.ext
  · apply Equiv.ext
    intro z
    apply Subtype.ext
    exact reflection_involutive_closed hp hq hpq z.property
  · apply Equiv.ext
    intro z
    exact Complex.conj_conj z

/-- Equal ambient reflections induce equal side crossing permutations. -/
theorem reflectionCrossingPerm_congr {p q a b : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b)
    (h : idealDiskSideReflection p q = idealDiskSideReflection a b) :
    reflectionCrossingPerm p q hp hq hpq = reflectionCrossingPerm a b ha hb hab := by
  apply Prod.ext
  · apply Equiv.ext
    intro z
    apply Subtype.ext
    exact congrFun h z
  · rfl

/-- Every adjacent pair is joined by its actual shared-side reflection. -/
theorem reached_adjacent_crossing_endpoints
    (V : VertexTriple) (A B : ReachedTriangle V)
    (hstepAdj : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    (hAB : (dualGraph V).Adj A B) :
    ∃ p ∈ A.val.val, ∃ q ∈ A.val.val, p ≠ q ∧
      p ∈ B.val.val ∧ q ∈ B.val.val ∧
      B.val.val = reflectedVertices A.val.val p q := by
  obtain ⟨p, hp, q, hq, hpq, hB⟩ := (hstepAdj A B).mpr hAB
  have hfix := idealDiskSideReflection_endpoints (A.val.property.2 p hp)
    (A.val.property.2 q hq) hpq
  refine ⟨p,hp,q,hq,hpq,?_,?_,hB⟩
  · rw [hB]
    exact Finset.mem_image.mpr ⟨p,hp,hfix.1⟩
  · rw [hB]
    exact Finset.mem_image.mpr ⟨q,hq,hfix.2⟩

/-- The pair of reflection and target conjugation attached to an oriented edge of the physical dual graph. -/
def reachedEdgePerm (V : VertexTriple)
    (hstepAdj : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    (A B : ReachedTriangle V) : Equiv.Perm closedReflectionDisk × Equiv.Perm ℂ := by
  classical
  exact if h : (dualGraph V).Adj A B then
    let hdata := reached_adjacent_crossing_endpoints V A B hstepAdj h
    let p := hdata.choose
    let q := hdata.choose_spec.2.choose
    reflectionCrossingPerm p q (A.val.property.2 p hdata.choose_spec.1)
      (A.val.property.2 q hdata.choose_spec.2.choose_spec.1)
      hdata.choose_spec.2.choose_spec.2.1
  else 1

/-- Any actual shared-side endpoints compute the canonical edge transport. -/
theorem reachedEdgePerm_eq
    (V : VertexTriple)
    (hstepAdj : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    (hsideUnique : ∀ A B : ReachedTriangle V, (dualGraph V).Adj A B →
      ∀ S U : Set ℂ, hasSide A.val.val S → hasSide B.val.val S →
        hasSide A.val.val U → hasSide B.val.val U → S = U)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b → IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (A B : ReachedTriangle V) (hAB : (dualGraph V).Adj A B)
    {p q : ℂ} (hpA : p ∈ A.val.val) (hqA : q ∈ A.val.val) (hpq : p ≠ q)
    (hpB : p ∈ B.val.val) (hqB : q ∈ B.val.val) :
    reachedEdgePerm V hstepAdj A B =
      reflectionCrossingPerm p q (A.val.property.2 p hpA) (A.val.property.2 q hqA) hpq := by
  classical
  unfold reachedEdgePerm
  rw [dite_eq_left hAB]
  dsimp only
  apply reflectionCrossingPerm_congr
  apply hreflection
  · exact A.val.property.2 _
      (reached_adjacent_crossing_endpoints V A B hstepAdj hAB).choose_spec.1
  · exact A.val.property.2 _
      (reached_adjacent_crossing_endpoints V A B hstepAdj hAB).choose_spec.2.choose_spec.1
  · exact (reached_adjacent_crossing_endpoints V A B hstepAdj hAB).choose_spec.2.choose_spec.2.1
  · exact A.val.property.2 p hpA
  · exact A.val.property.2 q hqA
  · exact hpq
  · let hd := reached_adjacent_crossing_endpoints V A B hstepAdj hAB
    exact hsideUnique A B hAB _ _
      ⟨hd.choose,hd.choose_spec.1,hd.choose_spec.2.choose,
        hd.choose_spec.2.choose_spec.1,hd.choose_spec.2.choose_spec.2.1,rfl⟩
      ⟨hd.choose,hd.choose_spec.2.choose_spec.2.2.1,hd.choose_spec.2.choose,
        hd.choose_spec.2.choose_spec.2.2.2.1,hd.choose_spec.2.choose_spec.2.1,rfl⟩
      ⟨p,hpA,q,hqA,hpq,rfl⟩ ⟨p,hpB,q,hqB,hpq,rfl⟩

end HolomorphicAnosov

namespace HolomorphicAnosov
open IdealDiskTriangle

/-- Traversing the same geometric edge in the opposite direction gives inverse transport. -/
theorem reachedEdgePerm_reverse
    (V : VertexTriple)
    (hstepAdj : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    (hsideUnique : ∀ A B : ReachedTriangle V, (dualGraph V).Adj A B →
      ∀ S U : Set ℂ, hasSide A.val.val S → hasSide B.val.val S →
        hasSide A.val.val U → hasSide B.val.val U → S = U)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b → IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (A B : ReachedTriangle V) (hAB : (dualGraph V).Adj A B) :
    reachedEdgePerm V hstepAdj A B * reachedEdgePerm V hstepAdj B A = 1 := by
  obtain ⟨p,hpA,q,hqA,hpq,hpB,hqB,_⟩ :=
    reached_adjacent_crossing_endpoints V A B hstepAdj hAB
  rw [reachedEdgePerm_eq V hstepAdj hsideUnique hreflection A B hAB hpA hqA hpq hpB hqB,
    reachedEdgePerm_eq V hstepAdj hsideUnique hreflection B A hAB.symm hpB hqB hpq hpA hqA]
  exact reflectionCrossingPerm_mul_self p q (A.val.property.2 p hpA) (A.val.property.2 q hqA) hpq

/-- The geometric reflection and target conjugation accumulated along a physical triangle path depend only on its endpoints. -/
theorem reached_transport_path_independent
    (V : VertexTriple)
    (hstepAdj : ∀ A B : ReachedTriangle V,
      reflectionStep A.val.val B.val.val ↔ (dualGraph V).Adj A B)
    (hsideUnique : ∀ A B : ReachedTriangle V, (dualGraph V).Adj A B →
      ∀ S U : Set ℂ, hasSide A.val.val S → hasSide B.val.val S →
        hasSide A.val.val U → hasSide B.val.val U → S = U)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b → IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (hTree : (dualGraph V).IsTree)
    {A B : ReachedTriangle V} (u v : (dualGraph V).Walk A B) :
    treeWalkProduct (reachedEdgePerm V hstepAdj) u =
      treeWalkProduct (reachedEdgePerm V hstepAdj) v := by
  exact treeWalkProduct_eq hTree.2 (reachedEdgePerm V hstepAdj)
    (reachedEdgePerm_reverse V hstepAdj hsideUnique hreflection) u v

end HolomorphicAnosov

noncomputable section
namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- The physical triangle reached by a literal original-side word. -/
def MarkedIdealDiskTriangle.wordTriangle (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) : ReachedTriangle T.vertexTriple :=
  ⟨⟨(Finset.univ.image T.vertex).image (T.itineraryMap w),
    reachable_three_vertices T.vertexTriple (T.itinerary_vertices_reachable w),
    reachable_unit_vertices T.vertexTriple.property.2 (T.itinerary_vertices_reachable w)⟩,
    T.itinerary_vertices_reachable w⟩

/-- A transported marked vertex is one of the actual word triangle's vertices. -/
theorem MarkedIdealDiskTriangle.wordTriangle_mem (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) (i : Fin 3) : T.itineraryMap w (T.vertex i) ∈ (T.wordTriangle w).val.val := by
  classical
  exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- Appending a generator crosses the corresponding transported physical side. -/
theorem MarkedIdealDiskTriangle.wordTriangle_append_vertices
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    (T.wordTriangle (w ++ [i])).val.val = reflectedVertices (T.wordTriangle w).val.val
      (T.itineraryMap w (T.vertex i)) (T.itineraryMap w (T.vertex (i + 1))) := by
  classical
  change (Finset.univ.image T.vertex).image (T.itineraryMap (w ++ [i])) =
    ((Finset.univ.image T.vertex).image (T.itineraryMap w)).image _
  simp only [Finset.image_image]
  apply Finset.image_congr
  intro j _
  dsimp only [Function.comp_apply]
  rw [T.itineraryMap_append, T.itineraryMap_cons]
  change T.itineraryMap w (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1))
    (T.vertex j)) = _
  exact (itineraryMap_reflection_covariance T w (T.norm_vertex i) (T.norm_vertex (i + 1))
    (T.vertex_ne_next i) (T.norm_vertex j).le).symm

/-- The two vertices of the transported side are distinct. -/
theorem MarkedIdealDiskTriangle.wordTriangle_side_ne
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    T.itineraryMap w (T.vertex i) ≠ T.itineraryMap w (T.vertex (i + 1)) := by
  intro h
  exact T.vertex_ne_next i (itineraryMap_injOn_closedDisk w
    (T.norm_vertex i).le (T.norm_vertex (i + 1)).le h)

/-- Consecutive word triangles are related by a physical reflection step. -/
theorem MarkedIdealDiskTriangle.wordTriangle_append_step
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    reflectionStep (T.wordTriangle w).val.val (T.wordTriangle (w ++ [i])).val.val :=
  ⟨_,T.wordTriangle_mem w i,_,T.wordTriangle_mem w (i + 1),
    T.wordTriangle_side_ne w i,T.wordTriangle_append_vertices w i⟩

/-- Reverse words invert the literal map on the closed disk, including ideal vertices. -/
theorem MarkedIdealDiskTriangle.itineraryMap_reverse_apply_closed
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    T.itineraryMap w.reverse (T.itineraryMap w z) = z := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.reverse_cons, T.itineraryMap_append, T.itineraryMap_cons, T.itineraryMap_cons]
    change T.itineraryMap w.reverse
      (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1))
        (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1))
          (T.itineraryMap w z))) = z
    rw [reflection_involutive_closed
      (T.norm_vertex i) (T.norm_vertex (i + 1)) (T.vertex_ne_next i)
      (itineraryMap_closedDisk w hz)]
    exact ih

/-- The disk permutation induced by a complete reflection word. -/
def MarkedIdealDiskTriangle.wordDiskPerm (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) : Equiv.Perm closedReflectionDisk where
  toFun z := ⟨T.itineraryMap w z, itineraryMap_closedDisk w z.property⟩
  invFun z := ⟨T.itineraryMap w.reverse z,
    itineraryMap_closedDisk w.reverse z.property⟩
  left_inv z := Subtype.ext (T.itineraryMap_reverse_apply_closed w z.property)
  right_inv z := Subtype.ext (by
    simpa only [List.reverse_reverse] using T.itineraryMap_reverse_apply_closed w.reverse z.property)

/-- The geometric word map together with its exact target conjugation. -/
def MarkedIdealDiskTriangle.wordCrossingPerm (T : MarkedIdealDiskTriangle)
    (w : List (Fin 3)) : Equiv.Perm closedReflectionDisk × Equiv.Perm ℂ :=
  (T.wordDiskPerm w, Complex.conjCLE.toEquiv ^ w.length)

/-- Physical crossing of the last side updates the entire word transport. -/
theorem MarkedIdealDiskTriangle.wordCrossingPerm_append
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    reflectionCrossingPerm (T.itineraryMap w (T.vertex i))
      (T.itineraryMap w (T.vertex (i + 1)))
      (itineraryMap_unitCircle w (T.norm_vertex i))
      (itineraryMap_unitCircle w (T.norm_vertex (i + 1)))
      (T.wordTriangle_side_ne w i) * T.wordCrossingPerm w =
        T.wordCrossingPerm (w ++ [i]) := by
  apply Prod.ext
  · apply Equiv.ext
    intro z
    apply Subtype.ext
    change idealDiskSideReflection (T.itineraryMap w (T.vertex i))
      (T.itineraryMap w (T.vertex (i + 1))) (T.itineraryMap w z) = T.itineraryMap (w ++ [i]) z
    rw [itineraryMap_reflection_covariance T w (T.norm_vertex i)
      (T.norm_vertex (i + 1)) (T.vertex_ne_next i) z.property,
      T.itineraryMap_append, T.itineraryMap_cons]
    rfl
  · change Complex.conjCLE.toEquiv * Complex.conjCLE.toEquiv ^ w.length =
      Complex.conjCLE.toEquiv ^ (w ++ [i]).length
    rw [List.length_append, List.length_singleton, pow_succ']

end HolomorphicAnosov

namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- The edge product is unchanged when the endpoints of a walk are copied. -/
theorem treeWalkProduct_copy {V A : Type*} [Group A] {G : SimpleGraph V}
    (e : V → V → A) {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') : treeWalkProduct e (p.copy hu hv) = treeWalkProduct e p := by
  subst u'
  subst v'
  rfl

/-- The shared side's two endpoints are retained by the next word triangle. -/
theorem MarkedIdealDiskTriangle.wordTriangle_append_side_mem
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) (i : Fin 3) :
    T.itineraryMap w (T.vertex i) ∈ (T.wordTriangle (w ++ [i])).val.val ∧
      T.itineraryMap w (T.vertex (i + 1)) ∈ (T.wordTriangle (w ++ [i])).val.val := by
  classical
  rw [T.wordTriangle_append_vertices]
  have hfix := idealDiskSideReflection_endpoints
    (itineraryMap_unitCircle w (T.norm_vertex i))
    (itineraryMap_unitCircle w (T.norm_vertex (i + 1))) (T.wordTriangle_side_ne w i)
  exact ⟨Finset.mem_image.mpr ⟨_,T.wordTriangle_mem w i,hfix.1⟩,
    Finset.mem_image.mpr ⟨_,T.wordTriangle_mem w (i + 1),hfix.2⟩⟩

/-- Every literal generator word is realized by a reversed physical walk whose edge product is precisely its disk transport and target conjugation. -/
theorem MarkedIdealDiskTriangle.wordCrossingPerm_realized
    (T : MarkedIdealDiskTriangle)
    (hstepAdj : ∀ A B : ReachedTriangle T.vertexTriple,
      reflectionStep A.val.val B.val.val ↔ (dualGraph T.vertexTriple).Adj A B)
    (hsideUnique : ∀ A B : ReachedTriangle T.vertexTriple, (dualGraph T.vertexTriple).Adj A B →
      ∀ S U : Set ℂ, hasSide A.val.val S → hasSide B.val.val S →
        hasSide A.val.val U → hasSide B.val.val U → S = U)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b → IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (w : List (Fin 3)) :
    ∃ P : (dualGraph T.vertexTriple).Walk (T.wordTriangle w) (T.wordTriangle []),
      treeWalkProduct (reachedEdgePerm T.vertexTriple hstepAdj) P = T.wordCrossingPerm w := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨.nil, ?_⟩
      apply Prod.ext
      · apply Equiv.ext
        intro z
        rfl
      · rfl
  | append_singleton w i ih =>
      obtain ⟨P,hP⟩ := ih
      have hAB := (hstepAdj (T.wordTriangle w) (T.wordTriangle (w ++ [i]))).mp
        (T.wordTriangle_append_step w i)
      have hmem := T.wordTriangle_append_side_mem w i
      refine ⟨.cons hAB.symm P, ?_⟩
      rw [treeWalkProduct, hP,
        reachedEdgePerm_eq T.vertexTriple hstepAdj hsideUnique hreflection
          (T.wordTriangle (w ++ [i])) (T.wordTriangle w) hAB.symm
          hmem.1 hmem.2 (T.wordTriangle_side_ne w i)
          (T.wordTriangle_mem w i) (T.wordTriangle_mem w (i + 1))]
      exact T.wordCrossingPerm_append w i

/-- Words that reach the same physical triangle induce the same disk map and the same target conjugation. -/
theorem MarkedIdealDiskTriangle.wordCrossingPerm_eq_of_triangle_eq
    (T : MarkedIdealDiskTriangle)
    (hstepAdj : ∀ A B : ReachedTriangle T.vertexTriple,
      reflectionStep A.val.val B.val.val ↔ (dualGraph T.vertexTriple).Adj A B)
    (hsideUnique : ∀ A B : ReachedTriangle T.vertexTriple, (dualGraph T.vertexTriple).Adj A B →
      ∀ S U : Set ℂ, hasSide A.val.val S → hasSide B.val.val S →
        hasSide A.val.val U → hasSide B.val.val U → S = U)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b → IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (hTree : (dualGraph T.vertexTriple).IsTree)
    (u v : List (Fin 3)) (he : T.wordTriangle u = T.wordTriangle v) :
    T.wordCrossingPerm u = T.wordCrossingPerm v := by
  obtain ⟨P,hP⟩ := T.wordCrossingPerm_realized hstepAdj hsideUnique hreflection u
  obtain ⟨Q,hQ⟩ := T.wordCrossingPerm_realized hstepAdj hsideUnique hreflection v
  have h := reached_transport_path_independent T.vertexTriple hstepAdj hsideUnique hreflection
    hTree (P.copy he rfl) Q
  rw [treeWalkProduct_copy, hP, hQ] at h
  exact h

/-- Literal itinerary chart independence on a physical tile. -/
theorem MarkedIdealDiskTriangle.itineraryChart_eqOn_of_triangle_eq
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFD : F.source ⊆ {z : ℂ | ‖z‖ < 1})
    (hstepAdj : ∀ A B : ReachedTriangle T.vertexTriple,
      reflectionStep A.val.val B.val.val ↔ (dualGraph T.vertexTriple).Adj A B)
    (hsideUnique : ∀ A B : ReachedTriangle T.vertexTriple, (dualGraph T.vertexTriple).Adj A B →
      ∀ S U : Set ℂ, hasSide A.val.val S → hasSide B.val.val S →
        hasSide A.val.val U → hasSide B.val.val U → S = U)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b → IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (hTree : (dualGraph T.vertexTriple).IsTree)
    (u v : List (Fin 3)) (he : T.wordTriangle u = T.wordTriangle v) :
    (T.itineraryChart F u).source = (T.itineraryChart F v).source ∧
      Set.EqOn (T.itineraryChart F u) (T.itineraryChart F v) (T.itineraryChart F u).source := by
  have h := T.wordCrossingPerm_eq_of_triangle_eq hstepAdj hsideUnique hreflection hTree u v he
  apply T.itineraryChart_eqOn_of_transport_eq F hFD u v
  · intro z hz
    have hh := Equiv.congr_fun (congrArg Prod.fst h) (⟨z,show ‖z‖ ≤ 1 from (hFD hz).le⟩ : closedReflectionDisk)
    exact congrArg Subtype.val hh
  · exact congrArg (fun e : Equiv.Perm ℂ ↦ (e : ℂ → ℂ)) (congrArg Prod.snd h)

end HolomorphicAnosov

namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- Unique shared sides in the tiling identify the side sets of any two actual representations of the same adjacent edge. -/
theorem reached_side_unique_from_tiling (V : VertexTriple)
    (A B : ReachedTriangle V) (hAB : (dualGraph V).Adj A B)
    (S U : Set ℂ) (hAS : hasSide A.val.val S) (hBS : hasSide B.val.val S)
    (hAU : hasSide A.val.val U) (hBU : hasSide B.val.val U) : S = U := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hunique,_,_,_⟩ := reflection_tiling V
  obtain ⟨R,hR,hRuniq⟩ := hunique A B hAB
  let s : ReachedSide V := ⟨S,A,hAS⟩
  let u : ReachedSide V := ⟨U,A,hAU⟩
  have hs : s = R := hRuniq s ⟨hAS,hBS⟩
  have hu : u = R := hRuniq u ⟨hAU,hBU⟩
  exact congrArg Subtype.val (hs.trans hu.symm)

/-- The actual reflection tiling makes the complete closed-disk transport and conjugation independent of the word representing a physical triangle. -/
theorem MarkedIdealDiskTriangle.word_transport_unique
    (T : MarkedIdealDiskTriangle)
    (hreflection : ∀ {p q a b : ℂ}, ‖p‖ = 1 → ‖q‖ = 1 → p ≠ q →
      ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
        IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a b →
        idealDiskSideReflection p q = idealDiskSideReflection a b)
    (u v : List (Fin 3))
    (he : (T.wordTriangle u).val.val = (T.wordTriangle v).val.val) :
    Set.EqOn (T.itineraryMap u) (T.itineraryMap v) {z : ℂ | ‖z‖ ≤ 1} ∧
      (conj^[u.length] : ℂ → ℂ) = conj^[v.length] := by
  obtain ⟨_,_,_,_,_,_,_,_,hTree,_,_,hstep,_,_⟩ := reflection_tiling T.vertexTriple
  have h := T.wordCrossingPerm_eq_of_triangle_eq hstep
    (reached_side_unique_from_tiling T.vertexTriple) hreflection hTree u v
    (Subtype.ext (Subtype.ext he))
  refine ⟨?_, congrArg (fun e : Equiv.Perm ℂ ↦ (e : ℂ → ℂ)) (congrArg Prod.snd h)⟩
  intro z hz
  exact congrArg Subtype.val (Equiv.congr_fun (congrArg Prod.fst h)
    (⟨z,hz⟩ : closedReflectionDisk))

end HolomorphicAnosov


namespace HolomorphicAnosov
open IdealDiskTriangle

/-- The native half-space triangle has exactly the same carrier as the marked Klein triangle inside the open disk. -/
theorem MarkedIdealDiskTriangle.native_triangle_eq
    (T : MarkedIdealDiskTriangle) :
    triangle T.vertexTriple.val = T.closedSet ∩ disk := by
  classical
  let B := T.affineBasis
  have hv (i : Fin 3) : T.vertex i ∈ T.vertexTriple.val :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hnorm (i : Fin 3) : ‖B i‖ = 1 := T.norm_vertex i
  ext z
  constructor
  · intro hz
    refine ⟨⟨hz.1.le, ?_⟩, hz.1⟩
    change idealDiskKlein z ∈ convexHull ℝ (Set.range B)
    rw [B.convexHull_eq_nonneg_coord]
    intro k
    have cond (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
        0 ≤ B.coord k (idealDiskKlein z) := by
      apply (sideEquation_mul_nonneg_iff_coord B i j k hij hjk hki
        (hnorm i) (hnorm j) (hnorm k) z).mp
      exact hz.2 (T.vertex i) (hv i) (T.vertex j) (hv j) (T.vertex k) (hv k)
        (T.distinct.ne hij) (T.distinct.ne hjk) (T.distinct.ne hki)
    fin_cases k
    · exact cond 1 2 0 (by decide) (by decide) (by decide)
    · exact cond 0 2 1 (by decide) (by decide) (by decide)
    · exact cond 0 1 2 (by decide) (by decide) (by decide)
  · rintro ⟨hz, hzd⟩
    refine ⟨hzd, ?_⟩
    intro p hp q hq r hr hpq hqr hrp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
    have hij : i ≠ j := fun he ↦ hpq (congrArg T.vertex he)
    have hjk : j ≠ k := fun he ↦ hqr (congrArg T.vertex he)
    have hki : k ≠ i := fun he ↦ hrp (congrArg T.vertex he)
    apply (sideEquation_mul_nonneg_iff_coord B i j k hij hjk hki
      (hnorm i) (hnorm j) (hnorm k) z).mpr
    have hm : idealDiskKlein z ∈ convexHull ℝ (Set.range B) := hz.2
    rw [B.convexHull_eq_nonneg_coord] at hm
    exact hm k

/-- The explicit inverse Klein map preserves the open disk. -/
theorem idealDiskKleinInv_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    ‖idealDiskKleinInv w‖ < 1 := by
  have hd : 0 < 1 + Real.sqrt (1 - ‖w‖ ^ 2) := by positivity
  have he : (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
      ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by norm_num
  rw [idealDiskKleinInv, norm_div, he, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hd, div_lt_one hd]
  linarith [Real.sqrt_nonneg (1 - ‖w‖ ^ 2)]

/-- Klein coordinates form an explicit partial homeomorphism of the open disk. -/
def idealDiskKleinPartial : OpenPartialHomeomorph ℂ ℂ where
  toFun := idealDiskKlein
  invFun := idealDiskKleinInv
  source := disk
  target := disk
  map_source' _ hz := idealDiskKlein_norm_lt_one hz
  map_target' _ hz := idealDiskKleinInv_norm_lt_one hz
  left_inv' _ hz := idealDiskKleinInv_left hz
  right_inv' _ hz := idealDiskKlein_right_inverse hz
  open_source := isOpen_lt continuous_norm continuous_const
  open_target := isOpen_lt continuous_norm continuous_const
  continuousOn_toFun := by
    apply Continuous.continuousOn
    unfold idealDiskKlein
    apply Continuous.div₀ (by fun_prop) (by fun_prop)
    intro z
    exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + ‖z‖ ^ 2))
  continuousOn_invFun := by
    apply Continuous.continuousOn
    unfold idealDiskKleinInv
    apply Continuous.div₀ continuous_id (by fun_prop)
    intro z
    exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - ‖z‖ ^ 2)))

/-- The native tiling interior is the literal marked interior. -/
theorem MarkedIdealDiskTriangle.native_openTriangle_eq
    (T : MarkedIdealDiskTriangle) :
    openTriangle T.vertexTriple.val = T.interiorSet := by
  have hc : triangle T.vertexTriple.val =
      disk ∩ idealDiskKlein ⁻¹' convexHull ℝ (Set.range T.vertex) := by
    rw [T.native_triangle_eq]
    ext z
    constructor
    · rintro ⟨⟨_, hz⟩, hzd⟩
      exact ⟨hzd, hz⟩
    · rintro ⟨hzd, hz⟩
      exact ⟨⟨hzd.le, hz⟩, hzd⟩
  rw [openTriangle, hc]
  change interior (idealDiskKleinPartial.source ∩
    idealDiskKleinPartial ⁻¹' convexHull ℝ (Set.range T.vertex)) = T.interiorSet
  rw [interior_inter]
  rw [idealDiskKleinPartial.open_source.interior_eq]
  exact (idealDiskKleinPartial.preimage_interior (convexHull ℝ (Set.range T.vertex))).symm

end HolomorphicAnosov
namespace HolomorphicAnosov
open IdealDiskTriangle Set
open scoped ComplexConjugate

/-- An arbitrary circular reflection carries the complete geodesic with endpoints a,b onto the complete geodesic with the reflected endpoints. -/
theorem reflection_openSide_image {p q a b : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    idealDiskSideReflection p q '' IdealDiskTriangle.openSide a b =
      IdealDiskTriangle.openSide (idealDiskSideReflection p q a) (idealDiskSideReflection p q b) := by
  let r := idealDiskSideReflection p q
  have hra := IdealDiskTriangle.reflection_unit hp hq hpq ha
  have hrb := IdealDiskTriangle.reflection_unit hp hq hpq hb
  have hrab : r a ≠ r b := fun he ↦ hab (IdealDiskTriangle.reflection_inj_closed hp hq hpq ha.le hb.le he)
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hrd := idealDiskSideReflection_mem_disk_g6 hp hq hpq hw.1
    refine ⟨hrd, (idealDiskSideReflection_fixed_iff_sideEquation hra hrb hrab hrd).mp ?_⟩
    rw [reflection_covariance hp hq hpq ha hb hab hw.1.le,
      IdealDiskTriangle.idealDiskSideReflection_fixed_openSide ha hb hab hw]
  · intro hz
    have hrd := idealDiskSideReflection_mem_disk_g6 hp hq hpq hz.1
    refine ⟨r z, ⟨hrd, ?_⟩, reflection_involutive_closed hp hq hpq hz.1.le⟩
    apply (idealDiskSideReflection_fixed_iff_sideEquation ha hb hab hrd).mp
    apply IdealDiskTriangle.reflection_inj_closed hp hq hpq
      (idealDiskSideReflection_mem_disk_g6 ha hb hab hrd).le hrd.le
    have hh := reflection_covariance hp hq hpq ha hb hab hrd.le
    rw [reflection_involutive_closed hp hq hpq hz.1.le,
      IdealDiskTriangle.idealDiskSideReflection_fixed_openSide hra hrb hrab hz] at hh
    exact hh.symm.trans (reflection_involutive_closed hp hq hpq hz.1.le).symm

end HolomorphicAnosov
