import HolomorphicAnosov.Topology.GallierXuFaceTriangleWitness
import HolomorphicAnosov.Topology.GallierXuOriginalTriangleDiskChartG6

noncomputable section
open Set Topology _root_.Topology Metric
namespace HolomorphicAnosov.Topology.GallierXu

/-- Injectivity of natural-number pairing identifies the increasing endpoints, so the native edge points agree.
Source: Gallier–Xu Proposition 3.2 p.31 and Lee Proposition 6.14 p.173. -/
lemma originalEdgePoint_of_label_eq {N : ℕ} {a b u v : Fin N}
    (h : edgeLabel a b = edgeLabel u v) (t : ℝ) :
    originalEdgePoint a b t = originalEdgePoint u v t := by
  have hp := Nat.pair_eq_pair.mp h
  have hmin : min a b = min u v := Fin.ext hp.1
  have hmax : max a b = max u v := Fin.ext hp.2
  simp only [originalEdgePoint, hmin, hmax]

/-- For increasing endpoints the cyclic parameter is unchanged; for decreasing endpoints replace it by one minus itself and swap the two affine terms.
Source: Gallier–Xu Proposition 3.2 p.31 and Lee Proposition 6.14 p.173. -/
lemma oriented_originalEdgePoint {N : ℕ} (a b : Fin N) (t : ℝ) :
    let τ := if decide (a < b) then t else 1-t
    (1-τ) • Pi.single a (1 : ℝ) + τ • Pi.single b 1 = originalEdgePoint a b t := by
  by_cases h : a < b
  · simp [h, originalEdgePoint, min_eq_left h.le, max_eq_right h.le]
  · simp [h, originalEdgePoint, min_eq_right (le_of_not_gt h),
      max_eq_left (le_of_not_gt h), add_comm]

/-- The actual list occurrence retains its original triangle, independently of
whether different words happen to agree. -/
def presentationTriangle {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (f : Fin (trianglePresentation K o).length) : Triangle K :=
  let a := (simplices K 2).attach.toList.get
    ⟨f.val, by simpa [trianglePresentation] using f.isLt⟩
  ⟨a.val, by simpa [simplices] using a.property⟩

/-- Reading the same index before and after the list map recovers the original triangle word.
Source: Gallier–Xu Proposition 3.2 p.31 and Lee Proposition 6.14 p.173. -/
lemma presentationTriangle_word {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (f : Fin (trianglePresentation K o).length) :
    triangleWord (presentationTriangle K o f) (o (presentationTriangle K o f)) =
      (trianglePresentation K o).get f := by
  change _ = (trianglePresentation K o)[f.val]
  simp only [trianglePresentation, List.getElem_map]
  rfl

/-- Each original triangle belongs to the attached finite triangle list and hence has an original presentation index.
Source: Gallier–Xu Proposition 3.2 p.31 and Lee Proposition 6.14 p.173. -/
lemma presentationTriangle_surjective {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) :
    Function.Surjective (presentationTriangle K o) := by
  intro s
  let a : {s // s ∈ simplices K 2} := ⟨s.val, by simpa [simplices] using s.property⟩
  have ha : a ∈ (simplices K 2).attach.toList := by simp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  let f : Fin (trianglePresentation K o).length :=
    ⟨i.val, by simpa [trianglePresentation] using i.isLt⟩
  refine ⟨f, ?_⟩
  apply Subtype.ext
  simpa only [presentationTriangle, f] using
    congrArg (fun z : {s // s ∈ simplices K 2} ↦ z.val) hi

/-- Read the cyclic side at its original list index, use the disk chart angle formula, reverse the parameter exactly for decreasing endpoints, and identify alternate endpoint labels by injectivity of pairing.
Source: Gallier–Xu Proposition 3.2 p.31 and Lee Proposition 6.14 p.173. -/
lemma original_triangle_chart_side {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (f : Fin (trianglePresentation K o).length)
    (q : C(Disk, carrier K))
    (hq : ∀ (i : Fin 3) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      (q ⟨Circle.exp (2*Real.pi*(i.val+t)/3),
        sphere_subset_closedBall (Circle.exp _).property⟩).val =
      (1-t) • Pi.single (o (presentationTriangle K o f) i).val 1 +
        t • Pi.single (o (presentationTriangle K o f) (finRotate 3 i)).val 1)
    (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hl : (((trianglePresentation K o).get f).get i).1 = edgeLabel u v) :
    (q (sidePointDisk f i t)).val = originalEdgePoint u v t := by
  let s := presentationTriangle K o f
  have hw := presentationTriangle_word K o f
  have hlen : ((trianglePresentation K o).get f).length = 3 := by
    rw [← hw]
    simp [triangleWord]
  let j : Fin 3 := ⟨i.val, hlen ▸ i.isLt⟩
  have hget : ((trianglePresentation K o).get f).get i =
      edgeDart (o s j).val (o s (finRotate 3 j)).val := by
    have hh := congrArg (fun l : Word ↦ l[i.val]?) hw
    have hleft : i.val < (triangleWord (presentationTriangle K o f)
        (o (presentationTriangle K o f))).length := by rw [hw]; exact i.isLt
    rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem i.isLt] at hh
    have he := Option.some.inj hh.symm
    simpa [triangleWord, List.get_eq_getElem, j, s] using he
  let τ : ℝ := if decide ((o s j).val < (o s (finRotate 3 j)).val) then t else 1-t
  have hτ : τ ∈ Icc (0 : ℝ) 1 := by
    dsimp [τ]
    split_ifs <;> constructor <;> linarith [ht.1,ht.2]
  have hp : sidePointDisk f i t =
      ⟨Circle.exp (2*Real.pi*(j.val+τ)/3), sphere_subset_closedBall (Circle.exp _).property⟩ := by
    apply Subtype.ext
    simp only [sidePointDisk, sidePoint, hget, hlen, edgeDart]
    rfl
  rw [hp, hq j τ hτ]
  exact (oriented_originalEdgePoint _ _ t).trans
    (originalEdgePoint_of_label_eq (by simpa only [hget, edgeDart] using hl) t)

/-- Purity gives an original triangle supporting every native carrier point.
This is the coverage step in the surjectivity argument of Lee Proposition 6.14,
p.173: enlarge the simplex supporting x to a triangle and keep its zero
coordinates outside the larger face. -/
lemma carrier_point_supported_triangle {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K)
    (x : ↥(carrier K)) :
    ∃ s : Triangle K, ∀ v ∉ s.val, (x : Fin N → ℝ) v = 0 := by
  obtain ⟨hx, s, hs, hxs⟩ := x.property
  obtain ⟨t, ht, hcard, hst⟩ := hpure s hs
  refine ⟨⟨t, ht, hcard⟩, ?_⟩
  intro v hv
  exact hxs v (fun hvs ↦ hv (hst hvs))

/-- Once every original triangle is covered by a face chart, the assembled map
is surjective. Apply carrier_point_supported_triangle, then the exact range
formula for that triangle. -/
lemma face_map_surjective_of_triangle_ranges {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hcover : ∀ s : Triangle K, ∃ f : Fin (trianglePresentation K o).length,
      {x : ↥(carrier K) | ∀ v ∉ s.val, (x : Fin N → ℝ) v = 0} ⊆
        Set.range (fun z : Disk ↦ q (f, z))) : Function.Surjective q := by
  intro x
  obtain ⟨s, hs⟩ := carrier_point_supported_triangle K hpure x
  obtain ⟨f, hf⟩ := hcover s
  obtain ⟨z, hz⟩ := hf hs
  exact ⟨(f, z), hz⟩

/-- Construct the original triangle face map with its prescribed side parameters.

Source: Gallier–Xu Proposition 3.2 and prescribed-boundary remark, p.31,
Note F.4 p.167; Lee Proposition 6.14 p.173 for the finite triangle coproduct.
For each face occurrence, extract its original triangle and cyclic order from
the two list maps. Its supported standard simplex is a closed affine triangle.
Parametrize its boundary by the three segments, assigning angle 2*pi*(i+t)/3
to the affine segment parameter t in cyclic order. The formulas agree at the
three corners. Closed-arc pasting gives a continuous circle map; injectivity
away from the shared corners and coverage make this a boundary homeomorphism.
Take any convex-body disk chart and adjust its boundary by the radial extension
of the discrepancy circle homeomorphism. Invert the adjusted chart to obtain
a disk-to-triangle homeomorphism with these exact boundary values. Compose
with the inclusion into the native carrier, separately on each original face.
Finite discrete coproduct continuity gives continuity of q. Purity puts every
carrier point in an original triangle, and the face charts are onto, proving
surjectivity. Injectivity and the exact supported image hold on each face by
its homeomorphism. For each side, edgeDart's sign reverses t precisely when
its cyclic endpoints are decreasing; hence the result is originalEdgePoint
with min/max endpoints. Injectivity of Nat.pair identifies the same unordered
endpoints for every alternate pair carrying that label. No link assumption
is needed for constructing this map. -/
theorem exists_triangle_face_map {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) :
    ∃ q : FaceDisks (trianglePresentation K o) → ↥(carrier K),
      Continuous q ∧ Function.Surjective q ∧
      (∀ f : Fin (trianglePresentation K o).length,
      Function.Injective (fun z : Disk ↦ q (f, z)) ∧
      ∃ s : Triangle K, triangleWord s (o s) = (trianglePresentation K o).get f ∧
        Set.range (fun z : Disk ↦ q (f, z)) =
          {x : ↥(carrier K) | ∀ v ∉ s.val, (x : Fin N → ℝ) v = 0}) ∧
      (∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t) := by
  classical
  choose chart hinj hrange hchart using fun f : Fin (trianglePresentation K o).length ↦
    original_triangle_disk_chart (presentationTriangle K o f) (o (presentationTriangle K o f))
  let q : FaceDisks (trianglePresentation K o) → carrier K := fun x ↦ chart x.1 x.2
  have hcontinuous : Continuous q := continuous_prod_of_discrete_left.mpr
    (fun f ↦ (chart f).continuous)
  have hcover : ∀ s : Triangle K, ∃ f : Fin (trianglePresentation K o).length,
      {x : carrier K | ∀ v ∉ s.val, (x : Fin N → ℝ) v = 0} ⊆
        Set.range (fun z : Disk ↦ q (f,z)) := by
    intro s
    obtain ⟨f, hf⟩ := presentationTriangle_surjective K o s
    refine ⟨f, ?_⟩
    change _ ⊆ Set.range (chart f)
    rw [hrange, hf]
  refine ⟨q, hcontinuous, face_map_surjective_of_triangle_ranges K hpure o q hcover, ?_, ?_⟩
  · intro f
    exact ⟨hinj f, presentationTriangle K o f, presentationTriangle_word K o f, hrange f⟩
  · intro f i u v t _ ht hl
    exact original_triangle_chart_side K o f (chart f) (hchart f) i u v t ht hl

end HolomorphicAnosov.Topology.GallierXu
