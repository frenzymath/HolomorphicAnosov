import HolomorphicAnosov.Topology.GallierXuCarrierCompact
import HolomorphicAnosov.Topology.FiniteSurfacePlanarFrontierG9
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
open Set
open scoped BigOperators
namespace HolomorphicAnosov.Topology.CairnsStrip

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The straight realization map retains the given geometric vertex positions. -/
def straightEval (p : Fin N → E) (x : Fin N → ℝ) : E := ∑ i, x i • p i

lemma sum_support (s : Finset (Fin N)) (x : Fin N → ℝ)
    (hx : ∀ i ∉ s, x i = 0) : ∑ i ∈ s, x i = ∑ i, x i := by
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi ↦ hx i hi)

lemma eval_support (p : Fin N → E) (s : Finset (Fin N)) (x : Fin N → ℝ)
    (hx : ∀ i ∉ s, x i = 0) : ∑ i ∈ s, x i • p i = straightEval p x := by
  apply Finset.sum_subset (Finset.subset_univ s)
  intro i _ hi
  rw [hx i hi, zero_smul]

/-- Barycentric weights supported on a face evaluate into its geometric hull. -/
theorem straightEval_mem_hull (p : Fin N → E) (s : Finset (Fin N))
    (x : Fin N → ℝ) (hx : x ∈ { f : Fin N → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 })
    (hs : ∀ i ∉ s, x i = 0) : straightEval p x ∈ convexHull ℝ (p '' (s : Set (Fin N))) := by
  apply mem_convexHull_of_exists_fintype (fun i : s ↦ x i) (fun i : s ↦ p i)
  · intro i
    exact hx.1 i
  · rw [Finset.sum_coe_sort, sum_support s x hs]
    exact hx.2
  · intro i
    exact ⟨i,i.property,rfl⟩
  · rw [Finset.sum_coe_sort s (fun i ↦ x i • p i)]
    exact eval_support p s x hs

/-- Every point of a finite geometric face has normalized nonnegative weights
on the original vertex indices. The injectivity assumption only identifies the
finite image sum with the original face sum. -/
theorem exists_weights_of_mem_hull (p : Fin N → E) (hp : Function.Injective p)
    (s : Finset (Fin N)) (z : E) (hz : z ∈ convexHull ℝ (p '' (s : Set (Fin N)))) :
    ∃ x : Fin N → ℝ, x ∈ { f : Fin N → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 } ∧
      (∀ i ∉ s, x i = 0) ∧ straightEval p x = z := by
  classical
  rw [← Finset.coe_image] at hz
  obtain ⟨w,hw0,hw1,hwz⟩ := Finset.mem_convexHull'.mp hz
  let x : Fin N → ℝ := fun i ↦ if i ∈ s then w (p i) else 0
  have hxzero : ∀ i ∉ s, x i = 0 := by intro i hi; simp [x,hi]
  have hsum : ∑ i, x i = 1 := by
    rw [← sum_support s x hxzero]
    calc
      ∑ i ∈ s, x i = ∑ i ∈ s, w (p i) := by apply Finset.sum_congr rfl; intro i hi; simp [x,hi]
      _ = ∑ j ∈ s.image p, w j := (Finset.sum_image (fun i _ j _ hij ↦ hp hij)).symm
      _ = 1 := hw1
  refine ⟨x,⟨?_,hsum⟩,hxzero,?_⟩
  · intro i
    by_cases hi : i ∈ s
    · simpa [x,hi] using hw0 (p i) (Finset.mem_image_of_mem p hi)
    · simp [x,hi]
  · rw [← eval_support p s x hxzero]
    calc
      ∑ i ∈ s, x i • p i = ∑ i ∈ s, w (p i) • p i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [x,hi]
      _ = ∑ j ∈ s.image p, w j • j := (Finset.sum_image (f := fun j ↦ w j • j) (fun i _ j _ hij ↦ hp hij)).symm
      _ = z := hwz

/-- Affine independence identifies the original coordinates of two supported
normalized barycentric vectors. -/
theorem straightEval_unique_on_face (p : Fin N → E) (s : Finset (Fin N))
    (hi : AffineIndependent ℝ (fun i : s ↦ p i))
    (x y : Fin N → ℝ) (hx : ∑ i, x i = 1) (hy : ∑ i, y i = 1)
    (hxs : ∀ i ∉ s, x i = 0) (hys : ∀ i ∉ s, y i = 0)
    (hxy : straightEval p x = straightEval p y) : x = y := by
  have hs : ∑ i : s, x i = ∑ i : s, y i := by
    rw [Finset.sum_coe_sort, Finset.sum_coe_sort, sum_support s x hxs, sum_support s y hys,hx,hy]
  have hv : ∑ i : s, x i • p i = ∑ i : s, y i • p i := by
    rw [Finset.sum_coe_sort s (fun i ↦ x i • p i), Finset.sum_coe_sort s (fun i ↦ y i • p i), eval_support p s x hxs, eval_support p s y hys]
    exact hxy
  have heq := hi.eq_of_sum_eq_sum hs hv
  funext i
  by_cases his : i ∈ s
  · exact heq ⟨i,his⟩ (Finset.mem_univ _)
  · rw [hxs i his,hys i his]

/-- A finite straight complex has a globally injective barycentric evaluation:
face intersections are precisely common geometric subfaces. -/
theorem straightEval_injective (K : AbstractSimplicialComplex (Fin N))
    (p : Fin N → E) (hp : Function.Injective p)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N)))) :
    Function.Injective (fun x : GallierXu.carrier K ↦ straightEval p x.val) := by
  intro x y hxy
  change straightEval p x.val = straightEval p y.val at hxy
  obtain ⟨s,hs,hxs⟩ := x.property.2
  obtain ⟨t,ht,hyt⟩ := y.property.2
  have hz : straightEval p x.val ∈ convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))) := by
    rw [← hinter s hs t ht]
    exact ⟨straightEval_mem_hull p s x.val x.property.1 hxs,
      by rw [hxy]; exact straightEval_mem_hull p t y.val y.property.1 hyt⟩
  obtain ⟨z,hz0,hzs,hzval⟩ := exists_weights_of_mem_hull p hp (s ∩ t) _ hz
  have hzs' : ∀ i ∉ s, z i = 0 := fun i his ↦ hzs i (by simp [his])
  have hzt' : ∀ i ∉ t, z i = 0 := fun i hit ↦ hzs i (by simp [hit])
  apply Subtype.ext
  exact (straightEval_unique_on_face p s (hi s hs) x.val z x.property.1.2 hz0.2 hxs hzs'
    hzval.symm).trans (straightEval_unique_on_face p t (hi t ht) z y.val hz0.2 y.property.1.2
      hzt' hyt (hzval.trans hxy))

/-- The barycentric evaluation is continuous in the original product topology. -/
lemma continuous_straightEval (p : Fin N → E) : Continuous (straightEval p) := by
  unfold straightEval
  exact continuous_finsetSum _ (fun i _ ↦ (continuous_apply i).smul continuous_const)

/-- The literal geometric realization of a finite straight simplicial complex
is homeomorphic to its standard barycentric carrier. The constructed map is
exactly the prescribed vertex interpolation. -/
theorem straightCarrier_homeomorph (K : AbstractSimplicialComplex (Fin N))
    (p : Fin N → E) (hp : Function.Injective p)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (A : Set E) (hA : A = ⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N)))) :
    ∃ H : GallierXu.carrier K ≃ₜ A, ∀ x, (H x).val = straightEval p x.val := by
  have hfA (x : GallierXu.carrier K) : straightEval p x.val ∈ A := by
    obtain ⟨s,hs,hxs⟩ := x.property.2
    rw [hA]
    exact mem_iUnion₂.mpr ⟨s,hs,straightEval_mem_hull p s x.val x.property.1 hxs⟩
  let f : GallierXu.carrier K → A := fun x ↦ ⟨straightEval p x.val,hfA x⟩
  have hf : Continuous f := ((continuous_straightEval p).comp continuous_subtype_val).subtype_mk _
  have hfinj : Function.Injective f := by
    intro x y hxy
    exact straightEval_injective K p hp hi hinter (congrArg Subtype.val hxy)
  have hfsurj : Function.Surjective f := by
    intro z
    have hz := z.property
    simp only [hA] at hz
    obtain ⟨s,hs,hzs⟩ := mem_iUnion₂.mp hz
    obtain ⟨x,hx,hxs,hxz⟩ := exists_weights_of_mem_hull p hp s z.val hzs
    exact ⟨⟨x,hx,s,hs,hxs⟩,Subtype.ext hxz⟩
  let : CompactSpace (GallierXu.carrier K) := isCompact_iff_compactSpace.mp (GallierXu.triangle_carrier_compact K)
  let e : GallierXu.carrier K ≃ A := Equiv.ofBijective f ⟨hfinj,hfsurj⟩
  have he : Continuous e := hf
  exact ⟨he.homeoOfEquivCompactToT2,fun _ ↦ rfl⟩

/-- Linear interpolation as a linear map, for exact segment transport. -/
def straightEvalLinear (p : Fin N → E) : (Fin N → ℝ) →ₗ[ℝ] E where
  toFun := straightEval p
  map_add' x y := by simp [straightEval,add_smul,Finset.sum_add_distrib]
  map_smul' r x := by simp [straightEval,Finset.smul_sum,smul_smul]

@[simp] lemma straightEval_single (p : Fin N → E) (i : Fin N) :
    straightEval p (Pi.single i 1) = p i := by
  classical
  simp [straightEval,Pi.single_apply]

/-- Standard edges evaluate onto the same straight geometric edges. -/
lemma straightEval_image_segment (p : Fin N → E) (i j : Fin N) :
    straightEval p '' segment ℝ (Pi.single i 1) (Pi.single j 1) = segment ℝ (p i) (p j) := by
  have h := image_segment ℝ (straightEvalLinear p).toAffineMap (Pi.single i 1) (Pi.single j 1)
  change straightEval p '' _ = segment ℝ (straightEval p _) (straightEval p _) at h
  simpa only [straightEval_single] using h

/-- Every point of an abstract edge is a point of the barycentric carrier. -/
lemma edge_segment_subset_carrier (K : AbstractSimplicialComplex (Fin N)) (i j : Fin N)
    (hij : ({i,j} : Finset (Fin N)) ∈ K.faces) :
    segment ℝ (Pi.single i 1) (Pi.single j 1) ⊆ GallierXu.carrier K := by
  have hconv : Convex ℝ {f : Fin N → ℝ | (∀ w, 0 ≤ f w) ∧ ∑ w, f w = 1} := by
    intro f hf g hg a b ha hb hab
    refine ⟨fun w ↦ add_nonneg (mul_nonneg ha (hf.1 w)) (mul_nonneg hb (hg.1 w)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]
  rintro x ⟨a,b,ha,hb,hab,rfl⟩
  refine ⟨hconv (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩)
    (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩) ha hb hab, {i,j}, hij, ?_⟩
  intro k hk
  have hki : k ≠ i := by intro h; exact hk (by simp [h])
  have hkj : k ≠ j := by intro h; exact hk (by simp [h])
  simp [hki,hkj]

/-- The barycentric cycle maps exactly onto its original geometric edge union. -/
theorem straightEval_cycleCarrier_image (K : AbstractSimplicialComplex (Fin N))
    (p : Fin N → E) (l : List (Fin N))
    (hl : ∀ i j, GallierXu.cycleEdge l i j → ({i,j} : Finset (Fin N)) ∈ K.faces) :
    (fun x : GallierXu.carrier K ↦ straightEval p x.val) '' GallierXu.cycleCarrier l =
      ⋃ i, ⋃ j, ⋃ (_ : GallierXu.cycleEdge l i j), segment ℝ (p i) (p j) := by
  apply subset_antisymm
  · rintro z ⟨x,⟨i,j,hij,hx⟩,rfl⟩
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hij,?_⟩⟩⟩
    rw [← straightEval_image_segment]
    exact ⟨x.val,hx,rfl⟩
  · intro z hz
    obtain ⟨i,hz⟩ := mem_iUnion.mp hz
    obtain ⟨j,hz⟩ := mem_iUnion.mp hz
    obtain ⟨hij,hz⟩ := mem_iUnion.mp hz
    rw [← straightEval_image_segment] at hz
    obtain ⟨x,hx,hxz⟩ := hz
    exact ⟨⟨x,edge_segment_subset_carrier K i j (hl i j hij) hx⟩,⟨i,j,hij,hx⟩,hxz⟩

/-- The concrete abstract complex generated by a finite family of triangles.
The cover condition keeps every vertex of `Fin N` as an actual vertex. -/
def triangleGeneratedComplex (T : Finset (Finset (Fin N)))
    (hcover : ∀ i : Fin N, ∃ t ∈ T, i ∈ t) : AbstractSimplicialComplex (Fin N) where
  faces := {s | s.Nonempty ∧ ∃ t ∈ T, s ⊆ t}
  isRelLowerSet_faces := by
    rintro s ⟨hs,t,ht,hst⟩
    refine ⟨hs,?_⟩
    intro u hus hu
    exact ⟨hu,t,ht,hus.trans hst⟩
  singleton_mem i := by
    obtain ⟨t,ht,hit⟩ := hcover i
    exact ⟨Finset.singleton_nonempty i,t,ht,Finset.singleton_subset_iff.mpr hit⟩

/-- Triangular generators make the whole generated complex pure of dimension two. -/
theorem triangleGeneratedComplex_pure (T : Finset (Finset (Fin N)))
    (hcover : ∀ i : Fin N, ∃ t ∈ T, i ∈ t) (hcard : ∀ t ∈ T, t.card = 3) :
    GallierXu.PureTwo (triangleGeneratedComplex T hcover) := by
  rintro s ⟨hs,t,ht,hst⟩
  refine ⟨t,⟨?_,t,ht,Finset.Subset.refl _⟩,hcard t ht,hst⟩
  exact Finset.card_pos.mp (by rw [hcard t ht]; omega)

/-- The two-simplices are exactly the original generators, with no duplicate
triangle instances introduced by face closure. -/
theorem triangleGeneratedComplex_triangles (T : Finset (Finset (Fin N)))
    (hcover : ∀ i : Fin N, ∃ t ∈ T, i ∈ t) (hcard : ∀ t ∈ T, t.card = 3) :
    GallierXu.simplices (triangleGeneratedComplex T hcover) 2 = T := by
  classical
  ext s
  simp only [GallierXu.simplices,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨hs,t,ht,hst⟩,hsc⟩
    have heq : s = t := Finset.eq_of_subset_of_card_le hst (by rw [hsc,hcard t ht])
    exact heq ▸ ht
  · intro hs
    refine ⟨⟨?_,s,hs,Finset.Subset.refl _⟩,hcard s hs⟩
    exact Finset.card_pos.mp (by rw [hcard s hs]; omega)

/-- Taking face closure does not change the union of geometric triangles. -/
theorem triangleGeneratedComplex_hull_union (T : Finset (Finset (Fin N)))
    (hcover : ∀ i : Fin N, ∃ t ∈ T, i ∈ t) (hne : ∀ t ∈ T, t.Nonempty)
    (p : Fin N → E) :
    (⋃ s ∈ (triangleGeneratedComplex T hcover).faces,
      convexHull ℝ (p '' (s : Set (Fin N)))) =
        ⋃ t ∈ T, convexHull ℝ (p '' (t : Set (Fin N))) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨s,⟨hs,t,ht,hst⟩,hx⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨t,ht,?_⟩
    exact convexHull_mono (Set.image_mono hst) hx
  · intro x hx
    obtain ⟨t,ht,hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨t,⟨hne t ht,t,ht,Finset.Subset.refl _⟩,hx⟩

/-- Affine independence passes from each triangular generator to every face. -/
theorem triangleGeneratedComplex_independent (T : Finset (Finset (Fin N)))
    (hcover : ∀ i : Fin N, ∃ t ∈ T, i ∈ t) (p : Fin N → E)
    (hi : ∀ t ∈ T, AffineIndependent ℝ (fun i : t ↦ p i)) :
    ∀ s ∈ (triangleGeneratedComplex T hcover).faces,
      AffineIndependent ℝ (fun i : s ↦ p i) := by
  rintro s ⟨hs,t,ht,hst⟩
  let f : s ↪ t := ⟨fun i ↦ ⟨i.val,hst i.property⟩,
    fun i j hij ↦ Subtype.ext (congrArg (fun v : t ↦ v.val) hij)⟩
  exact (hi t ht).comp_embedding f

/-- Checking geometric intersections on the generating triangles suffices for
all of their faces. Uniqueness of weights forces the shared point to be
supported on the intersection of the two smaller faces. -/
theorem triangleGeneratedComplex_intersections (T : Finset (Finset (Fin N)))
    (hcover : ∀ i : Fin N, ∃ t ∈ T, i ∈ t) (p : Fin N → E)
    (hp : Function.Injective p)
    (hi : ∀ t ∈ T, AffineIndependent ℝ (fun i : t ↦ p i))
    (hinter : ∀ s ∈ T, ∀ t ∈ T,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N)))) :
    ∀ s ∈ (triangleGeneratedComplex T hcover).faces,
      ∀ t ∈ (triangleGeneratedComplex T hcover).faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))) := by
  rintro s ⟨hs,u,hu,hsu⟩ t ⟨ht,v,hv,htv⟩
  apply subset_antisymm
  · rintro z ⟨hzs,hzt⟩
    have hz : z ∈ convexHull ℝ (p '' ((u ∩ v : Finset (Fin N)) : Set (Fin N))) := by
      rw [← hinter u hu v hv]
      exact ⟨convexHull_mono (Set.image_mono hsu) hzs,
        convexHull_mono (Set.image_mono htv) hzt⟩
    obtain ⟨x,hx,hxs,hxz⟩ := exists_weights_of_mem_hull p hp s z hzs
    obtain ⟨y,hy,hyt,hyz⟩ := exists_weights_of_mem_hull p hp t z hzt
    obtain ⟨w,hw,hwuv,hwz⟩ := exists_weights_of_mem_hull p hp (u ∩ v) z hz
    have hxu : ∀ i ∉ u, x i = 0 := fun i hi ↦ hxs i (fun his ↦ hi (hsu his))
    have hyv : ∀ i ∉ v, y i = 0 := fun i hi ↦ hyt i (fun hit ↦ hi (htv hit))
    have hwu : ∀ i ∉ u, w i = 0 := fun i hi ↦ hwuv i (by simp [hi])
    have hwv : ∀ i ∉ v, w i = 0 := fun i hi ↦ hwuv i (by simp [hi])
    have hxw := straightEval_unique_on_face p u (hi u hu) x w hx.2 hw.2 hxu hwu (hxz.trans hwz.symm)
    have hyw := straightEval_unique_on_face p v (hi v hv) y w hy.2 hw.2 hyv hwv (hyz.trans hwz.symm)
    have hxst : ∀ i ∉ s ∩ t, x i = 0 := by
      intro i hi
      by_cases his : i ∈ s
      · have hit : i ∉ t := by intro hit; exact hi (Finset.mem_inter.mpr ⟨his,hit⟩)
        rw [hxw,← hyw]
        exact hyt i hit
      · exact hxs i his
    rw [← hxz]
    exact straightEval_mem_hull p (s ∩ t) x hx hxst
  · intro z hz
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hz,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hz⟩


omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Enumerate exactly the geometric vertices of a finite triangle family. -/
theorem finiteTriangleFamily_enumeration {ι : Type*} [Finite ι] (v : ι → Fin 3 → E) :
    ∃ N : ℕ, ∃ p : Fin N → E, Function.Injective p ∧
      ∃ q : ι → Fin 3 → Fin N,
        (∀ s i, p (q s i) = v s i) ∧ (∀ j, ∃ s i, q s i = j) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let S : Finset E := Finset.univ.biUnion (fun s ↦ Finset.univ.image (v s))
  have hv (s : ι) (i : Fin 3) : v s i ∈ S := by
    exact Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let p : Fin (Fintype.card S) → E := fun i ↦ (e i).val
  let q : ι → Fin 3 → Fin (Fintype.card S) := fun s i ↦ e.symm ⟨v s i,hv s i⟩
  refine ⟨Fintype.card S,p,Subtype.val_injective.comp e.injective,q,?_,?_⟩
  · intro s i
    exact congrArg Subtype.val (e.apply_symm_apply ⟨v s i,hv s i⟩)
  · intro j
    obtain ⟨s,_,hs⟩ := Finset.mem_biUnion.mp (e j).property
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hs
    refine ⟨s,i,?_⟩
    apply e.injective
    change e (e.symm _) = e j
    rw [e.apply_symm_apply]
    exact Subtype.ext hi

/-- Every finite geometric triangle complex has an abstract pure two-dimensional
complex and a homeomorphism of its standard barycentric carrier onto its literal
geometric union. Vertex enumeration introduces no extra vertex. -/
theorem finiteTriangleFamily_realization {ι : Type*} [Finite ι] (v : ι → Fin 3 → E)
    (hi : ∀ s, AffineIndependent ℝ (v s))
    (hinter : ∀ s t, convexHull ℝ (range (v s)) ∩ convexHull ℝ (range (v t)) =
      convexHull ℝ (range (v s) ∩ range (v t))) :
    ∃ N : ℕ, ∃ K : AbstractSimplicialComplex (Fin N), ∃ p : Fin N → E,
      Function.Injective p ∧ GallierXu.PureTwo K ∧
      (∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i)) ∧
      (∀ s ∈ K.faces, ∀ t ∈ K.faces,
        convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
          convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N)))) ∧
      (⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N)))) =
        (⋃ s, convexHull ℝ (range (v s))) ∧
      ∃ H : GallierXu.carrier K ≃ₜ (⋃ s, convexHull ℝ (range (v s))),
        ∀ x, (H x).val = straightEval p x.val := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨N,p,hp,q,hq,hcover⟩ := finiteTriangleFamily_enumeration v
  have hqi (s : ι) : Function.Injective (q s) := by
    intro i j he
    apply (hi s).injective
    rw [← hq s i,← hq s j,he]
  let t : ι → Finset (Fin N) := fun s ↦ Finset.univ.image (q s)
  let T : Finset (Finset (Fin N)) := Finset.univ.image t
  have ht (s : ι) : p '' (t s : Set (Fin N)) = range (v s) := by
    ext y
    constructor
    · rintro ⟨j,hj,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i,(hq s i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨q s i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hq s i⟩
  have hcov : ∀ i : Fin N, ∃ a ∈ T, i ∈ a := by
    intro i
    obtain ⟨s,j,rfl⟩ := hcover i
    exact ⟨t s,Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  have hcard : ∀ a ∈ T, a.card = 3 := by
    intro a ha
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.card_image_of_injective _ (hqi s)).trans (by simp)
  have htind : ∀ a ∈ T, AffineIndependent ℝ (fun i : a ↦ p i) := by
    intro a ha
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp ha
    let e : t s ↪ range (v s) :=
      ⟨fun i ↦ ⟨p i,ht s ▸ mem_image_of_mem p i.property⟩,
        fun i j he ↦ Subtype.ext (hp (congrArg (fun x : range (v s) ↦ x.val) he))⟩
    exact (hi s).range.comp_embedding e
  have htinter : ∀ a ∈ T, ∀ b ∈ T,
      convexHull ℝ (p '' (a : Set (Fin N))) ∩ convexHull ℝ (p '' (b : Set (Fin N))) =
        convexHull ℝ (p '' ((a ∩ b : Finset (Fin N)) : Set (Fin N))) := by
    intro a ha b hb
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.coe_inter,Set.image_inter hp,ht,ht]
    exact hinter s u
  let K := triangleGeneratedComplex T hcov
  have hki := triangleGeneratedComplex_independent T hcov p htind
  have hkinter := triangleGeneratedComplex_intersections T hcov p hp htind htinter
  have hku : (⋃ a ∈ K.faces, convexHull ℝ (p '' (a : Set (Fin N)))) =
      ⋃ s, convexHull ℝ (range (v s)) := by
    rw [triangleGeneratedComplex_hull_union T hcov
      (fun a ha ↦ Finset.card_pos.mp (by rw [hcard a ha]; omega))]
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp ha
      exact mem_iUnion.mpr ⟨s,ht s ▸ hx⟩
    · intro hx
      obtain ⟨s,hs⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨t s,Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩,ht s ▸ hs⟩
  refine ⟨N,K,p,hp,triangleGeneratedComplex_pure T hcov hcard,hki,hkinter,hku,?_⟩
  exact straightCarrier_homeomorph K p hp hki hkinter _ hku.symm


lemma straightComplex_vertex_notMem_hull (K : AbstractSimplicialComplex (Fin N))
    (p : Fin N → E)
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (v : Fin N) (s : Finset (Fin N)) (hs : s ∈ K.faces) (hv : v ∉ s) :
    p v ∉ convexHull ℝ (p '' (s : Set (Fin N))) := by
  intro hx
  have hvertex : p v ∈ convexHull ℝ (p '' (({v} : Finset (Fin N)) : Set (Fin N))) :=
    subset_convexHull ℝ _ ⟨v,by simp,rfl⟩
  have hh := hinter {v} (K.singleton_mem v) s hs
  have hcommon : ({v} : Finset (Fin N)) ∩ s = ∅ := by simp [hv]
  have he : p v ∈ convexHull ℝ (p '' (({v} ∩ s : Finset (Fin N)) : Set (Fin N))) :=
    hh ▸ (show p v ∈ convexHull ℝ (p '' (({v} : Finset (Fin N)) : Set (Fin N))) ∩
      convexHull ℝ (p '' (s : Set (Fin N))) from ⟨hvertex,hx⟩)
  simp only [hcommon,Finset.coe_empty,image_empty,convexHull_empty,mem_empty_iff_false] at he

lemma linkReach_face_uniform (K : AbstractSimplicialComplex (Fin N))
    (v a : Fin N) (s : Finset (Fin N)) (hs : s ∈ K.faces) (hv : v ∈ s)
    (w z : Fin N) (hw : w ∈ s) (hz : z ∈ s) (hwv : w ≠ v) (hzv : z ≠ v) :
    Relation.ReflTransGen (GallierXu.linkEdge K v) a w ↔
      Relation.ReflTransGen (GallierXu.linkEdge K v) a z := by
  by_cases hwz : w = z
  · subst z
    rfl
  have ht : ({v,w,z} : Finset (Fin N)) ∈ K.faces := by
    apply (K.isRelLowerSet_faces hs).2 _ (by simp)
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hforward : GallierXu.linkEdge K v w z := ⟨hwz,hwv,hzv,ht⟩
  have hback : GallierXu.linkEdge K v z w :=
    ⟨Ne.symm hwz,hzv,hwv,by simpa only [Finset.pair_comm z w] using ht⟩
  exact ⟨fun h ↦ h.tail hforward,fun h ↦ h.tail hback⟩

/-- A connected punctured-neighborhood basis of a finite straight complex
forces every original simplicial link to be chain-connected. The proof uses
closed unions of faces from the two proposed link components. -/
theorem straightComplex_link_chainConnected
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → E) (hp : Function.Injective p)
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (A : Set E) (hA : A = ⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N))))
    (hlocal : ∀ v : Fin N, ∀ W : Set E, IsOpen W → p v ∈ W →
      ∃ U : Set E, IsOpen U ∧ p v ∈ U ∧ U ⊆ W ∧ IsPreconnected ((A ∩ U) \ {p v})) :
    ∀ v a b : Fin N,
      (a ≠ v ∧ ({v,a} : Finset (Fin N)) ∈ K.faces) →
      (b ≠ v ∧ ({v,b} : Finset (Fin N)) ∈ K.faces) →
      Relation.ReflTransGen (GallierXu.linkEdge K v) a b := by
  classical
  intro v a b ha hb
  by_contra hnot
  let reach : Fin N → Prop := Relation.ReflTransGen (GallierXu.linkEdge K v) a
  let geom (s : Finset (Fin N)) := convexHull ℝ (p '' (s : Set (Fin N)))
  have hgclosed (s : Finset (Fin N)) : IsClosed (geom s) :=
    (s.finite_toSet.image p).isClosed_convexHull ℝ
  let P := {s : Finset (Fin N) // s ∈ K.faces ∧ v ∈ s ∧ ∀ w ∈ s, w ≠ v → reach w}
  let M := {s : Finset (Fin N) // s ∈ K.faces ∧ v ∈ s ∧ ∀ w ∈ s, w ≠ v → ¬ reach w}
  let J := {s : Finset (Fin N) // s ∈ K.faces ∧ v ∉ s}
  let S : Set E := ⋃ s : P, geom s.val
  let T : Set E := ⋃ s : M, geom s.val
  let F : Set E := ⋃ s : J, geom s.val
  have hS : IsClosed S := isClosed_iUnion_of_finite (fun s ↦ hgclosed s.val)
  have hT : IsClosed T := isClosed_iUnion_of_finite (fun s ↦ hgclosed s.val)
  have hF : IsClosed F := isClosed_iUnion_of_finite (fun s ↦ hgclosed s.val)
  have hvF : p v ∉ F := by
    intro h
    obtain ⟨s,hs⟩ := mem_iUnion.mp h
    exact straightComplex_vertex_notMem_hull K p hinter v s.val s.property.1 s.property.2 hs
  have hpartition (s : Finset (Fin N)) (hs : s ∈ K.faces) (hv : v ∈ s) : geom s ⊆ S ∪ T := by
    by_cases hr : ∃ w ∈ s, w ≠ v ∧ reach w
    · obtain ⟨w,hw,hwv,hr⟩ := hr
      have hall : ∀ z ∈ s, z ≠ v → reach z := by
        intro z hz hzv
        exact (linkReach_face_uniform K v a s hs hv w z hw hz hwv hzv).mp hr
      exact fun x hx ↦ Or.inl (mem_iUnion.mpr ⟨⟨s,hs,hv,hall⟩,hx⟩)
    · have hall : ∀ z ∈ s, z ≠ v → ¬ reach z := by
        intro z hz hzv hrz
        exact hr ⟨z,hz,hzv,hrz⟩
      exact fun x hx ↦ Or.inr (mem_iUnion.mpr ⟨⟨s,hs,hv,hall⟩,hx⟩)
  have hST : S ∩ T ⊆ {p v} := by
    rintro x ⟨hxS,hxT⟩
    obtain ⟨s,hs⟩ := mem_iUnion.mp hxS
    obtain ⟨t,ht⟩ := mem_iUnion.mp hxT
    have hh := hinter s.val s.property.1 t.val t.property.1
    have hx : x ∈ convexHull ℝ (p '' ((s.val ∩ t.val : Finset (Fin N)) : Set (Fin N))) :=
      hh ▸ And.intro hs ht
    have hsub : p '' ((s.val ∩ t.val : Finset (Fin N)) : Set (Fin N)) ⊆ {p v} := by
      rintro y ⟨w,hw,rfl⟩
      by_cases he : w = v
      · simp [he]
      · exact False.elim (t.property.2.2 w (Finset.mem_inter.mp hw).2 he
          (s.property.2.2 w (Finset.mem_inter.mp hw).1 he))
    simpa only [convexHull_singleton] using convexHull_mono hsub hx
  obtain ⟨U,hU,hvU,hUF,hQ⟩ := hlocal v Fᶜ hF.isOpen_compl hvF
  have hQsub : (A ∩ U) \ {p v} ⊆ S ∪ T := by
    intro x hx
    have hxA := hx.1.1
    rw [hA] at hxA
    obtain ⟨s,hs,hxs⟩ := mem_iUnion₂.mp hxA
    have hv : v ∈ s := by
      by_contra hv
      exact hUF hx.1.2 (mem_iUnion.mpr ⟨⟨s,hs,hv⟩,hxs⟩)
    exact hpartition s hs hv hxs
  have hsegA (w : Fin N) (hw : ({v,w} : Finset (Fin N)) ∈ K.faces) :
      segment ℝ (p v) (p w) ⊆ A := by
    intro x hx
    rw [hA]
    apply mem_iUnion₂.mpr
    refine ⟨{v,w},hw,?_⟩
    simpa only [Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton,convexHull_pair] using hx
  have hsegS : segment ℝ (p v) (p a) ⊆ S := by
    have hs : ∀ w ∈ ({v,a} : Finset (Fin N)), w ≠ v → reach w := by
      intro w hw hne
      have he : w = a := Finset.mem_singleton.mp ((Finset.mem_insert.mp hw).resolve_left hne)
      subst w
      exact Relation.ReflTransGen.refl
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨{v,a},ha.2,by simp,hs⟩,?_⟩
    simpa only [geom,Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton,convexHull_pair] using hx
  have hsegT : segment ℝ (p v) (p b) ⊆ T := by
    have hs : ∀ w ∈ ({v,b} : Finset (Fin N)), w ≠ v → ¬ reach w := by
      intro w hw hne
      have he : w = b := Finset.mem_singleton.mp ((Finset.mem_insert.mp hw).resolve_left hne)
      subst w
      exact hnot
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨{v,b},hb.2,by simp,hs⟩,?_⟩
    simpa only [geom,Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton,convexHull_pair] using hx
  have hnear (w : Fin N) (hw : w ≠ v) :
      ∃ x, x ∈ U ∧ x ∈ segment ℝ (p v) (p w) ∧ x ≠ p v := by
    have hclosure : p v ∈ closure (openSegment ℝ (p v) (p w)) :=
      segment_subset_closure_openSegment (left_mem_segment ℝ _ _)
    obtain ⟨x,hxU,hxS⟩ := mem_closure_iff.mp hclosure U hU hvU
    refine ⟨x,hxU,openSegment_subset_segment ℝ _ _ hxS,?_⟩
    intro he
    subst x
    exact hw (hp ((left_mem_openSegment_iff.mp hxS).symm))
  have hQS : (((A ∩ U) \ {p v}) ∩ S).Nonempty := by
    obtain ⟨x,hxU,hxS,hxv⟩ := hnear a ha.1
    exact ⟨x,⟨⟨hsegA a ha.2 hxS,hxU⟩,by simpa using hxv⟩,hsegS hxS⟩
  have hQT : (((A ∩ U) \ {p v}) ∩ T).Nonempty := by
    obtain ⟨x,hxU,hxS,hxv⟩ := hnear b hb.1
    exact ⟨x,⟨⟨hsegA b hb.2 hxS,hxU⟩,by simpa using hxv⟩,hsegT hxS⟩
  obtain ⟨x,hxQ,hxST⟩ := isPreconnected_closed_iff.mp hQ S T hS hT hQsub hQS hQT
  exact hxQ.2 (hST hxST)


/-- The local disk and interval-fan charts put every point outside all original
boundary edges in the interior of a planar embedding. No prior boundary-cycle
enumeration is needed. -/
theorem surface_image_interior_of_not_boundary_edges {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (hpure : GallierXu.PureTwo K) (hlinks : GallierXu.SurfaceLinks K)
    (f : C(↥(GallierXu.carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f)
    (x : ↥(GallierXu.carrier K))
    (hx : ∀ u v, GallierXu.boundaryEdge K u v →
      x.val ∉ segment ℝ (Pi.single u 1) (Pi.single v 1)) :
    f x ∈ interior (range f) := by
  have hv : ∃ v, 0 < x.val v := by
    by_contra! h
    have hz : ∀ v, x.val v = 0 := fun v ↦ le_antisymm (h v) (x.property.1.1 v)
    have hh := x.property.1.2
    simp [hz] at hh
  obtain ⟨v,hv⟩ := hv
  obtain ⟨l,hnd,hvertices,hcircle | hpath⟩ := hlinks v
  · exact GallierXu.circularLink_image_interior_g9 K v hpure l hnd hcircle.1 hvertices
      hcircle.2 f hf x hv
  · have hfirst := GallierXu.intervalLink_first_boundaryEdge_g9 K v l hnd hpath.1 hpath.2
    have hlast := GallierXu.intervalLink_last_boundaryEdge_g9 K v l hnd hpath.1 hpath.2
    have hnotfirst : x.val ∉ segment ℝ
        (Pi.single (l.get ⟨0,by omega⟩) 1) (Pi.single v 1) := by
      rw [segment_symm]
      exact hx _ _ hfirst
    have hnotlast : x.val ∉ segment ℝ
        (Pi.single (l.get ⟨l.length-1,by omega⟩) 1) (Pi.single v 1) := by
      rw [segment_symm]
      exact hx _ _ hlast
    have hv1 : x.val v < 1 := by
      have hle := x.property.1.2 ▸ Finset.single_le_sum (fun w _ ↦ x.property.1.1 w)
        (Finset.mem_univ v)
      apply lt_of_le_of_ne hle
      intro hone
      apply hnotfirst
      rw [GallierXu.simplex_eq_single_of_coordinate_one_g9 x.val x.property.1 v hone]
      exact right_mem_segment ℝ _ _
    exact GallierXu.intervalLink_image_interior_g9 K v hpure l hnd hpath.1 hpath.2
      f hf x hv hv1 hnotfirst hnotlast

/-- The frontier of a finite embedded surface is covered by its original
one-triangle edges, before those edges have been ordered into cycles. -/
theorem surface_frontier_boundaryEdges_cover {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (hpure : GallierXu.PureTwo K) (hlinks : GallierXu.SurfaceLinks K)
    (f : C(↥(GallierXu.carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f) :
    ∀ y ∈ frontier (range f), ∃ u v, GallierXu.boundaryEdge K u v ∧
      ∃ x : ↥(GallierXu.carrier K),
        x.val ∈ segment ℝ (Pi.single u 1) (Pi.single v 1) ∧ f x = y := by
  let : CompactSpace ↥(GallierXu.carrier K) :=
    isCompact_iff_compactSpace.mp (GallierXu.triangle_carrier_compact K)
  have hc : IsClosed (range f) := (isCompact_range f.continuous).isClosed
  intro y hy
  have hym : y ∈ range f := hc.closure_eq ▸ frontier_subset_closure hy
  obtain ⟨x,rfl⟩ := hym
  by_contra hnot
  have hx : ∀ u v, GallierXu.boundaryEdge K u v →
      x.val ∉ segment ℝ (Pi.single u 1) (Pi.single v 1) := by
    intro u v h hseg
    exact hnot ⟨u,v,h,x,hseg,rfl⟩
  exact hy.2 (surface_image_interior_of_not_boundary_edges K hpure hlinks f hf x hx)


/-- A connected finite union of exact straight edges has a chain-connected
edge graph. A hypothetical graph-component partition would give a disjoint
closed separation of its geometric union. -/
theorem straightGraph_chainConnected
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → E)
    (hfaces : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (V : Finset (Fin N)) (R : Fin N → Fin N → Prop) (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hface : ∀ u v, R u v → ({u,v} : Finset (Fin N)) ∈ K.faces)
    (hneighbors : ∀ a ∈ V, ∃ b, R a b)
    (C : Set E) (hC : IsPreconnected C)
    (hcover : C = ⋃ u, ⋃ v, ⋃ (_ : R u v), segment ℝ (p u) (p v)) :
    ∀ a ∈ V, ∀ b ∈ V, Relation.ReflTransGen R a b := by
  classical
  intro a ha b hb
  by_contra hnot
  let reach := Relation.ReflTransGen R a
  have hedge (u v : Fin N) (h : R u v) : reach u ↔ reach v :=
    ⟨fun hu ↦ hu.tail h,fun hv ↦ hv.tail (hsymm h)⟩
  let I := {e : Fin N × Fin N // R e.1 e.2 ∧ reach e.1}
  let J := {e : Fin N × Fin N // R e.1 e.2 ∧ ¬ reach e.1}
  let S : Set E := ⋃ e : I, segment ℝ (p e.val.1) (p e.val.2)
  let T : Set E := ⋃ e : J, segment ℝ (p e.val.1) (p e.val.2)
  have hclosed (u v : Fin N) : IsClosed (segment ℝ (p u) (p v)) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hS : IsClosed S := isClosed_iUnion_of_finite (fun e ↦ hclosed e.val.1 e.val.2)
  have hT : IsClosed T := isClosed_iUnion_of_finite (fun e ↦ hclosed e.val.1 e.val.2)
  have hST : S ∩ T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxS,hxT⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxS
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxT
    have hcommon : ({i.val.1,i.val.2} ∩ {j.val.1,j.val.2} : Finset (Fin N)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hww := Finset.mem_inter.mp hw
      have hwr : reach w := by
        rcases Finset.mem_insert.mp hww.1 with rfl | hw
        · exact i.property.2
        · exact (Finset.mem_singleton.mp hw) ▸ (hedge _ _ i.property.1).mp i.property.2
      apply j.property.2
      rcases Finset.mem_insert.mp hww.2 with rfl | hw
      · exact hwr
      · exact (hedge _ _ j.property.1).mpr ((Finset.mem_singleton.mp hw) ▸ hwr)
    have hx : x ∈ convexHull ℝ (p ''
        (({i.val.1,i.val.2} ∩ {j.val.1,j.val.2} : Finset (Fin N)) : Set (Fin N))) := by
      rw [← hfaces _ (hface _ _ i.property.1) _ (hface _ _ j.property.1)]
      simpa only [Finset.coe_pair,Set.image_pair,convexHull_pair,Set.mem_inter_iff] using And.intro hi hj
    simp only [hcommon,Finset.coe_empty,Set.image_empty,convexHull_empty,Set.mem_empty_iff_false] at hx
  have hsub : C ⊆ S ∪ T := by
    intro x hx
    rw [hcover] at hx
    obtain ⟨u,hx⟩ := mem_iUnion.mp hx
    obtain ⟨v,hx⟩ := mem_iUnion.mp hx
    obtain ⟨huv,hx⟩ := mem_iUnion.mp hx
    by_cases hu : reach u
    · exact Or.inl (mem_iUnion.mpr ⟨⟨(u,v),huv,hu⟩,hx⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨(u,v),huv,hu⟩,hx⟩)
  have hpoint (u v : Fin N) (h : R u v) : p u ∈ C := by
    rw [hcover]
    exact mem_iUnion.mpr ⟨u,mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨h,left_mem_segment ℝ _ _⟩⟩⟩
  have hCS : (C ∩ S).Nonempty := by
    obtain ⟨c,hac⟩ := hneighbors a ha
    exact ⟨p a,hpoint a c hac,mem_iUnion.mpr ⟨⟨(a,c),hac,Relation.ReflTransGen.refl⟩,
      left_mem_segment ℝ _ _⟩⟩
  have hCT : (C ∩ T).Nonempty := by
    obtain ⟨c,hbc⟩ := hneighbors b hb
    exact ⟨p b,hpoint b c hbc,mem_iUnion.mpr ⟨⟨(b,c),hbc,hnot⟩,
      left_mem_segment ℝ _ _⟩⟩
  obtain ⟨x,_,hx⟩ := isPreconnected_closed_iff.mp hC S T hS hT hsub hCS hCT
  simp only [hST,Set.mem_empty_iff_false] at hx


/-- A connected set covered by finitely many disjoint closed sets lies in the
unique member it meets. -/
theorem finite_closed_partition_connected_subset {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (C : ι → Set X) (hclosed : ∀ i, IsClosed (C i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (S : Set X) (hS : IsPreconnected S) (hcover : S ⊆ ⋃ i, C i)
    (j : ι) (hSj : (S ∩ C j).Nonempty) : S ⊆ C j := by
  classical
  let T : Set X := ⋃ k : {k : ι // k ≠ j}, C k.val
  have hT : IsClosed T := isClosed_iUnion_of_finite (fun k ↦ hclosed k.val)
  have hsub : S ⊆ C j ∪ T := by
    intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover hx)
    by_cases he : k = j
    · exact Or.inl (he ▸ hk)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k,he⟩,hk⟩)
  intro x hx
  by_contra hxj
  have hxT : x ∈ T := (hsub hx).resolve_left hxj
  obtain ⟨y,_,hyj,hyT⟩ := isPreconnected_closed_iff.mp hS (C j) T (hclosed j) hT
    hsub hSj ⟨x,hx,hxT⟩
  obtain ⟨k,hyk⟩ := mem_iUnion.mp hyT
  exact Set.disjoint_left.mp (hdisjoint j k.val k.property.symm) hyj hyk

end HolomorphicAnosov.Topology.CairnsStrip
