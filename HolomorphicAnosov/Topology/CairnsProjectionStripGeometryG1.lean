import HolomorphicAnosov.Topology.FinitePlaneProjection
import HolomorphicAnosov.Topology.CairnsRectangleSimplicity
import HolomorphicAnosov.Topology.FiniteSurfacePlanarFrontierG9
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Convex.PathConnected

/-!
# Generic-projection strip geometry for a polygonal annulus

Cairns (1951), preliminary 2(B), p.860: after a generic shear, each boundary edge
is the graph of an affine function. Noncrossing graphs retain their order on a
strip, and each intervening band belongs to one side of the polygon boundary.
-/

noncomputable section
open Set
namespace HolomorphicAnosov.Topology.CairnsStrip
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The separating linear projection chosen for the finite vertex set. -/
def projection (t : ℝ) (x : Plane) : ℝ := x 0 + t * x 1

/-- Sheared coordinates preserve the ordinate. -/
def shear (t : ℝ) : Plane ≃ₜ (ℝ × ℝ) where
  toFun x := (projection t x, x 1)
  invFun x := WithLp.toLp 2 ![x.1 - t * x.2, x.2]
  left_inv x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [projection]
  right_inv x := by simp [projection]
  continuous_toFun := by
    show Continuous (fun x : Plane => (x 0 + t * x 1, x 1))
    fun_prop
  continuous_invFun := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
      (continuous_pi fun i ↦ by fin_cases i <;> fun_prop)

/-- The affine height function of a nonvertical edge in sheared coordinates. -/
def edgeHeight (t : ℝ) (a b : Plane) (u : ℝ) : ℝ :=
  a 1 + (u - projection t a) / (projection t b - projection t a) * (b 1 - a 1)

lemma projection_lineMap (t : ℝ) (a b : Plane) (r : ℝ) :
    projection t (AffineMap.lineMap a b r) =
      projection t a + r * (projection t b - projection t a) := by
  simp [projection, AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply]
  ring

lemma lineMap_ordinate (t : ℝ) (a b : Plane)
    (hab : projection t a ≠ projection t b) (r : ℝ) :
    (AffineMap.lineMap a b r) 1 =
      edgeHeight t a b (projection t (AffineMap.lineMap a b r)) := by
  rw [projection_lineMap]
  simp only [edgeHeight]
  rw [add_sub_cancel_left, mul_div_cancel_right₀ r (sub_ne_zero.mpr hab.symm)]
  simp [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply]
  ring

/-- A nonvertical closed segment is exactly its affine graph over the interval
between its projected endpoints. -/
theorem segment_graph (t : ℝ) (a b : Plane) (hab : projection t a < projection t b)
    (x : Plane) :
    x ∈ segment ℝ a b ↔
      projection t x ∈ Icc (projection t a) (projection t b) ∧
        x 1 = edgeHeight t a b (projection t x) := by
  constructor
  · rw [segment_eq_image_lineMap]
    rintro ⟨r, hr, rfl⟩
    refine ⟨?_, lineMap_ordinate t a b hab.ne r⟩
    rw [projection_lineMap]
    constructor <;> nlinarith [hr.1, hr.2]
  · rintro ⟨hx, hy⟩
    let r := (projection t x - projection t a) / (projection t b - projection t a)
    have hr : r ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le
      · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
    have hp : projection t (AffineMap.lineMap a b r) = projection t x := by
      rw [projection_lineMap]
      dsimp only [r]
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
      ring
    have heq : AffineMap.lineMap a b r = x := by
      apply (shear t).injective
      apply Prod.ext
      · exact hp
      · change (AffineMap.lineMap a b r) 1 = x 1
        rw [lineMap_ordinate t a b hab.ne, hp, hy]
    rw [← heq]
    exact lineMap_mem_segment ℝ a b hr

lemma continuous_edgeHeight (t : ℝ) (a b : Plane) : Continuous (edgeHeight t a b) := by
  unfold edgeHeight
  fun_prop

/-- Two disjoint edge graphs cannot exchange vertical order in a connected strip. -/
theorem graph_order_on_interval (f g : ℝ → ℝ) (l r : ℝ)
    (hf : ContinuousOn f (Ioo l r)) (hg : ContinuousOn g (Ioo l r))
    (hne : ∀ u ∈ Ioo l r, f u ≠ g u) :
    (∀ u ∈ Ioo l r, f u < g u) ∨ (∀ u ∈ Ioo l r, g u < f u) := by
  have h := isPreconnected_Ioo.image (fun u ↦ f u - g u) (hf.sub hg)
  have hsub : (fun u ↦ f u - g u) '' Ioo l r ⊆ Iio 0 ∪ Ioi 0 := by
    rintro z ⟨u, hu, rfl⟩
    exact lt_or_gt_of_ne (sub_ne_zero.mpr (hne u hu))
  rcases h.subset_or_subset isOpen_Iio isOpen_Ioi
      (Set.disjoint_left.mpr (fun x hx hy ↦ (lt_trans hx hy).false)) hsub with h | h
  · exact Or.inl (fun u hu ↦ sub_neg.mp (h (Set.mem_image_of_mem _ hu)))
  · exact Or.inr (fun u hu ↦ sub_pos.mp (h (Set.mem_image_of_mem _ hu)))

/-- A connected band avoiding a closed set's frontier lies wholly on one side.
The two open sides cover the band and cannot both meet a connected set. -/
theorem band_side {X : Type*} [TopologicalSpace X] (D S : Set X)
    (hD : IsClosed D) (hS : IsPreconnected S) (havoid : Disjoint S (frontier D)) :
    S ⊆ interior D ∨ S ⊆ Dᶜ := by
  apply hS.subset_or_subset isOpen_interior hD.isOpen_compl
    (Set.disjoint_left.mpr (fun _ hx hy ↦ hy (interior_subset hx)))
  intro x hx
  by_cases hd : x ∈ D
  · left
    by_contra hi
    exact Set.disjoint_left.mp havoid hx
      (by rw [frontier, hD.closure_eq]; exact ⟨hd, hi⟩)
  · exact Or.inr hd



/-- A strip cell in coordinates normalized to have horizontal range `[0,1]`. -/
def closedBand (a b c d : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧
    (1-p.1)*a+p.1*b ≤ p.2 ∧ p.2 ≤ (1-p.1)*c+p.1*d}

lemma convex_closedBand (a b c d : ℝ) : Convex ℝ (closedBand a b c d) := by
  intro p hp q hq s t hs ht hst
  change 0 ≤ s*p.1+t*q.1 ∧ s*p.1+t*q.1 ≤ 1 ∧
    (1-(s*p.1+t*q.1))*a+(s*p.1+t*q.1)*b ≤ s*p.2+t*q.2 ∧
      s*p.2+t*q.2 ≤ (1-(s*p.1+t*q.1))*c+(s*p.1+t*q.1)*d
  rcases hp with ⟨hp0,hp1,hpl,hpu⟩
  rcases hq with ⟨hq0,hq1,hql,hqu⟩
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr hp1), mul_nonneg ht (sub_nonneg.mpr hq1)]
  · have h := add_le_add (mul_le_mul_of_nonneg_left hpl hs)
      (mul_le_mul_of_nonneg_left hql ht)
    have he : 1-(s*p.1+t*q.1) = s*(1-p.1)+t*(1-q.1) := by nlinarith
    rw [he]
    nlinarith
  · have h := add_le_add (mul_le_mul_of_nonneg_left hpu hs)
      (mul_le_mul_of_nonneg_left hqu ht)
    have he : 1-(s*p.1+t*q.1) = s*(1-p.1)+t*(1-q.1) := by nlinarith
    rw [he]
    nlinarith

lemma band_corners_mem (a b c d : ℝ) (hac : a ≤ c) (hbd : b ≤ d) :
    ({(0,a),(1,b),(1,d),(0,c)} : Set (ℝ × ℝ)) ⊆ closedBand a b c d := by
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp [closedBand, hac, hbd]

/-- Lower and upper affine sides enclose their convex combinations. -/
theorem closedBand_eq_convexHull (a b c d : ℝ) (hac : a ≤ c) (hbd : b ≤ d) :
    closedBand a b c d = convexHull ℝ {(0,a),(1,b),(1,d),(0,c)} := by
  apply subset_antisymm
  · intro p hp
    rcases hp with ⟨hp0,hp1,hpl,hpu⟩
    let L : ℝ × ℝ := (p.1, (1-p.1)*a+p.1*b)
    let U : ℝ × ℝ := (p.1, (1-p.1)*c+p.1*d)
    have hL : L ∈ convexHull ℝ {(0,a),(1,b),(1,d),(0,c)} := by
      have h := (convex_convexHull ℝ {(0,a),(1,b),(1,d),(0,c)})
        (subset_convexHull ℝ _ (by simp : (0,a) ∈ ({(0,a),(1,b),(1,d),(0,c)} : Set (ℝ × ℝ))))
        (subset_convexHull ℝ _ (by simp : (1,b) ∈ ({(0,a),(1,b),(1,d),(0,c)} : Set (ℝ × ℝ))))
        (sub_nonneg.mpr hp1) hp0 (by ring : 1-p.1+p.1=1)
      simpa [L, Prod.smul_mk, Prod.mk_add_mk] using h
    have hU : U ∈ convexHull ℝ {(0,a),(1,b),(1,d),(0,c)} := by
      have h := (convex_convexHull ℝ {(0,a),(1,b),(1,d),(0,c)})
        (subset_convexHull ℝ _ (by simp : (0,c) ∈ ({(0,a),(1,b),(1,d),(0,c)} : Set (ℝ × ℝ))))
        (subset_convexHull ℝ _ (by simp : (1,d) ∈ ({(0,a),(1,b),(1,d),(0,c)} : Set (ℝ × ℝ))))
        (sub_nonneg.mpr hp1) hp0 (by ring : 1-p.1+p.1=1)
      simpa [U, Prod.smul_mk, Prod.mk_add_mk] using h
    have hpseg : p ∈ segment ℝ L U := by
      by_cases heq : U.2 = L.2
      · have hpL : p = L := Prod.ext rfl (by dsimp [L,U] at heq ⊢; linarith)
        rw [hpL]
        exact left_mem_segment ℝ L U
      · have hpos : 0 < U.2 - L.2 := by
          have hle : L.2 ≤ U.2 := hpl.trans hpu
          exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm heq))
        let r := (p.2-L.2)/(U.2-L.2)
        have hr0 : 0 ≤ r := div_nonneg (by dsimp [L]; linarith) hpos.le
        have hr1 : r ≤ 1 := (div_le_one hpos).mpr (by dsimp [U]; linarith)
        have h := lineMap_mem_segment ℝ L U (show r ∈ Icc (0:ℝ) 1 from ⟨hr0,hr1⟩)
        convert h using 1
        apply Prod.ext
        · simp [AffineMap.lineMap_apply_module, L,U]
          ring
        · simp only [AffineMap.lineMap_apply_module, Prod.snd_add]
          dsimp [r]
          field_simp
          nlinarith
    exact (convex_convexHull ℝ _).segment_subset hL hU hpseg
  · exact convexHull_min (band_corners_mem a b c d hac hbd) (convex_closedBand a b c d)

/-- Each convex strip cell is the union of two closed triangles. This includes
one or both vertical sides degenerating to a point. The diagonal joins the
lower left and upper right corners. -/
theorem closedBand_two_triangles (a b c d : ℝ) (hac : a ≤ c) (hbd : b ≤ d) :
    closedBand a b c d =
      convexHull ℝ {(0,a),(1,b),(1,d)} ∪
        convexHull ℝ {(0,a),(1,d),(0,c)} := by
  have hlow : closedBand a b a d = convexHull ℝ {(0,a),(1,b),(1,d)} := by
    rw [closedBand_eq_convexHull a b a d le_rfl hbd]
    congr 1
    ext p
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  have hupp : closedBand a d c d = convexHull ℝ {(0,a),(1,d),(0,c)} := by
    simpa only [Set.insert_idem] using closedBand_eq_convexHull a d c d hac le_rfl
  apply subset_antisymm
  · intro p hp
    rcases le_total p.2 ((1-p.1)*a+p.1*d) with h | h
    · exact Or.inl (hlow ▸ ⟨hp.1,hp.2.1,hp.2.2.1,h⟩)
    · exact Or.inr (hupp ▸ ⟨hp.1,hp.2.1,h,hp.2.2.2⟩)
  · apply union_subset
    · apply convexHull_min _ (convex_closedBand a b c d)
      intro p hp
      apply band_corners_mem a b c d hac hbd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      tauto
    · apply convexHull_min _ (convex_closedBand a b c d)
      intro p hp
      apply band_corners_mem a b c d hac hbd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      tauto

/-- The triangles in the strip-cell split meet exactly along their shared
closed diagonal, including both endpoints. -/
theorem closedBand_triangles_inter (a b c d : ℝ) (hac : a ≤ c) (hbd : b ≤ d) :
    convexHull ℝ {((0:ℝ),a),(1,b),(1,d)} ∩
        convexHull ℝ {(0,a),(1,d),(0,c)} = segment ℝ (0,a) (1,d) := by
  have hlow : closedBand a b a d = convexHull ℝ {(0,a),(1,b),(1,d)} := by
    rw [closedBand_eq_convexHull a b a d le_rfl hbd]
    congr 1
    ext p
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  have hupp : closedBand a d c d = convexHull ℝ {(0,a),(1,d),(0,c)} := by
    simpa only [Set.insert_idem] using closedBand_eq_convexHull a d c d hac le_rfl
  rw [← hlow, ← hupp]
  apply subset_antisymm
  · rintro p ⟨hl,hu⟩
    have hy : p.2 = (1-p.1)*a+p.1*d := le_antisymm hl.2.2.2 hu.2.2.1
    have h := lineMap_mem_segment ℝ ((0:ℝ),a) (1,d)
      (show p.1 ∈ Icc (0:ℝ) 1 from ⟨hl.1,hl.2.1⟩)
    convert h using 1
    apply Prod.ext
    · simp [AffineMap.lineMap_apply_module]
    · simpa [AffineMap.lineMap_apply_module] using hy
  · intro p hp
    constructor
    · exact (convex_closedBand a b a d).segment_subset
        (by simp [closedBand]) (by simp [closedBand,hbd]) hp
    · exact (convex_closedBand a d c d).segment_subset
        (by simp [closedBand,hac]) (by simp [closedBand]) hp


/-- The vertical affine line used to test nondegeneracy of a strip triangle. -/
def verticalLine (u : ℝ) : AffineSubspace ℝ (ℝ × ℝ) where
  carrier := {p | p.1 = u}
  smul_vsub_vadd_mem' c p q r hp hq hr := by
    change c * (p.1 - q.1) + r.1 = u
    change p.1 = u at hp
    change q.1 = u at hq
    change r.1 = u at hr
    rw [hp,hq,hr]
    ring

/-- The lower triangle is nondegenerate whenever its vertical right side is. -/
theorem lowerTriangle_affineIndependent (a b d : ℝ) (hbd : b ≠ d) :
    AffineIndependent ℝ ![((0:ℝ),a),(1,b),(1,d)] := by
  apply affineIndependent_of_ne_of_notMem_of_mem_of_mem (s := verticalLine 1)
  · intro h
    exact hbd (congrArg Prod.snd h)
  · change ¬ (0:ℝ) = 1
    norm_num
  · rfl
  · rfl

/-- The upper triangle is nondegenerate whenever its vertical left side is. -/
theorem upperTriangle_affineIndependent (a c d : ℝ) (hac : a ≠ c) :
    AffineIndependent ℝ ![((0:ℝ),a),(1,d),(0,c)] := by
  apply affineIndependent_of_ne_of_mem_of_notMem_of_mem (s := verticalLine 0)
  · intro h
    exact hac (congrArg Prod.snd h)
  · rfl
  · change ¬ (1:ℝ) = 0
    norm_num
  · rfl

/-- The closed strip cell is closed in the coordinate plane. -/
lemma isClosed_closedBand (a b c d : ℝ) : IsClosed (closedBand a b c d) := by
  unfold closedBand
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_fst continuous_const)
  exact (isClosed_le (by fun_prop) continuous_snd).inter
    (isClosed_le continuous_snd (by fun_prop))

/-- Strict inequalities define an open subset of the strip cell. -/
lemma strictBand_subset_interior (a b c d : ℝ) :
    {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 ∧
      (1-p.1)*a+p.1*b < p.2 ∧ p.2 < (1-p.1)*c+p.1*d} ⊆
        interior (closedBand a b c d) := by
  apply interior_maximal
  · rintro p ⟨h0,h1,hl,hu⟩
    exact ⟨h0.le,h1.le,hl.le,hu.le⟩
  · apply IsOpen.inter (isOpen_lt continuous_const continuous_fst)
    apply IsOpen.inter (isOpen_lt continuous_fst continuous_const)
    exact (isOpen_lt (by fun_prop) continuous_snd).inter
      (isOpen_lt continuous_snd (by fun_prop))

/-- At least one noncollapsed vertical side makes the strip cell full dimensional. -/
theorem closedBand_interior_nonempty (a b c d : ℝ) (hac : a ≤ c) (hbd : b ≤ d)
    (hne : a < c ∨ b < d) : (interior (closedBand a b c d)).Nonempty := by
  refine ⟨(1/2,(a+b+c+d)/4), strictBand_subset_interior a b c d ?_⟩
  change 0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1 ∧
    (1-1/2)*a+(1/2)*b < (a+b+c+d)/4 ∧
      (a+b+c+d)/4 < (1-1/2)*c+(1/2)*d
  rcases hne with hne | hne <;> norm_num <;> constructor <;> linarith

/-- The closure of the open cell recovers its full closed polygon, including
its vertical sides and any collapsed endpoint. -/
theorem closedBand_regular (a b c d : ℝ) (hac : a ≤ c) (hbd : b ≤ d)
    (hne : a < c ∨ b < d) :
    closure (interior (closedBand a b c d)) = closedBand a b c d := by
  rw [(convex_closedBand a b c d).closure_interior_eq_closure_of_nonempty_interior
    (closedBand_interior_nonempty a b c d hac hbd hne), (isClosed_closedBand a b c d).closure_eq]

/-- Inserting a point on a vertical side subdivides a triangle without
changing its carrier. Convex join distributes over the two subsegments. -/
theorem verticalTriangle_split (p : ℝ × ℝ) (u a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    convexHull ℝ {p,(u,a),(u,c)} =
      convexHull ℝ {p,(u,a),(u,b)} ∪ convexHull ℝ {p,(u,b),(u,c)} := by
  let f : ℝ →ᵃ[ℝ] (ℝ × ℝ) := (AffineMap.const ℝ ℝ u).prod (AffineMap.id ℝ ℝ)
  have hseg : segment ℝ (u,a) (u,c) = segment ℝ (u,a) (u,b) ∪ segment ℝ (u,b) (u,c) := by
    have h := congrArg (fun s : Set ℝ ↦ f '' s) (Icc_union_Icc_eq_Icc hab hbc)
    rw [Set.image_union] at h
    have hi (x y : ℝ) (hxy : x ≤ y) : f '' Icc x y = segment ℝ (u,x) (u,y) := by
      rw [← segment_eq_Icc hxy, image_segment]
      rfl
    rw [hi a b hab, hi b c hbc, hi a c (hab.trans hbc)] at h
    exact h.symm
  rw [← convexJoin_singleton_segment, hseg, convexJoin_union_right,
    convexJoin_singleton_segment, convexJoin_singleton_segment]

/-- A finite increasing subdivision of a vertical side gives an exact fan
triangulation of the original triangle. -/
theorem verticalTriangle_fan (p : ℝ × ℝ) (u : ℝ) (y : ℕ → ℝ) (hy : Monotone y)
    (n : ℕ) (hn : 0 < n) :
    convexHull ℝ {p,(u,y 0),(u,y n)} =
      ⋃ i ∈ Finset.range n, convexHull ℝ {p,(u,y i),(u,y (i+1))} := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      rw [verticalTriangle_split p u (y 0) (y n) (y (n+1)) (hy (Nat.zero_le n))
        (hy (Nat.le_succ n)), ih hnpos]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro (⟨i,hi,hx⟩ | hx)
        · exact ⟨i, by omega, hx⟩
        · exact ⟨n, by omega, hx⟩
      · rintro ⟨i,hi,hx⟩
        by_cases hin : i = n
        · exact Or.inr (hin ▸ hx)
        · exact Or.inl ⟨i, by omega, hx⟩

/-- A strip with a collapsed left side is precisely its remaining triangle. -/
lemma lowerTriangle_eq_band (a b c : ℝ) (hbc : b ≤ c) :
    convexHull ℝ {((0:ℝ),a),(1,b),(1,c)} = closedBand a b a c := by
  rw [closedBand_eq_convexHull a b a c le_rfl hbc]
  congr 1
  ext p
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto

/-- A strip collapsed along both sides is its diagonal segment. -/
lemma thinBand_eq_segment (a b : ℝ) :
    closedBand a b a b = segment ℝ (0,a) (1,b) := by
  rw [closedBand_eq_convexHull a b a b le_rfl le_rfl, ← convexHull_pair]
  congr 1
  ext p
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto

/-- Consecutive triangles in a vertical fan meet along exactly their shared
radial edge. -/
theorem verticalFan_adjacent_inter (a b c d : ℝ) (hbc : b ≤ c) (hcd : c ≤ d) :
    convexHull ℝ {((0:ℝ),a),(1,b),(1,c)} ∩
      convexHull ℝ {(0,a),(1,c),(1,d)} = segment ℝ (0,a) (1,c) := by
  rw [lowerTriangle_eq_band a b c hbc, lowerTriangle_eq_band a c d hcd,
    ← thinBand_eq_segment a c]
  ext p
  constructor
  · rintro ⟨hl,hr⟩
    exact ⟨hl.1,hl.2.1,hr.2.2.1,hl.2.2.2⟩
  · rintro ⟨h0,h1,hl,hu⟩
    refine ⟨⟨h0,h1,?_,hu⟩,⟨h0,h1,hl,?_⟩⟩
    · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hbc)]
    · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hcd)]

/-- Fan triangles with separated vertical bases meet only at the apex. -/
theorem verticalFan_separated_inter (a b c d e : ℝ)
    (hbc : b ≤ c) (hcd : c < d) (hde : d ≤ e) :
    convexHull ℝ {((0:ℝ),a),(1,b),(1,c)} ∩
      convexHull ℝ {(0,a),(1,d),(1,e)} = {(0,a)} := by
  rw [lowerTriangle_eq_band a b c hbc, lowerTriangle_eq_band a d e hde]
  ext p
  constructor
  · rintro ⟨hl,hr⟩
    have h0 : p.1 = 0 := by
      have hle := hr.2.2.1.trans hl.2.2.2
      have hmul : p.1 * (d-c) ≤ 0 := by nlinarith
      have hn : ¬ 0 < p.1 := by intro hp; nlinarith [mul_pos hp (sub_pos.mpr hcd)]
      exact le_antisymm (le_of_not_gt hn) hl.1
    have hy : p.2 = a := by
      have hlow := hl.2.2.1
      have hupp := hl.2.2.2
      rw [h0] at hlow hupp
      nlinarith
    exact Prod.ext h0 hy
  · rintro rfl
    constructor <;> simp [closedBand]

/-- The horizontal affine change restoring an actual strip's width and offset. -/
def horizontalStretch (l r : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun x := (l+(r-l)*x.1,x.2)
  linear :=
    { toFun := fun x ↦ ((r-l)*x.1,x.2)
      map_add' := by intro x y; (apply Prod.ext <;> simp); ring
      map_smul' := by intro c x; (apply Prod.ext <;> simp); ring }
  map_vadd' x y := by
    (apply Prod.ext <;> simp); ring

/-- Positive-width strips retain all geometric distinctions under normalization. -/
lemma horizontalStretch_injective (l r : ℝ) (hlr : l < r) :
    Function.Injective (horizontalStretch l r) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext
  · change l+(r-l)*x.1 = l+(r-l)*y.1 at h1
    exact mul_left_cancel₀ (sub_ne_zero.mpr hlr.ne') (add_left_cancel h1)
  · exact h2

/-- Coordinate normalization sends every named triangle to the convex hull of
the same three stretched vertices. -/
lemma horizontalStretch_triangle (l r : ℝ) (a b c : ℝ × ℝ) :
    horizontalStretch l r '' convexHull ℝ {a,b,c} =
      convexHull ℝ {horizontalStretch l r a,horizontalStretch l r b,horizontalStretch l r c} := by
  rw [AffineMap.image_convexHull]
  simp only [Set.image_insert_eq,Set.image_singleton]

/-- Restoring the original horizontal coordinates preserves the full strip-cell
triangulation, including both collapsed-side cases. -/
theorem stretchedBand_two_triangles (l r a b c d : ℝ) (hac : a ≤ c) (hbd : b ≤ d) :
    horizontalStretch l r '' closedBand a b c d =
      convexHull ℝ {(l,a),(r,b),(r,d)} ∪ convexHull ℝ {(l,a),(r,d),(l,c)} := by
  rw [closedBand_two_triangles a b c d hac hbd,Set.image_union,
    horizontalStretch_triangle,horizontalStretch_triangle]
  simp [horizontalStretch]

/-- Positive-width stretching preserves the exact shared diagonal. -/
theorem stretchedBand_triangles_inter (l r a b c d : ℝ) (hlr : l < r)
    (hac : a ≤ c) (hbd : b ≤ d) :
    convexHull ℝ {(l,a),(r,b),(r,d)} ∩ convexHull ℝ {(l,a),(r,d),(l,c)} =
      segment ℝ (l,a) (r,d) := by
  have h := congrArg (fun s : Set (ℝ × ℝ) ↦ horizontalStretch l r '' s)
    (closedBand_triangles_inter a b c d hac hbd)
  rw [Set.image_inter (horizontalStretch_injective l r hlr),horizontalStretch_triangle,
    horizontalStretch_triangle,image_segment] at h
  simpa [horizontalStretch] using h

/-- The closure of a selected open cell stays on the exterior side of the
polygon. The witness chooses the exterior component of the frontier complement. -/
theorem regularCell_exterior {X : Type*} [TopologicalSpace X]
    (D S : Set X) (hD : IsClosed D) (hreg : closure (interior S) = S)
    (hconn : IsPreconnected (interior S))
    (havoid : Disjoint (interior S) (frontier D))
    (hwitness : (interior S \ D).Nonempty) : S ⊆ (interior D)ᶜ := by
  have hout : interior S ⊆ Dᶜ := by
    rcases band_side D (interior S) hD hconn havoid with hin | hout
    · rcases hwitness with ⟨x, hx, hnot⟩
      exact False.elim (hnot (interior_subset (hin hx)))
    · exact hout
  rw [← hreg, ← closure_compl]
  exact closure_mono hout

/-- A closed rectangular region with a closed hole strictly inside it is the
closure of its open exterior. This includes both boundary components. -/
theorem annulus_closure_open {X : Type*} [TopologicalSpace X]
    (D R : Set X) (hD : IsClosed D) (hR : IsClosed R)
    (hreg : closure (interior R) = R) (hcontain : D ⊆ interior R) :
    closure (interior R \ D) = R \ interior D := by
  apply subset_antisymm
  · apply closure_minimal
    · exact fun x hx ↦ ⟨interior_subset hx.1, fun h ↦ hx.2 (interior_subset h)⟩
    · exact hR.sdiff isOpen_interior
  · intro x hx
    by_cases hi : x ∈ interior R
    · have hc : x ∈ closure Dᶜ := by rw [closure_compl]; exact hx.2
      exact isOpen_interior.inter_closure ⟨hi, hc⟩
    · have hd : x ∉ D := fun h ↦ hi (hcontain h)
      have hc : x ∈ closure (interior R) \ closure D := by
        rw [hreg, hD.closure_eq]
        exact ⟨hx.1, hd⟩
      exact closure_sdiff hc

/-- Finite closed cells covering the open exterior away from a dense set's
exceptional lines cover the entire closed annulus. -/
theorem annulus_finite_closed_cover {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (D R G : Set X) (C : ι → Set X) (hD : IsClosed D) (hR : IsClosed R)
    (hreg : closure (interior R) = R) (hcontain : D ⊆ interior R)
    (hG : Dense G) (hclosed : ∀ i, IsClosed (C i))
    (hsub : ∀ i, C i ⊆ R \ interior D)
    (hcover : (interior R \ D) ∩ G ⊆ ⋃ i, C i) :
    (⋃ i, C i) = R \ interior D := by
  apply subset_antisymm (iUnion_subset hsub)
  rw [← annulus_closure_open D R hD hR hreg hcontain]
  apply closure_minimal _ (isClosed_iUnion_of_finite hclosed)
  exact (hG.open_subset_closure_inter (isOpen_interior.sdiff hD)).trans
    (closure_minimal hcover (isClosed_iUnion_of_finite hclosed))

/-- The finitely many exceptional vertical lines do not affect density. -/
lemma finite_vertical_complement_dense (T : Finset ℝ) :
    Dense {p : ℝ × ℝ | p.1 ∉ T} := by
  classical
  have h : Dense ((T : Set ℝ)ᶜ) := by
    induction T using Finset.induction_on with
    | empty => simpa only [Finset.coe_empty, compl_empty] using (dense_univ : Dense (univ : Set ℝ))
    | @insert a T ha ih =>
      simpa only [Finset.coe_insert, Set.insert_eq, compl_union, inter_comm] using
        ih.inter_of_isOpen_right (dense_compl_singleton a) isOpen_compl_singleton
  exact h.preimage isOpenMap_fst

/-- Coefficients for a nonvertical supporting line. -/
def lineHeight (f : ℝ × ℝ) (x : ℝ) : ℝ := f.1*x+f.2

lemma continuous_lineHeight (f : ℝ × ℝ) : Continuous (lineHeight f) := by
  unfold lineHeight
  fun_prop

/-- All abscissae at which two distinct nonparallel supporting lines cross. -/
def crossingLevels (F : Finset (ℝ × ℝ)) : Finset ℝ := by
  classical
  exact ((F ×ˢ F).filter (fun p ↦ p.1.1 ≠ p.2.1)).image
    (fun p ↦ (p.2.2-p.1.2)/(p.1.1-p.2.1))

lemma lineHeight_ne_of_not_crossing (F : Finset (ℝ × ℝ))
    (f g : ℝ × ℝ) (hf : f ∈ F) (hg : g ∈ F) (hfg : f ≠ g)
    (x : ℝ) (hx : x ∉ crossingLevels F) : lineHeight f x ≠ lineHeight g x := by
  classical
  intro heq
  by_cases hs : f.1 = g.1
  · apply hfg
    apply Prod.ext hs
    unfold lineHeight at heq
    rw [hs] at heq
    linarith
  · apply hx
    apply Finset.mem_image.mpr
    refine ⟨(f,g), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf,hg⟩,hs⟩, ?_⟩
    dsimp
    apply (div_eq_iff (sub_ne_zero.mpr hs)).mpr
    unfold lineHeight at heq
    nlinarith

/-- Two successive critical levels bound an open strip containing no crossing. -/
def ConsecutiveLevels (T : Finset ℝ) (l r : ℝ) : Prop :=
  l ∈ T ∧ r ∈ T ∧ l < r ∧ ∀ u ∈ T, u ≤ l ∨ r ≤ u

/-- Every noncritical coordinate between finite extreme levels lies in a
uniquely delimited gap (existence form). -/
theorem exists_consecutiveLevels (T : Finset ℝ) (x : ℝ) (hx : x ∉ T)
    (hleft : ∃ l ∈ T, l < x) (hright : ∃ r ∈ T, x < r) :
    ∃ l r, ConsecutiveLevels T l r ∧ x ∈ Ioo l r := by
  classical
  let L := T.filter (· < x)
  let U := T.filter (x < ·)
  have hL : L.Nonempty := by
    rcases hleft with ⟨l,hl,hlx⟩
    exact ⟨l,Finset.mem_filter.mpr ⟨hl,hlx⟩⟩
  have hU : U.Nonempty := by
    rcases hright with ⟨r,hr,hxr⟩
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,hxr⟩⟩
  obtain ⟨l,hl,hlmax⟩ := L.exists_max_image id hL
  obtain ⟨r,hr,hrmin⟩ := U.exists_min_image id hU
  obtain ⟨hlT,hlx⟩ := Finset.mem_filter.mp hl
  obtain ⟨hrT,hxr⟩ := Finset.mem_filter.mp hr
  refine ⟨l,r,⟨hlT,hrT,hlx.trans hxr,?_⟩,hlx,hxr⟩
  intro u hu
  rcases lt_trichotomy u x with h | h | h
  · exact Or.inl (hlmax u (Finset.mem_filter.mpr ⟨hu,h⟩))
  · exact False.elim (hx (h ▸ hu))
  · exact Or.inr (hrmin u (Finset.mem_filter.mpr ⟨hu,h⟩))

lemma ConsecutiveLevels.not_mem {T : Finset ℝ} {l r x : ℝ}
    (h : ConsecutiveLevels T l r) (hx : x ∈ Ioo l r) : x ∉ T := by
  intro hm
  rcases h.2.2.2 x hm with h | h <;> linarith [hx.1,hx.2]

/-- The strict order of all supporting lines is constant throughout a strip. -/
theorem lineHeight_order_in_strip (F : Finset (ℝ × ℝ)) (T : Finset ℝ)
    (hT : crossingLevels F ⊆ T) (l r x : ℝ) (hgap : ConsecutiveLevels T l r)
    (hx : x ∈ Ioo l r) (f g : ℝ × ℝ) (hf : f ∈ F) (hg : g ∈ F)
    (hfg : lineHeight f x < lineHeight g x) :
    ∀ u ∈ Ioo l r, lineHeight f u < lineHeight g u := by
  have hne : f ≠ g := by intro h; subst g; exact hfg.false
  have hd : ∀ u ∈ Ioo l r, lineHeight f u ≠ lineHeight g u := by
    intro u hu
    apply lineHeight_ne_of_not_crossing F f g hf hg hne
    exact fun hm ↦ hgap.not_mem hu (hT hm)
  rcases graph_order_on_interval (lineHeight f) (lineHeight g) l r
    (continuous_lineHeight f).continuousOn (continuous_lineHeight g).continuousOn hd with h | h
  · exact h
  · exact False.elim ((h x hx).not_gt hfg)

/-- Endpoint heights inherit the weak order in an open strip, allowing a band
side to collapse to a vertex at a crossing. -/
lemma lineHeight_order_endpoints (f g : ℝ × ℝ) (l r : ℝ) (hlr : l < r)
    (horder : ∀ x ∈ Ioo l r, lineHeight f x < lineHeight g x) :
    lineHeight f l ≤ lineHeight g l ∧ lineHeight f r ≤ lineHeight g r := by
  have hclosed : Icc l r ⊆ {x | lineHeight f x ≤ lineHeight g x} := by
    rw [← closure_Ioo hlr.ne]
    exact closure_minimal (fun x hx ↦ (horder x hx).le)
      (isClosed_le (continuous_lineHeight f) (continuous_lineHeight g))
  exact ⟨hclosed ⟨le_rfl,hlr.le⟩,hclosed ⟨hlr.le,le_rfl⟩⟩

/-- A vertical shear making one supporting line horizontal. -/
def verticalShear (f : ℝ × ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1,p.2-lineHeight f p.1)
  invFun p := (p.1,p.2+lineHeight f p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by dsimp [lineHeight]; fun_prop
  continuous_invFun := by dsimp [lineHeight]; fun_prop

lemma isOpenMap_lineResidual (f : ℝ × ℝ) :
    IsOpenMap (fun p : ℝ × ℝ ↦ p.2-lineHeight f p.1) :=
  isOpenMap_snd.comp (verticalShear f).isOpenMap

lemma supporting_graph_complement_dense (f : ℝ × ℝ) :
    Dense {p : ℝ × ℝ | p.2 ≠ lineHeight f p.1} := by
  have h := (dense_compl_singleton (0:ℝ)).preimage (isOpenMap_lineResidual f)
  convert h using 1
  ext p
  simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_singleton_iff, sub_eq_zero]

/-- Points avoiding every supporting line and every critical vertical line are
dense. Thus a finite closed cell cover need only be checked at these points. -/
theorem arrangement_generic_dense (T : Finset ℝ) (F : Finset (ℝ × ℝ)) :
    Dense {p : ℝ × ℝ | p.1 ∉ T ∧ ∀ f ∈ F, p.2 ≠ lineHeight f p.1} := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using finite_vertical_complement_dense T
  | @insert f F hf ih =>
    have ho : IsOpen {p : ℝ × ℝ | p.2 ≠ lineHeight f p.1} :=
      isOpen_ne_fun continuous_snd ((continuous_lineHeight f).comp continuous_fst)
    have h := ih.inter_of_isOpen_right (supporting_graph_complement_dense f) ho
    convert h using 1
    ext p
    simp only [mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp, mem_inter_iff]
    tauto

/-- The closed cell between two full supporting lines in a vertical strip. -/
def stripCell (l r : ℝ) (f g : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | l ≤ p.1 ∧ p.1 ≤ r ∧ lineHeight f p.1 ≤ p.2 ∧ p.2 ≤ lineHeight g p.1}

lemma isClosed_stripCell (l r : ℝ) (f g : ℝ × ℝ) : IsClosed (stripCell l r f g) := by
  unfold stripCell
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_fst continuous_const)
  exact (isClosed_le ((continuous_lineHeight f).comp continuous_fst) continuous_snd).inter
    (isClosed_le continuous_snd ((continuous_lineHeight g).comp continuous_fst))

lemma convex_stripCell (l r : ℝ) (f g : ℝ × ℝ) : Convex ℝ (stripCell l r f g) := by
  intro p hp q hq s t hs ht hst
  change l ≤ s*p.1+t*q.1 ∧ s*p.1+t*q.1 ≤ r ∧
    f.1*(s*p.1+t*q.1)+f.2 ≤ s*p.2+t*q.2 ∧
      s*p.2+t*q.2 ≤ g.1*(s*p.1+t*q.1)+g.2
  rcases hp with ⟨hp0,hp1,hpl,hpu⟩
  rcases hq with ⟨hq0,hq1,hql,hqu⟩
  unfold lineHeight at hpl hpu hql hqu
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr hp0),mul_nonneg ht (sub_nonneg.mpr hq0),congrArg (fun a : ℝ ↦ a*l) hst]
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr hp1),mul_nonneg ht (sub_nonneg.mpr hq1),congrArg (fun a : ℝ ↦ a*r) hst]
  · have h := add_le_add (mul_le_mul_of_nonneg_left hpl hs)
      (mul_le_mul_of_nonneg_left hql ht)
    nlinarith [congrArg (fun a : ℝ ↦ a*f.2) hst]
  · have h := add_le_add (mul_le_mul_of_nonneg_left hpu hs)
      (mul_le_mul_of_nonneg_left hqu ht)
    nlinarith [congrArg (fun a : ℝ ↦ a*g.2) hst]

/-- The interior of a strip cell is exactly the four strict half-plane
inequalities, including when a vertical side collapses. -/
theorem interior_stripCell (l r : ℝ) (f g : ℝ × ℝ) :
    interior (stripCell l r f g) =
      {p | l < p.1 ∧ p.1 < r ∧ lineHeight f p.1 < p.2 ∧ p.2 < lineHeight g p.1} := by
  have hrep : stripCell l r f g =
      Prod.fst ⁻¹' Ici l ∩ (Prod.fst ⁻¹' Iic r ∩
      ((fun p : ℝ × ℝ ↦ p.2-lineHeight f p.1) ⁻¹' Ici 0 ∩
      (fun p : ℝ × ℝ ↦ p.2-lineHeight g p.1) ⁻¹' Iic 0)) := by
    ext p
    simp only [stripCell, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      mem_Ici, mem_Iic, sub_nonneg, sub_nonpos]
  rw [hrep,interior_inter,interior_inter,interior_inter,
    ← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst,
    ← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst,
    ← (isOpenMap_lineResidual f).preimage_interior_eq_interior_preimage (by unfold lineHeight; fun_prop),
    ← (isOpenMap_lineResidual g).preimage_interior_eq_interior_preimage (by unfold lineHeight; fun_prop),
    interior_Ici,interior_Iic,interior_Ici,interior_Iic]
  ext p
  simp only [mem_inter_iff,mem_preimage,mem_Ioi,mem_Iio,mem_ofPred_eq,sub_pos,sub_neg]

/-- A cell with a positive gap at one interior coordinate has nonempty interior. -/
lemma stripCell_interior_nonempty (l r x : ℝ) (f g : ℝ × ℝ)
    (hx : x ∈ Ioo l r) (hfg : lineHeight f x < lineHeight g x) :
    (interior (stripCell l r f g)).Nonempty := by
  rw [interior_stripCell]
  refine ⟨(x,(lineHeight f x+lineHeight g x)/2),hx.1,hx.2,?_,?_⟩ <;> linarith

lemma stripCell_regular (l r x : ℝ) (f g : ℝ × ℝ)
    (hx : x ∈ Ioo l r) (hfg : lineHeight f x < lineHeight g x) :
    closure (interior (stripCell l r f g)) = stripCell l r f g := by
  rw [(convex_stripCell l r f g).closure_interior_eq_closure_of_nonempty_interior
    (stripCell_interior_nonempty l r x f g hx hfg),(isClosed_stripCell l r f g).closure_eq]

/-- Adjacent supporting lines at one generic vertical slice. -/
def AdjacentLines (F : Finset (ℝ × ℝ)) (f g : ℝ × ℝ) (x : ℝ) : Prop :=
  f ∈ F ∧ g ∈ F ∧ lineHeight f x < lineHeight g x ∧
    ∀ h ∈ F, lineHeight h x ≤ lineHeight f x ∨ lineHeight g x ≤ lineHeight h x

/-- A point between two line heights and off all supporting lines lies between
an adjacent pair in the finite height order. -/
theorem exists_adjacentLines (F : Finset (ℝ × ℝ)) (x y : ℝ)
    (hoff : ∀ f ∈ F, y ≠ lineHeight f x)
    (hbelow : ∃ f ∈ F, lineHeight f x < y)
    (habove : ∃ g ∈ F, y < lineHeight g x) :
    ∃ f g, AdjacentLines F f g x ∧ lineHeight f x < y ∧ y < lineHeight g x := by
  classical
  let H := F.image (fun f ↦ lineHeight f x)
  have hy : y ∉ H := by
    rintro hm
    obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hm
    exact hoff f hf he.symm
  have hb : ∃ a ∈ H, a < y := by
    rcases hbelow with ⟨f,hf,he⟩
    exact ⟨lineHeight f x,Finset.mem_image.mpr ⟨f,hf,rfl⟩,he⟩
  have ha : ∃ b ∈ H, y < b := by
    rcases habove with ⟨f,hf,he⟩
    exact ⟨lineHeight f x,Finset.mem_image.mpr ⟨f,hf,rfl⟩,he⟩
  obtain ⟨a,b,hab,hay,hyb⟩ := exists_consecutiveLevels H y hy hb ha
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hab.1
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hab.2.1
  refine ⟨f,g,⟨hf,hg,hab.2.2.1,?_⟩,hay,hyb⟩
  intro h hh
  exact hab.2.2.2 _ (Finset.mem_image.mpr ⟨h,hh,rfl⟩)

/-- Adjacency is unchanged inside a strip, because none of the supporting
lines cross there. -/
theorem AdjacentLines.in_strip {F : Finset (ℝ × ℝ)} {T : Finset ℝ}
    (hT : crossingLevels F ⊆ T) {l r x u : ℝ}
    (hgap : ConsecutiveLevels T l r) (hx : x ∈ Ioo l r) (hu : u ∈ Ioo l r)
    {f g : ℝ × ℝ} (h : AdjacentLines F f g x) : AdjacentLines F f g u := by
  refine ⟨h.1,h.2.1,lineHeight_order_in_strip F T hT l r x hgap hx f g h.1 h.2.1
    h.2.2.1 u hu,?_⟩
  intro k hk
  rcases h.2.2.2 k hk with hkf | hgk
  · left
    rcases hkf.eq_or_lt with he | he
    · have heq : k = f := by
        by_contra hn
        exact lineHeight_ne_of_not_crossing F k f hk h.1 hn x
          (fun hm ↦ hgap.not_mem hx (hT hm)) he
      subst k
      exact le_rfl
    · exact (lineHeight_order_in_strip F T hT l r x hgap hx k f hk h.1 he u hu).le
  · right
    rcases hgk.eq_or_lt with he | he
    · have heq : g = k := by
        by_contra hn
        exact lineHeight_ne_of_not_crossing F g k h.2.1 hk hn x
          (fun hm ↦ hgap.not_mem hx (hT hm)) he
      subst k
      exact le_rfl
    · exact (lineHeight_order_in_strip F T hT l r x hgap hx g k h.2.1 hk he u hu).le

/-- No supporting line enters the interior of an adjacent cell. -/
theorem adjacentCell_avoids_lines (F : Finset (ℝ × ℝ)) (T : Finset ℝ)
    (hT : crossingLevels F ⊆ T) (l r x : ℝ) (hgap : ConsecutiveLevels T l r)
    (hx : x ∈ Ioo l r) (f g : ℝ × ℝ) (hadj : AdjacentLines F f g x) :
    Disjoint (interior (stripCell l r f g))
      {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1} := by
  rw [interior_stripCell]
  apply Set.disjoint_left.mpr
  rintro p ⟨hl,hr,hf,hg⟩ ⟨k,hk,he⟩
  have ha := hadj.in_strip hT hgap hx ⟨hl,hr⟩
  rcases ha.2.2.2 k hk with h | h <;> linarith

/-- A witness in the annulus selects a whole adjacent closed cell. The
frontiers are subsets of the supporting lines, so neither can cut its interior. -/
theorem adjacentCell_subset_annulus (D R : Set (ℝ × ℝ))
    (hD : IsClosed D) (hR : IsClosed R) (F : Finset (ℝ × ℝ)) (T : Finset ℝ)
    (hT : crossingLevels F ⊆ T)
    (hfrontD : frontier D ⊆ {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1})
    (hfrontR : frontier R ⊆ {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1})
    (l r x : ℝ) (hgap : ConsecutiveLevels T l r) (hx : x ∈ Ioo l r)
    (f g : ℝ × ℝ) (hadj : AdjacentLines F f g x)
    (hw : (interior (stripCell l r f g) ∩ (interior R \ D)).Nonempty) :
    stripCell l r f g ⊆ R \ interior D := by
  have hav := adjacentCell_avoids_lines F T hT l r x hgap hx f g hadj
  have hconn := (convex_stripCell l r f g).interior.isPreconnected
  have hreg := stripCell_regular l r x f g hx hadj.2.2.1
  have hex := regularCell_exterior D (stripCell l r f g) hD hreg hconn
    (hav.mono_right hfrontD) (by rcases hw with ⟨p,hp,_,hpd⟩; exact ⟨p,hp,hpd⟩)
  have hin : interior (stripCell l r f g) ⊆ interior R := by
    rcases band_side R (interior (stripCell l r f g)) hR hconn
      (hav.mono_right hfrontR) with h | h
    · exact h
    · rcases hw with ⟨p,hp,hpr,_⟩
      exact False.elim (h hp (interior_subset hpr))
  have hsubR : stripCell l r f g ⊆ R := by
    rw [← hreg]
    exact closure_minimal (hin.trans interior_subset) hR
  exact fun p hp ↦ ⟨hsubR hp,hex hp⟩

/-- Finite choices of two critical levels and two supporting lines. -/
abbrev StripIndex (T : Finset ℝ) (F : Finset (ℝ × ℝ)) := T × T × F × F

def indexCell {T : Finset ℝ} {F : Finset (ℝ × ℝ)} (c : StripIndex T F) : Set (ℝ × ℝ) :=
  stripCell c.1 c.2.1 c.2.2.1 c.2.2.2

/-- Selected cells have consecutive horizontal levels, consecutive supporting
lines, and one interior witness in the open annulus. All data are finite. -/
def SelectedCell (D R : Set (ℝ × ℝ)) (T : Finset ℝ) (F : Finset (ℝ × ℝ)) :=
  {c : StripIndex T F // ConsecutiveLevels T c.1 c.2.1 ∧
    AdjacentLines F c.2.2.1 c.2.2.2 ((c.1+c.2.1)/2) ∧
    (interior (indexCell c) ∩ (interior R \ D)).Nonempty}

instance selectedCell_finite (D R : Set (ℝ × ℝ)) (T : Finset ℝ) (F : Finset (ℝ × ℝ)) :
    Finite (SelectedCell D R T F) := inferInstanceAs (Finite {_c : StripIndex T F // _})

/-- The finite arrangement cells cover exactly the closed exterior annulus.
The two bracketing hypotheses mean that the critical levels and supporting lines
include those of the enclosing rectangle. -/
theorem selectedCells_cover (D R : Set (ℝ × ℝ))
    (hD : IsClosed D) (hR : IsClosed R) (hregR : closure (interior R) = R)
    (hcontain : D ⊆ interior R) (T : Finset ℝ) (F : Finset (ℝ × ℝ))
    (hT : crossingLevels F ⊆ T)
    (hfrontD : frontier D ⊆ {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1})
    (hfrontR : frontier R ⊆ {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1})
    (hlevels : ∀ p ∈ interior R,
      (∃ l ∈ T, l < p.1) ∧ (∃ r ∈ T, p.1 < r))
    (hheights : ∀ p ∈ interior R,
      (∃ f ∈ F, lineHeight f p.1 < p.2) ∧ (∃ g ∈ F, p.2 < lineHeight g p.1)) :
    (⋃ c : SelectedCell D R T F, indexCell c.val) = R \ interior D := by
  apply annulus_finite_closed_cover D R
    {p : ℝ × ℝ | p.1 ∉ T ∧ ∀ f ∈ F, p.2 ≠ lineHeight f p.1}
    (fun c : SelectedCell D R T F ↦ indexCell c.val)
    hD hR hregR hcontain (arrangement_generic_dense T F)
  · intro c
    exact isClosed_stripCell _ _ _ _
  · intro c
    have hm : ((c.val.1 : ℝ)+(c.val.2.1 : ℝ))/2 ∈
        Ioo (c.val.1 : ℝ) (c.val.2.1 : ℝ) := by
      constructor <;> linarith [c.property.1.2.2.1]
    exact adjacentCell_subset_annulus D R hD hR F T hT hfrontD hfrontR
      _ _ _ c.property.1 hm _ _ c.property.2.1 c.property.2.2
  · rintro p ⟨⟨hpR,hpD⟩,hpT,hpF⟩
    obtain ⟨l,r,hgap,hpl,hpr⟩ := exists_consecutiveLevels T p.1 hpT
      (hlevels p hpR).1 (hlevels p hpR).2
    obtain ⟨f,g,hadj,hpf,hpg⟩ := exists_adjacentLines F p.1 p.2 hpF
      (hheights p hpR).1 (hheights p hpR).2
    let c : StripIndex T F := ⟨⟨l,hgap.1⟩,⟨r,hgap.2.1⟩,⟨f,hadj.1⟩,⟨g,hadj.2.1⟩⟩
    have hm : (l+r)/2 ∈ Ioo l r := by constructor <;> linarith [hgap.2.2.1]
    have hpc : p ∈ interior (indexCell c) := by
      change p ∈ interior (stripCell l r f g)
      rw [interior_stripCell]
      exact ⟨hpl,hpr,hpf,hpg⟩
    let sc : SelectedCell D R T F := ⟨c,hgap,
      hadj.in_strip hT hgap ⟨hpl,hpr⟩ hm,⟨p,hpc,hpR,hpD⟩⟩
    exact mem_iUnion.mpr ⟨sc,interior_subset hpc⟩

lemma lineHeight_blend (f : ℝ × ℝ) (l r u : ℝ) :
    lineHeight f (l+(r-l)*u) = (1-u)*lineHeight f l+u*lineHeight f r := by
  unfold lineHeight
  ring

/-- The literal cell inequalities agree with the normalized four-corner band. -/
theorem stripCell_eq_stretchedBand (l r : ℝ) (hlr : l < r) (f g : ℝ × ℝ) :
    stripCell l r f g = horizontalStretch l r ''
      closedBand (lineHeight f l) (lineHeight f r) (lineHeight g l) (lineHeight g r) := by
  ext p
  constructor
  · rintro ⟨hl,hr,hf,hg⟩
    let u := (p.1-l)/(r-l)
    have hcoord : l+(r-l)*u = p.1 := by
      dsimp [u]
      rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hlr.ne')]
      ring
    have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hl) (sub_pos.mpr hlr).le
    have hu1 : u ≤ 1 := (div_le_one (sub_pos.mpr hlr)).mpr (by linarith)
    refine ⟨(u,p.2),⟨hu0,hu1,?_,?_⟩,?_⟩
    · rw [← lineHeight_blend,hcoord]
      exact hf
    · rw [← lineHeight_blend,hcoord]
      exact hg
    · change (l+(r-l)*u,p.2) = p
      exact Prod.ext hcoord rfl
  · rintro ⟨q,⟨hq0,hq1,hf,hg⟩,rfl⟩
    change l ≤ l+(r-l)*q.1 ∧ l+(r-l)*q.1 ≤ r ∧
      lineHeight f (l+(r-l)*q.1) ≤ q.2 ∧ q.2 ≤ lineHeight g (l+(r-l)*q.1)
    rw [lineHeight_blend,lineHeight_blend]
    exact ⟨by nlinarith [mul_nonneg (sub_pos.mpr hlr).le hq0],
      by nlinarith [mul_nonneg (sub_pos.mpr hlr).le (sub_nonneg.mpr hq1)],hf,hg⟩

/-- Every arrangement cell is the union of its two diagonal triangles. -/
theorem stripCell_two_triangles (l r : ℝ) (hlr : l < r) (f g : ℝ × ℝ)
    (hl : lineHeight f l ≤ lineHeight g l) (hr : lineHeight f r ≤ lineHeight g r) :
    stripCell l r f g =
      convexHull ℝ {(l,lineHeight f l),(r,lineHeight f r),(r,lineHeight g r)} ∪
      convexHull ℝ {(l,lineHeight f l),(r,lineHeight g r),(l,lineHeight g l)} := by
  rw [stripCell_eq_stretchedBand l r hlr]
  exact stretchedBand_two_triangles l r _ _ _ _ hl hr

/-- The only common points of the two cell triangles lie on the chosen diagonal. -/
theorem stripCell_triangles_inter (l r : ℝ) (hlr : l < r) (f g : ℝ × ℝ)
    (hl : lineHeight f l ≤ lineHeight g l) (hr : lineHeight f r ≤ lineHeight g r) :
    convexHull ℝ {(l,lineHeight f l),(r,lineHeight f r),(r,lineHeight g r)} ∩
      convexHull ℝ {(l,lineHeight f l),(r,lineHeight g r),(l,lineHeight g l)} =
      segment ℝ (l,lineHeight f l) (r,lineHeight g r) :=
  stretchedBand_triangles_inter l r _ _ _ _ hlr hl hr

/-- A cell cannot have both vertical sides collapsed if the lines are strictly
ordered at an interior coordinate. -/
lemma stripCell_noncollapsed_side (l r x : ℝ) (hlr : l < r) (f g : ℝ × ℝ)
    (hl : lineHeight f l ≤ lineHeight g l) (hr : lineHeight f r ≤ lineHeight g r)
    (hx : lineHeight f x < lineHeight g x) :
    lineHeight f l < lineHeight g l ∨ lineHeight f r < lineHeight g r := by
  by_contra h
  push Not at h
  have he1 := le_antisymm hl h.1
  have he2 := le_antisymm hr h.2
  have hfg : f = g := by
    apply Prod.ext
    · unfold lineHeight at he1 he2
      have he : (f.1-g.1)*(r-l) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hlr.ne'))
    · unfold lineHeight at he1 he2
      have he : (f.1-g.1)*(r-l) = 0 := by nlinarith
      have hs := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hlr.ne'))
      rw [hs] at he1
      linarith
  subst g
  exact hx.false

lemma strip_lowerTriangle_affineIndependent (l r a b d : ℝ) (hlr : l ≠ r) (hbd : b ≠ d) :
    AffineIndependent ℝ ![(l,a),(r,b),(r,d)] := by
  apply affineIndependent_of_ne_of_notMem_of_mem_of_mem (s := verticalLine r)
  · intro h; exact hbd (congrArg Prod.snd h)
  · exact hlr
  · rfl
  · rfl

lemma strip_upperTriangle_affineIndependent (l r a c d : ℝ) (hlr : l ≠ r) (hac : a ≠ c) :
    AffineIndependent ℝ ![(l,a),(r,d),(l,c)] := by
  apply affineIndependent_of_ne_of_mem_of_notMem_of_mem (s := verticalLine l)
  · intro h; exact hac (congrArg Prod.snd h)
  · rfl
  · exact hlr.symm
  · rfl

/-- The two ordered vertex triples of a strip-cell triangulation. -/
def cellTriangle (l r : ℝ) (f g : ℝ × ℝ) (side : Bool) : Fin 3 → ℝ × ℝ :=
  if side then ![(l,lineHeight f l),(r,lineHeight g r),(l,lineHeight g l)]
  else ![(l,lineHeight f l),(r,lineHeight f r),(r,lineHeight g r)]

def cellTriangleNondegenerate (l r : ℝ) (f g : ℝ × ℝ) (side : Bool) : Prop :=
  if side then lineHeight f l < lineHeight g l else lineHeight f r < lineHeight g r

lemma cellTriangle_independent (l r : ℝ) (hlr : l < r) (f g : ℝ × ℝ) (side : Bool)
    (h : cellTriangleNondegenerate l r f g side) :
    AffineIndependent ℝ (cellTriangle l r f g side) := by
  cases side
  · exact strip_lowerTriangle_affineIndependent l r _ _ _ hlr.ne (show _ < _ from h).ne
  · exact strip_upperTriangle_affineIndependent l r _ _ _ hlr.ne (show _ < _ from h).ne

lemma cellTriangle_range_false (l r : ℝ) (f g : ℝ × ℝ) :
    range (cellTriangle l r f g false) =
      {(l,lineHeight f l),(r,lineHeight f r),(r,lineHeight g r)} := by
  ext p
  simp [cellTriangle,Matrix.range_cons,Matrix.range_empty,or_comm,or_assoc]

lemma cellTriangle_range_true (l r : ℝ) (f g : ℝ × ℝ) :
    range (cellTriangle l r f g true) =
      {(l,lineHeight f l),(r,lineHeight g r),(l,lineHeight g l)} := by
  ext p
  simp [cellTriangle,Matrix.range_cons,Matrix.range_empty,or_comm,or_left_comm]

/-- Degenerate cell triangles are omitted: their segments already lie in the
other triangle. This yields a cover entirely by genuine two-simplices. -/
theorem stripCell_nondegenerate_triangles (l r x : ℝ) (hlr : l < r) (f g : ℝ × ℝ)
    (hl : lineHeight f l ≤ lineHeight g l) (hr : lineHeight f r ≤ lineHeight g r)
    (hx : lineHeight f x < lineHeight g x) :
    stripCell l r f g =
      ⋃ side : {b : Bool // cellTriangleNondegenerate l r f g b},
        convexHull ℝ (range (cellTriangle l r f g side.val)) := by
  have hunion := stripCell_two_triangles l r hlr f g hl hr
  have hside := stripCell_noncollapsed_side l r x hlr f g hl hr hx
  apply subset_antisymm
  · intro p hp
    rw [hunion] at hp
    rcases hp with hp | hp
    · by_cases hright : lineHeight f r < lineHeight g r
      · apply mem_iUnion.mpr
        refine ⟨⟨false,hright⟩,?_⟩
        rwa [cellTriangle_range_false]
      · have he : lineHeight f r = lineHeight g r := le_antisymm hr (le_of_not_gt hright)
        have hleft := hside.resolve_right hright
        apply mem_iUnion.mpr
        refine ⟨⟨true,hleft⟩,?_⟩
        rw [cellTriangle_range_true]
        apply convexHull_mono (s := {(l,lineHeight f l),(r,lineHeight f r),(r,lineHeight g r)}) _ hp
        rw [he]
        intro q hq
        simp only [mem_insert_iff,mem_singleton_iff] at hq ⊢
        tauto
    · by_cases hleft : lineHeight f l < lineHeight g l
      · apply mem_iUnion.mpr
        refine ⟨⟨true,hleft⟩,?_⟩
        rwa [cellTriangle_range_true]
      · have he : lineHeight f l = lineHeight g l := le_antisymm hl (le_of_not_gt hleft)
        have hright := hside.resolve_left hleft
        apply mem_iUnion.mpr
        refine ⟨⟨false,hright⟩,?_⟩
        rw [cellTriangle_range_false]
        apply convexHull_mono (s := {(l,lineHeight f l),(r,lineHeight g r),(l,lineHeight g l)}) _ hp
        rw [he]
        intro q hq
        simp only [mem_insert_iff,mem_singleton_iff] at hq ⊢
        tauto
  · intro p hp
    obtain ⟨side,hp⟩ := mem_iUnion.mp hp
    rw [hunion]
    cases h : side.val
    · left
      rw [h,cellTriangle_range_false] at hp
      exact hp
    · right
      rw [h,cellTriangle_range_true] at hp
      exact hp

/-- A selected cell and one of its genuine diagonal triangles. -/
def SelectedTriangle (D R : Set (ℝ × ℝ)) (T : Finset ℝ) (F : Finset (ℝ × ℝ)) :=
  {cb : SelectedCell D R T F × Bool // cellTriangleNondegenerate
    cb.1.val.1 cb.1.val.2.1 cb.1.val.2.2.1 cb.1.val.2.2.2 cb.2}

instance selectedTriangle_finite (D R : Set (ℝ × ℝ)) (T : Finset ℝ) (F : Finset (ℝ × ℝ)) :
    Finite (SelectedTriangle D R T F) := inferInstanceAs (Finite {_cb : SelectedCell D R T F × Bool // _})

def selectedTriangleVertices {D R : Set (ℝ × ℝ)} {T : Finset ℝ} {F : Finset (ℝ × ℝ)}
    (s : SelectedTriangle D R T F) : Fin 3 → ℝ × ℝ :=
  cellTriangle s.val.1.val.1 s.val.1.val.2.1 s.val.1.val.2.2.1 s.val.1.val.2.2.2 s.val.2

lemma selectedTriangle_independent {D R : Set (ℝ × ℝ)} {T : Finset ℝ} {F : Finset (ℝ × ℝ)}
    (s : SelectedTriangle D R T F) : AffineIndependent ℝ (selectedTriangleVertices s) :=
  cellTriangle_independent _ _ s.val.1.property.1.2.2.1 _ _ _ s.property

/-- Replacing every selected cell by its genuine triangles preserves the union. -/
theorem selectedTriangle_union (D R : Set (ℝ × ℝ)) (T : Finset ℝ) (F : Finset (ℝ × ℝ))
    (hT : crossingLevels F ⊆ T) :
    (⋃ s : SelectedTriangle D R T F, convexHull ℝ (range (selectedTriangleVertices s))) =
      ⋃ c : SelectedCell D R T F, indexCell c.val := by
  have heq (c : SelectedCell D R T F) :
      indexCell c.val = ⋃ b : {b : Bool // cellTriangleNondegenerate
          c.val.1 c.val.2.1 c.val.2.2.1 c.val.2.2.2 b},
        convexHull ℝ (range (cellTriangle c.val.1 c.val.2.1 c.val.2.2.1 c.val.2.2.2 b.val)) := by
    have hm : ((c.val.1 : ℝ)+(c.val.2.1 : ℝ))/2 ∈ Ioo (c.val.1 : ℝ) (c.val.2.1 : ℝ) := by
      constructor <;> linarith [c.property.1.2.2.1]
    have horder := lineHeight_order_in_strip F T hT _ _ _ c.property.1 hm
      _ _ c.property.2.1.1 c.property.2.1.2.1 c.property.2.1.2.2.1
    have hep := lineHeight_order_endpoints _ _ _ _ c.property.1.2.2.1 horder
    exact stripCell_nondegenerate_triangles _ _ _ c.property.1.2.2.1
      _ _ hep.1 hep.2 c.property.2.1.2.2.1
  ext p
  constructor
  · intro hp
    obtain ⟨s,hs⟩ := mem_iUnion.mp hp
    apply mem_iUnion.mpr
    refine ⟨s.val.1,?_⟩
    rw [heq]
    exact mem_iUnion.mpr ⟨⟨s.val.2,s.property⟩,hs⟩
  · intro hp
    obtain ⟨c,hc⟩ := mem_iUnion.mp hp
    rw [heq] at hc
    obtain ⟨b,hb⟩ := mem_iUnion.mp hc
    exact mem_iUnion.mpr ⟨⟨(c,b.val),b.property⟩,hb⟩

/-- Interior points admit small vertical displacements in both directions. -/
lemma interior_vertical_perturb (R : Set (ℝ × ℝ)) (p : ℝ × ℝ) (hp : p ∈ interior R) :
    (∃ y < p.2, (p.1,y) ∈ interior R) ∧ (∃ y > p.2, (p.1,y) ∈ interior R) := by
  have ho : IsOpen ((fun y : ℝ ↦ (p.1,y)) ⁻¹' interior R) :=
    isOpen_interior.preimage (by fun_prop)
  have hm : p.2 ∈ (fun y : ℝ ↦ (p.1,y)) ⁻¹' interior R := hp
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hm)
  exact ⟨⟨(a+p.2)/2,by linarith [hab.1],hsub ⟨by linarith [hab.1],by linarith [hab.1,hab.2]⟩⟩,
    ⟨(p.2+b)/2,by linarith [hab.2],hsub ⟨by linarith [hab.1,hab.2],by linarith [hab.2]⟩⟩⟩

/-- The vertical fiber of a compact planar region has frontier points above
and below each interior point. These supply the bounding supporting lines. -/
theorem compact_frontier_height_bracketing (R : Set (ℝ × ℝ)) (hR : IsCompact R)
    (p : ℝ × ℝ) (hp : p ∈ interior R) :
    (∃ q ∈ frontier R, q.1 = p.1 ∧ q.2 < p.2) ∧
      (∃ q ∈ frontier R, q.1 = p.1 ∧ p.2 < q.2) := by
  let S := R ∩ {q : ℝ × ℝ | q.1 = p.1}
  have hS : IsCompact S := hR.inter_right (isClosed_eq continuous_fst continuous_const)
  have hSn : S.Nonempty := ⟨p,interior_subset hp,rfl⟩
  obtain ⟨lo,hlo,hmin⟩ := hS.exists_isMinOn hSn continuous_snd.continuousOn
  obtain ⟨hi,hhi,hmax⟩ := hS.exists_isMaxOn hSn continuous_snd.continuousOn
  have hloF : lo ∈ frontier R := by
    rw [frontier,hR.isClosed.closure_eq]
    refine ⟨hlo.1,?_⟩
    intro h
    obtain ⟨y,hy,hyR⟩ := (interior_vertical_perturb R lo h).1
    have hm := hmin (show (lo.1,y) ∈ S from ⟨interior_subset hyR,hlo.2⟩)
    exact hy.not_ge hm
  have hhiF : hi ∈ frontier R := by
    rw [frontier,hR.isClosed.closure_eq]
    refine ⟨hhi.1,?_⟩
    intro h
    obtain ⟨y,hy,hyR⟩ := (interior_vertical_perturb R hi h).2
    have hm := hmax (show (hi.1,y) ∈ S from ⟨interior_subset hyR,hhi.2⟩)
    exact hy.not_ge hm
  obtain ⟨ylo,hylo,hyloR⟩ := (interior_vertical_perturb R p hp).1
  obtain ⟨yhi,hyhi,hyhiR⟩ := (interior_vertical_perturb R p hp).2
  exact ⟨⟨lo,hloF,hlo.2,(hmin (show (p.1,ylo) ∈ S from ⟨interior_subset hyloR,rfl⟩)).trans_lt hylo⟩,
    ⟨hi,hhiF,hhi.2,hyhi.trans_le (hmax (show (p.1,yhi) ∈ S from ⟨interior_subset hyhiR,rfl⟩))⟩⟩

/-- Covering the frontier of a compact region by finitely many nonvertical
lines automatically brackets every interior point by two line heights. -/
theorem compact_supporting_heights_bracket (R : Set (ℝ × ℝ)) (hR : IsCompact R)
    (F : Finset (ℝ × ℝ))
    (hfront : frontier R ⊆ {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1})
    (p : ℝ × ℝ) (hp : p ∈ interior R) :
    (∃ f ∈ F, lineHeight f p.1 < p.2) ∧ (∃ g ∈ F, p.2 < lineHeight g p.1) := by
  obtain ⟨⟨lo,hlo,hlox,hloy⟩,⟨hi,hhi,hhix,hhiy⟩⟩ := compact_frontier_height_bracketing R hR p hp
  obtain ⟨f,hf,hfe⟩ := hfront hlo
  obtain ⟨g,hg,hge⟩ := hfront hhi
  refine ⟨⟨f,hf,?_⟩,⟨g,hg,?_⟩⟩
  · rw [hlox] at hfe
    rwa [← hfe]
  · rw [hhix] at hge
    rwa [← hge]

/-- A finite critical set can include every crossing and strictly bracket a
compact region's horizontal projection. -/
theorem exists_bracketing_levels (R : Set (ℝ × ℝ)) (hR : IsCompact R)
    (F : Finset (ℝ × ℝ)) :
    ∃ T : Finset ℝ, crossingLevels F ⊆ T ∧ ∀ p ∈ R,
      (∃ l ∈ T, l < p.1) ∧ (∃ r ∈ T, p.1 < r) := by
  classical
  obtain ⟨lo,hlo⟩ := hR.bddBelow_image continuous_fst.continuousOn
  obtain ⟨hi,hhi⟩ := hR.bddAbove_image continuous_fst.continuousOn
  let T := insert (lo-1) (insert (hi+1) (crossingLevels F))
  refine ⟨T,?_,?_⟩
  · intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  · intro p hp
    have hl := hlo (mem_image_of_mem Prod.fst hp)
    have hr := hhi (mem_image_of_mem Prod.fst hp)
    exact ⟨⟨lo-1,Finset.mem_insert_self _ _,by linarith⟩,
      ⟨hi+1,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),by linarith⟩⟩

/-- A compact regular planar region with a closed hole strictly inside and
finitely many nonvertical supporting lines admits the concrete finite
nondegenerate triangle cover constructed above. -/
theorem compact_polygonal_annulus_triangle_cover (D R : Set (ℝ × ℝ))
    (hD : IsClosed D) (hR : IsCompact R) (hregR : closure (interior R) = R)
    (hcontain : D ⊆ interior R) (F : Finset (ℝ × ℝ))
    (hfrontD : frontier D ⊆ {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1})
    (hfrontR : frontier R ⊆ {p : ℝ × ℝ | ∃ k ∈ F, p.2 = lineHeight k p.1}) :
    ∃ T : Finset ℝ, crossingLevels F ⊆ T ∧
      (⋃ s : SelectedTriangle D R T F, convexHull ℝ (range (selectedTriangleVertices s))) =
        R \ interior D := by
  obtain ⟨T,hT,hlevels⟩ := exists_bracketing_levels R hR F
  refine ⟨T,hT,?_⟩
  rw [selectedTriangle_union D R T F hT]
  exact selectedCells_cover D R hD hR.isClosed hregR hcontain T F hT hfrontD hfrontR
    (fun p hp ↦ hlevels p (interior_subset hp))
    (compact_supporting_heights_bracket R hR F hfrontR)

/-- Two gaps of a finite ordered set either coincide or have disjoint interiors. -/
lemma ConsecutiveLevels.separated_or_eq {T : Finset ℝ} {l r l' r' : ℝ}
    (h : ConsecutiveLevels T l r) (h' : ConsecutiveLevels T l' r') :
    (l = l' ∧ r = r') ∨ r ≤ l' ∨ r' ≤ l := by
  rcases lt_trichotomy l l' with hll | hll | hll
  · rcases h.2.2.2 l' h'.1 with he | he
    · exact False.elim (hll.not_ge he)
    · exact Or.inr (Or.inl he)
  · left
    refine ⟨hll,?_⟩
    apply le_antisymm
    · rcases h.2.2.2 r' h'.2.1 with he | he
      · exact False.elim (by linarith [h'.2.2.1])
      · exact he
    · rcases h'.2.2.2 r h.2.1 with he | he
      · exact False.elim (by linarith [h.2.2.1])
      · exact he
  · rcases h'.2.2.2 l h.1 with he | he
    · exact False.elim (hll.not_ge he)
    · exact Or.inr (Or.inr he)

lemma AdjacentLines.heightGap {F : Finset (ℝ × ℝ)} {f g : ℝ × ℝ} {x : ℝ}
    (h : AdjacentLines F f g x) :
    ConsecutiveLevels (F.image (fun k ↦ lineHeight k x)) (lineHeight f x) (lineHeight g x) := by
  classical
  refine ⟨Finset.mem_image.mpr ⟨f,h.1,rfl⟩,Finset.mem_image.mpr ⟨g,h.2.1,rfl⟩,h.2.2.1,?_⟩
  rintro u hu
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hu
  exact h.2.2.2 k hk

/-- At either endpoint of a strip no supporting-line vertex lies strictly
inside a vertical cell side. This is the absence of unmatched side vertices. -/
theorem adjacentLines_endpoint_gap (F : Finset (ℝ × ℝ)) (T : Finset ℝ)
    (hT : crossingLevels F ⊆ T) (l r x : ℝ) (hgap : ConsecutiveLevels T l r)
    (hx : x ∈ Ioo l r) (f g : ℝ × ℝ) (hadj : AdjacentLines F f g x)
    (u : ℝ) (hu : u ∈ Icc l r) (k : ℝ × ℝ) (hk : k ∈ F) :
    lineHeight k u ≤ lineHeight f u ∨ lineHeight g u ≤ lineHeight k u := by
  have hclosed : IsClosed {z | lineHeight k z ≤ lineHeight f z ∨
      lineHeight g z ≤ lineHeight k z} :=
    (isClosed_le (continuous_lineHeight k) (continuous_lineHeight f)).union
      (isClosed_le (continuous_lineHeight g) (continuous_lineHeight k))
  have hsub : Ioo l r ⊆ {z | lineHeight k z ≤ lineHeight f z ∨
      lineHeight g z ≤ lineHeight k z} := by
    intro z hz
    exact (hadj.in_strip hT hgap hx hz).2.2.2 k hk
  have hc := closure_minimal hsub hclosed
  rw [closure_Ioo hgap.2.2.1.ne] at hc
  exact hc hu

/-- Distinct selected cells have disjoint planar interiors. -/
theorem selectedCell_interiors_disjoint (D R : Set (ℝ × ℝ)) (T : Finset ℝ)
    (F : Finset (ℝ × ℝ)) (hT : crossingLevels F ⊆ T)
    (c d : SelectedCell D R T F) (hcd : c ≠ d) :
    Disjoint (interior (indexCell c.val)) (interior (indexCell d.val)) := by
  apply Set.disjoint_left.mpr
  intro p hpc hpd
  change p ∈ interior (stripCell _ _ _ _) at hpc hpd
  rw [interior_stripCell] at hpc hpd
  rcases c.property.1.separated_or_eq d.property.1 with ⟨hl,hr⟩ | hsep | hsep
  · have hmc : ((c.val.1 : ℝ)+(c.val.2.1 : ℝ))/2 ∈ Ioo (c.val.1 : ℝ) (c.val.2.1 : ℝ) := by
      constructor <;> linarith [c.property.1.2.2.1]
    have hmd : ((d.val.1 : ℝ)+(d.val.2.1 : ℝ))/2 ∈ Ioo (d.val.1 : ℝ) (d.val.2.1 : ℝ) := by
      constructor <;> linarith [d.property.1.2.2.1]
    have hca := c.property.2.1.in_strip hT c.property.1 hmc ⟨hpc.1,hpc.2.1⟩
    have hda := d.property.2.1.in_strip hT d.property.1 hmd ⟨hpd.1,hpd.2.1⟩
    rcases hca.heightGap.separated_or_eq hda.heightGap with ⟨hfl,hfr⟩ | hsep | hsep
    · have hnot : p.1 ∉ crossingLevels F := fun h ↦ c.property.1.not_mem ⟨hpc.1,hpc.2.1⟩ (hT h)
      have hf : (c.val.2.2.1 : ℝ × ℝ) = d.val.2.2.1 := by
        by_contra hn
        exact lineHeight_ne_of_not_crossing F _ _ c.val.2.2.1.property d.val.2.2.1.property hn _ hnot hfl
      have hg : (c.val.2.2.2 : ℝ × ℝ) = d.val.2.2.2 := by
        by_contra hn
        exact lineHeight_ne_of_not_crossing F _ _ c.val.2.2.2.property d.val.2.2.2.property hn _ hnot hfr
      apply hcd
      apply Subtype.ext
      exact Prod.ext (Subtype.ext hl) (Prod.ext (Subtype.ext hr)
        (Prod.ext (Subtype.ext hf) (Subtype.ext hg)))
    · linarith [hpc.2.2.2,hpd.2.2.1]
    · linarith [hpd.2.2.2,hpc.2.2.1]
  · linarith [hpc.2.1,hpd.1]
  · linarith [hpd.2.1,hpc.1]

open scoped BigOperators in
/-- A supporting hyperplane cuts the convex hull of finitely many vertices in
exactly the hull of the vertices on that hyperplane. -/
theorem finiteHull_supporting_face {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Finset E) (L : E →ₗ[ℝ] ℝ) (c : ℝ) (hS : ∀ y ∈ S, L y ≤ c) :
    convexHull ℝ (S : Set E) ∩ {x | L x = c} =
      convexHull ℝ ((S : Set E) ∩ {x | L x = c}) := by
  classical
  let U := S.filter (fun y ↦ L y = c)
  have hU : (U : Set E) = (S : Set E) ∩ {x | L x = c} := by ext y; simp [U]
  rw [← hU]
  apply subset_antisymm
  · rintro x ⟨hx,hxc⟩
    change L x = c at hxc
    obtain ⟨w,hw0,hw1,hwx⟩ := Finset.mem_convexHull'.mp hx
    have hwL : ∑ y ∈ S, w y * L y = c := by
      have h := congrArg L hwx
      simpa only [map_sum,map_smul,smul_eq_mul,hxc] using h
    have hsum : ∑ y ∈ S, w y * (c-L y) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib,← Finset.sum_mul,hw1,hwL]
      ring
    have hz : ∀ y ∈ S, L y ≠ c → w y = 0 := by
      intro y hy hne
      have hm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun z hz ↦ mul_nonneg (hw0 z hz) (sub_nonneg.mpr (hS z hz)))).mp hsum y hy
      exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hne.symm)
    refine Finset.mem_convexHull'.mpr ⟨w,?_,?_,?_⟩
    · intro y hy
      exact hw0 y (Finset.mem_filter.mp hy).1
    · calc
        ∑ y ∈ U, w y = ∑ y ∈ S, w y := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro y hy hn
          apply hz y hy
          exact fun he ↦ hn (Finset.mem_filter.mpr ⟨hy,he⟩)
        _ = 1 := hw1
    · calc
        ∑ y ∈ U, w y • y = ∑ y ∈ S, w y • y := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro y hy hn
          rw [hz y hy (fun he ↦ hn (Finset.mem_filter.mpr ⟨hy,he⟩)),zero_smul]
        _ = x := hwx
  · intro x hx
    refine ⟨convexHull_mono (show (U : Set E) ⊆ (S : Set E) from
      fun y hy ↦ (Finset.mem_filter.mp hy).1) hx,?_⟩
    have hc : Convex ℝ {x : E | L x = c} := by
      intro y hy z hz a b ha hb hab
      change L (a • y+b • z) = c
      rw [map_add,map_smul,map_smul]
      change a*L y+b*L z = c
      rw [show L y = c from hy,show L z = c from hz,← add_mul,hab,one_mul]
    exact (convexHull_min (fun y hy ↦ (Finset.mem_filter.mp hy).2) hc) hx

/-- The affine graph coefficient of a projected nonvertical segment, with
endpoints swapped when necessary. -/
def segmentLineCoeff (t : ℝ) (a b : Plane) : ℝ × ℝ :=
  if projection t a < projection t b then
    ( (a 1-b 1)/(projection t a-projection t b),
      a 1 - ((a 1-b 1)/(projection t a-projection t b))*projection t a )
  else
    ( (b 1-a 1)/(projection t b-projection t a),
      b 1 - ((b 1-a 1)/(projection t b-projection t a))*projection t b )

lemma segmentLineCoeff_graph (t : ℝ) (a b : Plane)
    (hab : projection t a ≠ projection t b) (x : Plane) (hx : x ∈ segment ℝ a b) :
    (shear t x).2 = lineHeight (segmentLineCoeff t a b) (shear t x).1 := by
  by_cases h : projection t a < projection t b
  · simp only [segmentLineCoeff, h, ↓reduceIte]
    have hh := (segment_graph t a b h x).1 hx
    have hh2 := hh.2
    convert hh2 using 1 <;> simp [shear, lineHeight, edgeHeight]; field_simp; ring
  · have hba : projection t b < projection t a := lt_of_le_of_ne
      (le_of_not_gt h) (Ne.symm hab)
    simp only [segmentLineCoeff, h, ↓reduceIte]
    have hx' : x ∈ segment ℝ b a := by simpa only [segment_symm ℝ a b] using hx
    have hh := (segment_graph t b a hba x).1 hx'
    have hh2 := hh.2
    convert hh2 using 1 <;> simp [shear, lineHeight, edgeHeight]; field_simp; ring

lemma segmentLineCoeff_mem (t : ℝ) (a b : Plane) (hab : projection t a ≠ projection t b) :
    ∀ x ∈ segment ℝ a b, ∃ f : ℝ × ℝ, f = segmentLineCoeff t a b ∧
      (shear t x).2 = lineHeight f (shear t x).1 := by
  intro x hx
  exact ⟨segmentLineCoeff t a b,rfl,segmentLineCoeff_graph t a b hab x hx⟩

/-- Supporting graph coefficients from a finite edge family. -/
def segmentLineCoeffs (t : ℝ) {ι : Type*} [Fintype ι]
    (a b : ι → Plane) : Finset (ℝ × ℝ) :=
  Finset.univ.image (fun i ↦ segmentLineCoeff t (a i) (b i))

lemma segmentLineCoeffs_support (t : ℝ) {ι : Type*} [Fintype ι]
    (a b : ι → Plane) (hproj : ∀ i, projection t (a i) ≠ projection t (b i))
    {x : Plane} (hx : x ∈ ⋃ i, segment ℝ (a i) (b i)) :
    ∃ f ∈ segmentLineCoeffs t a b, (shear t x).2 = lineHeight f (shear t x).1 := by
  rcases mem_iUnion.mp hx with ⟨i,hi⟩
  obtain ⟨f,hf0,hf⟩ := segmentLineCoeff_mem t (a i) (b i) (hproj i) x hi
  subst f
  exact ⟨segmentLineCoeff t (a i) (b i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hf⟩

/-- A sheared polygon with nonvertical edges has its entire boundary in the
finite family of supporting graphs. -/
theorem polygon_supporting_lines (t : ℝ) {n : ℕ} (P : Polygon Plane n)
    (hproj : ∀ i, projection t (P i) ≠ projection t (P (finRotate n i))) :
    shear t '' P.boundary ℝ ⊆
      {q : ℝ × ℝ | ∃ f ∈ segmentLineCoeffs t P (fun i ↦ P (finRotate n i)),
        q.2 = lineHeight f q.1} := by
  rintro q ⟨x,hx,rfl⟩
  apply segmentLineCoeffs_support t P (fun i ↦ P (finRotate n i)) hproj
  simpa only [Polygon.boundary,Polygon.edgeSet,affineSegment_eq_segment] using hx

/-- The supporting family for the original polygon is also a supporting family
for the frontier of its sheared closed region. -/
theorem polygon_frontier_supporting_lines (t : ℝ) {n : ℕ} (P : Polygon Plane n)
    (D : Set Plane) (hfront : frontier D = P.boundary ℝ)
    (hproj : ∀ i, projection t (P i) ≠ projection t (P (finRotate n i))) :
    frontier (shear t '' D) ⊆
      {q : ℝ × ℝ | ∃ f ∈ segmentLineCoeffs t P (fun i ↦ P (finRotate n i)),
        q.2 = lineHeight f q.1} := by
  rw [← (shear t).image_frontier,hfront]
  exact polygon_supporting_lines t P hproj

/-- Horizontal segment parametrization in product coordinates. -/
lemma horizontalSegment_eq (a b y : ℝ) (hab : a ≤ b) :
    segment ℝ (a,y) (b,y) = Icc a b ×ˢ {y} := by
  let f : ℝ →ᵃ[ℝ] (ℝ × ℝ) := (AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ y)
  have h := image_segment ℝ f a b
  rw [segment_eq_Icc hab] at h
  change f '' Icc a b = segment ℝ (a,y) (b,y) at h
  rw [← h]
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,rfl⟩
  · rintro ⟨hx,hy⟩
    refine ⟨p.1,hx,?_⟩
    exact Prod.ext rfl (Set.mem_singleton_iff.mp hy).symm

lemma verticalSegment_eq (x a b : ℝ) (hab : a ≤ b) :
    segment ℝ (x,a) (x,b) = {x} ×ˢ Icc a b := by
  let f : ℝ →ᵃ[ℝ] (ℝ × ℝ) := (AffineMap.const ℝ ℝ x).prod (AffineMap.id ℝ ℝ)
  have h := image_segment ℝ f a b
  rw [segment_eq_Icc hab] at h
  change f '' Icc a b = segment ℝ (x,a) (x,b) at h
  rw [← h]
  ext p
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨rfl,hy⟩
  · rintro ⟨hx,hy⟩
    refine ⟨p.2,hy,?_⟩
    exact Prod.ext (Set.mem_singleton_iff.mp hx).symm rfl

/-- The literal rectangle frontier consists of its four closed sides. -/
theorem rectangle_frontier_segments (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    frontier (Icc a b ×ˢ Icc c d) =
      segment ℝ (a,c) (b,c) ∪ segment ℝ (a,d) (b,d) ∪
      segment ℝ (a,c) (a,d) ∪ segment ℝ (b,c) (b,d) := by
  rw [horizontalSegment_eq _ _ _ hab.le,horizontalSegment_eq _ _ _ hab.le,
    verticalSegment_eq _ _ _ hcd.le,verticalSegment_eq _ _ _ hcd.le,
    frontier,closure_prod_eq,isClosed_Icc.closure_eq,isClosed_Icc.closure_eq,
    interior_prod_eq,interior_Icc,interior_Icc]
  ext p
  simp only [mem_sdiff,mem_prod,mem_Icc,mem_Ioo,mem_union,mem_singleton_iff]
  constructor
  · rintro ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,hn⟩
    by_cases hpc : p.2 = c
    · exact Or.inl (Or.inl (Or.inl ⟨⟨ha,hb⟩,hpc⟩))
    by_cases hpd : p.2 = d
    · exact Or.inl (Or.inl (Or.inr ⟨⟨ha,hb⟩,hpd⟩))
    by_cases hpa : p.1 = a
    · exact Or.inl (Or.inr ⟨hpa,hc,hd⟩)
    by_cases hpb : p.1 = b
    · exact Or.inr ⟨hpb,hc,hd⟩
    exact False.elim (hn ⟨⟨lt_of_le_of_ne ha (Ne.symm hpa),lt_of_le_of_ne hb hpb⟩,
      lt_of_le_of_ne hc (Ne.symm hpc),lt_of_le_of_ne hd hpd⟩)
  · rintro (((⟨hx,hy⟩ | ⟨hx,hy⟩) | ⟨hx,hy⟩) | ⟨hx,hy⟩) <;>
      subst_vars <;> constructor <;> simp_all <;> linarith

/-- Product coordinates regarded as the Euclidean plane. -/
def planeCoordinates : (ℝ × ℝ) →ₗ[ℝ] Plane where
  toFun p := WithLp.toLp 2 ![p.1,p.2]
  map_add' p q := by apply PiLp.ext; intro i; fin_cases i <;> simp
  map_smul' a p := by apply PiLp.ext; intro i; fin_cases i <;> simp

lemma planeCoordinates_eq (p : ℝ × ℝ) : planeCoordinates p = (shear 0).symm p := by
  simp [planeCoordinates,shear]

lemma rectangle_coordinates_image (a b : Fin 2 → ℝ) :
    (shear 0).symm '' (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)) =
      {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩ i
    fin_cases i <;> simpa [shear] using (show a _ ≤ _ ∧ _ ≤ b _ from
      by first | exact hp.1 | exact hp.2)
  · intro hx
    refine ⟨(x 0,x 1),⟨hx 0,hx 1⟩,?_⟩
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [shear]

/-- The four transformed corners determine the complete rectangle frontier. -/
theorem affine_rectangle_frontier (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ)
    (hab : ∀ i, a i < b i) :
    frontier (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) =
      let p00 := e (planeCoordinates (a 0,a 1))
      let p10 := e (planeCoordinates (b 0,a 1))
      let p01 := e (planeCoordinates (a 0,b 1))
      let p11 := e (planeCoordinates (b 0,b 1))
      segment ℝ p00 p10 ∪ segment ℝ p01 p11 ∪ segment ℝ p00 p01 ∪ segment ℝ p10 p11 := by
  rw [← rectangle_coordinates_image a b,← Set.image_comp]
  let H := (shear 0).symm.trans e.toHomeomorph
  change frontier (H '' _) = _
  rw [← H.image_frontier,rectangle_frontier_segments _ _ _ _ (hab 0) (hab 1)]
  simp only [Set.image_union]
  have hs (p q : ℝ × ℝ) : H '' segment ℝ p q =
      segment ℝ (e (planeCoordinates p)) (e (planeCoordinates q)) := by
    let f := e.toAffineEquiv.toAffineMap.comp planeCoordinates.toAffineMap
    have hfun : (H : (ℝ × ℝ) → Plane) = f := by
      funext x
      exact congrArg e (planeCoordinates_eq x).symm
    rw [hfun]
    exact image_segment ℝ f p q
  rw [hs,hs,hs,hs]

def rectangleEdgeA (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ) : Fin 4 → Plane :=
  ![e (planeCoordinates (a 0,a 1)), e (planeCoordinates (a 0,b 1)),
    e (planeCoordinates (a 0,a 1)), e (planeCoordinates (b 0,a 1))]

def rectangleEdgeB (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ) : Fin 4 → Plane :=
  ![e (planeCoordinates (b 0,a 1)), e (planeCoordinates (b 0,b 1)),
    e (planeCoordinates (a 0,b 1)), e (planeCoordinates (b 0,b 1))]

lemma rectangle_frontier_edgeUnion (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ)
    (hab : ∀ i, a i < b i) :
    frontier (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) =
      ⋃ i, segment ℝ (rectangleEdgeA e a b i) (rectangleEdgeB e a b i) := by
  rw [affine_rectangle_frontier e a b hab]
  ext x
  simp [rectangleEdgeA,rectangleEdgeB,Fin.exists_fin_succ,or_assoc]

lemma affine_rectangle_compact (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ) :
    IsCompact (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) := by
  rw [← rectangle_coordinates_image a b]
  exact ((isCompact_Icc.prod isCompact_Icc).image (shear 0).symm.continuous).image e.continuous

lemma affine_rectangle_regular (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ)
    (hab : ∀ i, a i < b i) :
    closure (interior (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})) =
      e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
  rw [← rectangle_coordinates_image a b]
  change closure (interior (e.toHomeomorph '' ((shear 0).symm '' _))) = _
  rw [← e.toHomeomorph.image_interior,← e.toHomeomorph.image_closure,
    ← (shear 0).symm.image_interior,← (shear 0).symm.image_closure,
    interior_prod_eq,interior_Icc,interior_Icc,closure_prod_eq,
    closure_Ioo (hab 0).ne,closure_Ioo (hab 1).ne]
  rfl

/-- Both original boundary components yield a concrete finite supporting-line
family after a shear nonvertical on all their edges. -/
theorem annulus_supporting_family (t : ℝ) {n : ℕ} (P : Polygon Plane n)
    (D : Set Plane) (hfront : frontier D = P.boundary ℝ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ) (hab : ∀ i, a i < b i)
    (hprojP : ∀ i, projection t (P i) ≠ projection t (P (finRotate n i)))
    (hprojR : ∀ i, projection t (rectangleEdgeA e a b i) ≠ projection t (rectangleEdgeB e a b i)) :
    ∃ F : Finset (ℝ × ℝ),
      frontier (shear t '' D) ⊆ {q | ∃ f ∈ F, q.2 = lineHeight f q.1} ∧
      frontier (shear t '' (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})) ⊆
        {q | ∃ f ∈ F, q.2 = lineHeight f q.1} := by
  classical
  let FP := segmentLineCoeffs t P (fun i ↦ P (finRotate n i))
  let FR := segmentLineCoeffs t (rectangleEdgeA e a b) (rectangleEdgeB e a b)
  refine ⟨FP ∪ FR,?_,?_⟩
  · intro q hq
    obtain ⟨f,hf,he⟩ := polygon_frontier_supporting_lines t P D hfront hprojP hq
    exact ⟨f,Finset.mem_union_left _ hf,he⟩
  · rw [← (shear t).image_frontier,rectangle_frontier_edgeUnion e a b hab]
    rintro q ⟨x,hx,rfl⟩
    obtain ⟨f,hf,he⟩ := segmentLineCoeffs_support t (rectangleEdgeA e a b)
      (rectangleEdgeB e a b) hprojR hx
    exact ⟨f,Finset.mem_union_right _ hf,he⟩

lemma rectangle_edges_nondegenerate (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ)
    (hab : ∀ i, a i < b i) (i : Fin 4) : rectangleEdgeA e a b i ≠ rectangleEdgeB e a b i := by
  intro h
  fin_cases i <;> simp only [rectangleEdgeA,rectangleEdgeB,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk] at h
  all_goals
    have he := e.injective h
    have h0 := congrArg (fun x : Plane ↦ x 0) he
    have h1 := congrArg (fun x : Plane ↦ x 1) he
    simp [planeCoordinates] at h0 h1
    first | exact (hab 0).ne h0 | exact (hab 1).ne h1

lemma polygon_edges_nondegenerate {n : ℕ} (hn : 2 ≤ n) (P : Polygon Plane n)
    (hP : Function.Injective P) (i : Fin n) : P i ≠ P (finRotate n i) := by
  intro h
  have hi := hP h
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hv := congrArg Fin.val hi
  rw [coe_finRotate] at hv
  split_ifs at hv with he
  · have : i.val = k := congrArg Fin.val he
    omega
  · omega

/-- Generic projection can be chosen simultaneously for every polygon edge and
every side of the containing affine rectangle. -/
theorem exists_common_nondegenerate_shear {n : ℕ} (hn : 2 ≤ n) (P : Polygon Plane n)
    (hP : Function.Injective P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ)
    (hab : ∀ i, a i < b i) :
    ∃ t : ℝ,
      (∀ i, projection t (P i) ≠ projection t (P (finRotate n i))) ∧
      (∀ i, projection t (rectangleEdgeA e a b i) ≠ projection t (rectangleEdgeB e a b i)) := by
  let S := range P ∪ (range (rectangleEdgeA e a b) ∪ range (rectangleEdgeB e a b))
  have hS : S.Finite := (finite_range P).union
    ((finite_range (rectangleEdgeA e a b)).union (finite_range (rectangleEdgeB e a b)))
  obtain ⟨t,ht⟩ := exists_injective_plane_projection_of_finite hS
  have hsep (x y : Plane) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
      projection t x ≠ projection t y := by
    intro h
    exact hne (congrArg Subtype.val (ht (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h))
  refine ⟨t,?_,?_⟩
  · intro i
    exact hsep _ _ (Or.inl ⟨i,rfl⟩) (Or.inl ⟨finRotate n i,rfl⟩)
      (polygon_edges_nondegenerate hn P hP i)
  · intro i
    exact hsep _ _ (Or.inr (Or.inl ⟨i,rfl⟩)) (Or.inr (Or.inr ⟨i,rfl⟩))
      (rectangle_edges_nondegenerate e a b hab i)

/-- The original polygonal annulus admits a finite cover by genuine straight
triangles in explicitly chosen sheared coordinates. No arrangement or bracketing
hypothesis is added to the geometric input. -/
theorem polygonal_annulus_finite_triangle_cover (D R : Set Plane)
    (hD : IsClosed D)
    (hpolygon : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n,
      Function.Injective P ∧ frontier D = P.boundary ℝ)
    (hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧ R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})
    (hcontain : D ⊆ interior R) :
    ∃ (t : ℝ) (F : Finset (ℝ × ℝ)) (T : Finset ℝ),
      crossingLevels F ⊆ T ∧
      (⋃ s : SelectedTriangle (shear t '' D) (shear t '' R) T F,
        convexHull ℝ (range (selectedTriangleVertices s))) = shear t '' (R \ interior D) := by
  obtain ⟨n,hn,P,hP,hfront⟩ := hpolygon
  obtain ⟨e,a,b,hab,rfl⟩ := hrectangle
  obtain ⟨t,htP,htR⟩ := exists_common_nondegenerate_shear (by omega) P hP e a b hab
  obtain ⟨F,hFD,hFR⟩ := annulus_supporting_family t P D hfront e a b hab htP htR
  have hDc : IsClosed (shear t '' D) := (shear t).isClosed_image.mpr hD
  have hRc : IsCompact (shear t '' (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})) :=
    (affine_rectangle_compact e a b).image (shear t).continuous
  have hRreg : closure (interior (shear t '' (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}))) =
      shear t '' (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) := by
    rw [← (shear t).image_interior,← (shear t).image_closure,affine_rectangle_regular e a b hab]
  have hsub : shear t '' D ⊆ interior (shear t '' (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})) := by
    rw [← (shear t).image_interior]
    exact image_mono hcontain
  obtain ⟨T,hT,hcover⟩ := compact_polygonal_annulus_triangle_cover _ _ hDc hRc hRreg hsub F hFD hFR
  refine ⟨t,F,T,hT,?_⟩
  rw [hcover,← (shear t).image_interior,Set.image_sdiff (shear t).injective]

/-- Two intervals whose endpoints never lie strictly inside each other meet
in precisely the convex hull of their common endpoints. This includes all
collapsed-side cases. -/
theorem gapIntervals_hull_inter (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hca : c ≤ a ∨ b ≤ c) (hda : d ≤ a ∨ b ≤ d)
    (hac : a ≤ c ∨ d ≤ a) (hbc : b ≤ c ∨ d ≤ b) :
    Icc a b ∩ Icc c d = convexHull ℝ ({a,b} ∩ {c,d} : Set ℝ) := by
  rcases lt_trichotomy b c with hbc' | hbc' | hcb
  · have hi : Icc a b ∩ Icc c d = (∅ : Set ℝ) := by
      ext x
      simp only [mem_inter_iff,mem_Icc,mem_empty_iff_false,iff_false]
      rintro ⟨⟨_,hxb⟩,⟨hcx,_⟩⟩
      linarith
    have hs : ({a,b} ∩ {c,d} : Set ℝ) = ∅ := by
      ext x
      simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff,mem_empty_iff_false,iff_false]
      rintro ⟨rfl | rfl,h | h⟩ <;> linarith
    rw [hi,hs,convexHull_empty]
  · subst c
    have hi : Icc a b ∩ Icc b d = ({b} : Set ℝ) := by
      ext x
      simp only [mem_inter_iff,mem_Icc,mem_singleton_iff]
      constructor
      · intro h; linarith [h.1.2,h.2.1]
      · rintro rfl; exact ⟨⟨hab,le_rfl⟩,le_rfl,hcd⟩
    have hs : ({a,b} ∩ {b,d} : Set ℝ) = {b} := by
      ext x
      simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl,h | h⟩ <;> linarith
      · rintro rfl; exact ⟨Or.inr rfl,Or.inl rfl⟩
    rw [hi,hs,convexHull_singleton]
  · rcases lt_trichotomy d a with hda' | hda' | had
    · have hi : Icc a b ∩ Icc c d = (∅ : Set ℝ) := by
        ext x
        simp only [mem_inter_iff,mem_Icc,mem_empty_iff_false,iff_false]
        rintro ⟨⟨hax,_⟩,⟨_,hxd⟩⟩
        linarith
      have hs : ({a,b} ∩ {c,d} : Set ℝ) = ∅ := by
        ext x
        simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff,mem_empty_iff_false,iff_false]
        rintro ⟨rfl | rfl,h | h⟩ <;> linarith
      rw [hi,hs,convexHull_empty]
    · subst d
      have hi : Icc a b ∩ Icc c a = ({a} : Set ℝ) := by
        ext x
        simp only [mem_inter_iff,mem_Icc,mem_singleton_iff]
        constructor
        · intro h; linarith [h.1.1,h.2.2]
        · rintro rfl; exact ⟨⟨le_rfl,hab⟩,hcd,le_rfl⟩
      have hs : ({a,b} ∩ {c,a} : Set ℝ) = {a} := by
        ext x
        simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff]
        constructor
        · rintro ⟨rfl | rfl,h | h⟩ <;> linarith
        · rintro rfl; exact ⟨Or.inl rfl,Or.inr rfl⟩
      rw [hi,hs,convexHull_singleton]
    · have heac : a = c := le_antisymm
        (hac.resolve_right (not_le_of_gt had)) (hca.resolve_right (not_le_of_gt hcb))
      have hebd : b = d := le_antisymm
        (hda.resolve_left (not_le_of_gt had)) (hbc.resolve_left (not_le_of_gt hcb))
      subst c
      subst d
      rw [inter_self,inter_self,convexHull_pair,segment_eq_Icc hab]

/-- Convex hulls on opposite sides of a hyperplane intersect as faces whenever
the vertices on that hyperplane belong to one affinely independent set. -/
theorem finiteHulls_separated_inter {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S T U : Finset E) (L : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hS : ∀ y ∈ S, L y ≤ c) (hT : ∀ y ∈ T, c ≤ L y)
    (hSU : ∀ y ∈ S, L y = c → y ∈ U) (hTU : ∀ y ∈ T, L y = c → y ∈ U)
    (hU : AffineIndependent ℝ ((↑) : U → E)) :
    convexHull ℝ (S : Set E) ∩ convexHull ℝ (T : Set E) =
      convexHull ℝ ((S : Set E) ∩ T) := by
  classical
  let S₀ := S.filter (fun y ↦ L y = c)
  let T₀ := T.filter (fun y ↦ L y = c)
  have hs0 : (S₀ : Set E) = (S : Set E) ∩ {y | L y = c} := by ext y; simp [S₀]
  have ht0 : (T₀ : Set E) = (T : Set E) ∩ {y | (-L) y = -c} := by
    ext y
    simp [T₀]
  have hSf : convexHull ℝ (S : Set E) ∩ {y | L y = c} = convexHull ℝ (S₀ : Set E) := by
    rw [hs0]
    exact finiteHull_supporting_face S L c hS
  have hTf : convexHull ℝ (T : Set E) ∩ {y | (-L) y = -c} = convexHull ℝ (T₀ : Set E) := by
    rw [ht0]
    exact finiteHull_supporting_face T (-L) (-c) (fun y hy ↦ by simpa using neg_le_neg (hT y hy))
  have hSU' : S₀ ⊆ U := fun y hy ↦ hSU y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hTU' : T₀ ⊆ U := fun y hy ↦ hTU y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  apply subset_antisymm
  · rintro x ⟨hxS,hxT⟩
    have hl : L x ≤ c := (convexHull_min hS (convex_halfSpace_le (.mk L.map_add L.map_smul) c)) hxS
    have hr : c ≤ L x := (convexHull_min hT (convex_halfSpace_ge (.mk L.map_add L.map_smul) c)) hxT
    have he : L x = c := le_antisymm hl hr
    have hxS₀ : x ∈ convexHull ℝ (S₀ : Set E) := hSf ▸ ⟨hxS,he⟩
    have hxT₀ : x ∈ convexHull ℝ (T₀ : Set E) := hTf ▸ ⟨hxT,by simpa using congrArg Neg.neg he⟩
    have hi := (hU.convexHull_inter hSU' hTU').symm
    have hx : x ∈ convexHull ℝ ((S₀ : Set E) ∩ T₀) := hi ▸ ⟨hxS₀,hxT₀⟩
    apply convexHull_mono (t := ((S : Set E) ∩ T)) _ hx
    intro y hy
    exact ⟨(Finset.mem_filter.mp hy.1).1,(Finset.mem_filter.mp hy.2).1⟩
  · exact fun x hx ↦ ⟨convexHull_mono inter_subset_left hx,convexHull_mono inter_subset_right hx⟩

/-- Exact intersections descend from two simplices to any of their subfaces. -/
theorem finiteHulls_subface_inter {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S T A B : Finset E) (hAS : A ⊆ S) (hBT : B ⊆ T)
    (hS : AffineIndependent ℝ ((↑) : S → E)) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hinter : convexHull ℝ (S : Set E) ∩ convexHull ℝ (T : Set E) =
      convexHull ℝ ((S : Set E) ∩ T)) :
    convexHull ℝ (A : Set E) ∩ convexHull ℝ (B : Set E) =
      convexHull ℝ ((A : Set E) ∩ B) := by
  classical
  apply subset_antisymm
  · rintro x ⟨hxA,hxB⟩
    have hxST : x ∈ convexHull ℝ ((S : Set E) ∩ T) := by
      rw [← hinter]
      exact ⟨convexHull_mono hAS hxA,convexHull_mono hBT hxB⟩
    have hxAT : x ∈ convexHull ℝ ((A : Set E) ∩ T) := by
      have he := hS.convexHull_inter hAS (Finset.inter_subset_left : S ∩ T ⊆ S)
      have hx : x ∈ convexHull ℝ ((A : Set E) ∩ (S ∩ T : Finset E)) := by
        rw [he]
        exact ⟨hxA,by simpa using hxST⟩
      apply convexHull_mono (t := ((A : Set E) ∩ T)) _ hx
      intro y hy
      exact ⟨hy.1,(Finset.mem_inter.mp hy.2).2⟩
    have he := hT.convexHull_inter (Finset.inter_subset_right : A ∩ T ⊆ T) hBT
    have hx : x ∈ convexHull ℝ (((A ∩ T : Finset E) : Set E) ∩ B) := by
      rw [he]
      exact ⟨by simpa using hxAT,hxB⟩
    apply convexHull_mono (t := ((A : Set E) ∩ B)) _ hx
    intro y hy
    exact ⟨(Finset.mem_inter.mp hy.1).1,hy.2⟩
  · exact fun x hx ↦ ⟨convexHull_mono inter_subset_left hx,convexHull_mono inter_subset_right hx⟩

/-- Supporting faces may belong to different edges; exact intersections of
those two edges descend to the corresponding triangle faces. -/
theorem finiteHulls_inter_of_supporting_subfaces {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S T A B : Finset E) (L : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hS : ∀ y ∈ S, L y ≤ c) (hT : ∀ y ∈ T, c ≤ L y)
    (hSA : ∀ y ∈ S, L y = c → y ∈ A) (hTB : ∀ y ∈ T, L y = c → y ∈ B)
    (hA : AffineIndependent ℝ ((↑) : A → E)) (hB : AffineIndependent ℝ ((↑) : B → E))
    (hAB : convexHull ℝ (A : Set E) ∩ convexHull ℝ (B : Set E) =
      convexHull ℝ ((A : Set E) ∩ B)) :
    convexHull ℝ (S : Set E) ∩ convexHull ℝ (T : Set E) =
      convexHull ℝ ((S : Set E) ∩ T) := by
  classical
  let S₀ := S.filter (fun y ↦ L y = c)
  let T₀ := T.filter (fun y ↦ L y = c)
  have hs0 : (S₀ : Set E) = (S : Set E) ∩ {y | L y = c} := by ext y; simp [S₀]
  have ht0 : (T₀ : Set E) = (T : Set E) ∩ {y | (-L) y = -c} := by ext y; simp [T₀]
  have hSf : convexHull ℝ (S : Set E) ∩ {y | L y = c} = convexHull ℝ (S₀ : Set E) := by
    rw [hs0]; exact finiteHull_supporting_face S L c hS
  have hTf : convexHull ℝ (T : Set E) ∩ {y | (-L) y = -c} = convexHull ℝ (T₀ : Set E) := by
    rw [ht0]
    exact finiteHull_supporting_face T (-L) (-c) (fun y hy ↦ by simpa using neg_le_neg (hT y hy))
  have hS₀A : S₀ ⊆ A := fun y hy ↦ hSA y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hT₀B : T₀ ⊆ B := fun y hy ↦ hTB y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hsmall := finiteHulls_subface_inter A B S₀ T₀ hS₀A hT₀B hA hB hAB
  apply subset_antisymm
  · rintro x ⟨hxS,hxT⟩
    have hl : L x ≤ c := (convexHull_min hS (convex_halfSpace_le (.mk L.map_add L.map_smul) c)) hxS
    have hr : c ≤ L x := (convexHull_min hT (convex_halfSpace_ge (.mk L.map_add L.map_smul) c)) hxT
    have he : L x = c := le_antisymm hl hr
    have hxS₀ : x ∈ convexHull ℝ (S₀ : Set E) := hSf ▸ ⟨hxS,he⟩
    have hxT₀ : x ∈ convexHull ℝ (T₀ : Set E) := hTf ▸ ⟨hxT,by simpa using congrArg Neg.neg he⟩
    have hx : x ∈ convexHull ℝ ((S₀ : Set E) ∩ T₀) := hsmall ▸ ⟨hxS₀,hxT₀⟩
    apply convexHull_mono (t := ((S : Set E) ∩ T)) _ hx
    intro y hy
    exact ⟨(Finset.mem_filter.mp hy.1).1,(Finset.mem_filter.mp hy.2).1⟩
  · exact fun x hx ↦ ⟨convexHull_mono inter_subset_left hx,convexHull_mono inter_subset_right hx⟩

lemma affineIndependent_pair_set {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) :
    AffineIndependent ℝ ((↑) : ({a,b} : Set E) → E) := by
  by_cases hab : a = b
  · subst b
    have he : ({a,a} : Set E) = {a} := by ext x; simp
    rw [he]
    exact affineIndependent_of_subsingleton ℝ _
  · have h := (affineIndependent_of_ne ℝ hab).range
    have he : range ![a,b] = ({a,b} : Set E) := by
      ext x
      simp [Matrix.range_cons,Matrix.range_empty,or_comm]
    rw [he] at h
    exact h

/-- The vertical side version of the endpoint-gap hull intersection lemma. -/
theorem verticalGap_hulls_inter (u a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hca : c ≤ a ∨ b ≤ c) (hda : d ≤ a ∨ b ≤ d)
    (hac : a ≤ c ∨ d ≤ a) (hbc : b ≤ c ∨ d ≤ b) :
    convexHull ℝ {(u,a),(u,b)} ∩ convexHull ℝ {(u,c),(u,d)} =
      convexHull ℝ ({(u,a),(u,b)} ∩ {(u,c),(u,d)} : Set (ℝ × ℝ)) := by
  let f : ℝ →ᵃ[ℝ] (ℝ × ℝ) := (AffineMap.const ℝ ℝ u).prod (AffineMap.id ℝ ℝ)
  have hf : Function.Injective f := fun x y h ↦ congrArg Prod.snd h
  have h := congrArg (fun S : Set ℝ ↦ f '' S) (gapIntervals_hull_inter a b c d hab hcd hca hda hac hbc)
  rw [Set.image_inter hf,← segment_eq_Icc hab,← segment_eq_Icc hcd,
    image_segment,image_segment,AffineMap.image_convexHull,Set.image_inter hf] at h
  simpa only [Set.image_insert_eq,Set.image_singleton,convexHull_pair,
    f,AffineMap.prod_apply,AffineMap.const_apply,AffineMap.id_apply] using h

def cellTriangleFinset (l r : ℝ) (f g : ℝ × ℝ) (side : Bool) : Finset (ℝ × ℝ) :=
  Finset.univ.image (cellTriangle l r f g side)

lemma coe_cellTriangleFinset (l r : ℝ) (f g : ℝ × ℝ) (side : Bool) :
    (cellTriangleFinset l r f g side : Set (ℝ × ℝ)) = range (cellTriangle l r f g side) := by
  simp [cellTriangleFinset]

lemma cellTriangle_horizontal_bounds (l r : ℝ) (hlr : l ≤ r) (f g : ℝ × ℝ) (side : Bool)
    (p : ℝ × ℝ) (hp : p ∈ cellTriangleFinset l r f g side) : l ≤ p.1 ∧ p.1 ≤ r := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  cases side <;> fin_cases i <;> simp [cellTriangle,hlr]

lemma cellTriangle_right_vertices (l r : ℝ) (hlr : l < r) (f g : ℝ × ℝ) (side : Bool)
    (p : ℝ × ℝ) (hp : p ∈ cellTriangleFinset l r f g side) (hx : p.1 = r) :
    p ∈ ({(r,lineHeight f r),(r,lineHeight g r)} : Finset (ℝ × ℝ)) := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  cases side <;> fin_cases i <;> simp [cellTriangle] at hx ⊢ <;> linarith

lemma cellTriangle_left_vertices (l r : ℝ) (hlr : l < r) (f g : ℝ × ℝ) (side : Bool)
    (p : ℝ × ℝ) (hp : p ∈ cellTriangleFinset l r f g side) (hx : p.1 = l) :
    p ∈ ({(l,lineHeight f l),(l,lineHeight g l)} : Finset (ℝ × ℝ)) := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  cases side <;> fin_cases i <;> simp [cellTriangle] at hx ⊢ <;> linarith

/-- Triangles from strips sharing a vertical side meet in their exact common
vertex face when neither side has an unmatched interior vertex. -/
theorem cellTriangles_join_inter (l m r : ℝ) (hlm : l < m) (hmr : m < r)
    (f g h k : ℝ × ℝ) (s t : Bool)
    (hfg : lineHeight f m ≤ lineHeight g m) (hhk : lineHeight h m ≤ lineHeight k m)
    (hh : lineHeight h m ≤ lineHeight f m ∨ lineHeight g m ≤ lineHeight h m)
    (hk : lineHeight k m ≤ lineHeight f m ∨ lineHeight g m ≤ lineHeight k m)
    (hf : lineHeight f m ≤ lineHeight h m ∨ lineHeight k m ≤ lineHeight f m)
    (hg : lineHeight g m ≤ lineHeight h m ∨ lineHeight k m ≤ lineHeight g m) :
    convexHull ℝ (cellTriangleFinset l m f g s : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset m r h k t : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l m f g s : Set (ℝ × ℝ)) ∩ cellTriangleFinset m r h k t) := by
  classical
  apply finiteHulls_inter_of_supporting_subfaces _ _
    {(m,lineHeight f m),(m,lineHeight g m)} {(m,lineHeight h m),(m,lineHeight k m)}
    (LinearMap.fst ℝ ℝ ℝ) m
  · intro p hp
    exact (cellTriangle_horizontal_bounds l m hlm.le f g s p hp).2
  · intro p hp
    exact (cellTriangle_horizontal_bounds m r hmr.le h k t p hp).1
  · exact cellTriangle_right_vertices l m hlm f g s
  · exact cellTriangle_left_vertices m r hmr h k t
  · let e : ↥({(m,lineHeight f m),(m,lineHeight g m)} : Finset (ℝ × ℝ)) ↪
        ↥({(m,lineHeight f m),(m,lineHeight g m)} : Set (ℝ × ℝ)) :=
      ⟨fun y ↦ ⟨y.val,by
        simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
          Set.mem_singleton_iff] using y.property⟩,
        fun x y he ↦ Subtype.ext (congrArg (fun z : ↥({(m,lineHeight f m),(m,lineHeight g m)} : Set (ℝ × ℝ)) ↦ z.val) he)⟩
    exact (affineIndependent_pair_set (m,lineHeight f m) (m,lineHeight g m)).comp_embedding e
  · let e : ↥({(m,lineHeight h m),(m,lineHeight k m)} : Finset (ℝ × ℝ)) ↪
        ↥({(m,lineHeight h m),(m,lineHeight k m)} : Set (ℝ × ℝ)) :=
      ⟨fun y ↦ ⟨y.val,by
        simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
          Set.mem_singleton_iff] using y.property⟩,
        fun x y he ↦ Subtype.ext (congrArg (fun z : ↥({(m,lineHeight h m),(m,lineHeight k m)} : Set (ℝ × ℝ)) ↦ z.val) he)⟩
    exact (affineIndependent_pair_set (m,lineHeight h m) (m,lineHeight k m)).comp_embedding e
  · simpa only [Finset.coe_insert,Finset.coe_singleton] using
      verticalGap_hulls_inter m _ _ _ _ hfg hhk hh hk hf hg


lemma affineIndependent_pair_finset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [DecidableEq E] (a b : E) : AffineIndependent ℝ ((↑) : ({a,b} : Finset E) → E) := by
  let e : ↥({a,b} : Finset E) ↪ ↥({a,b} : Set E) :=
    ⟨fun y ↦ ⟨y.val,by
      simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] using y.property⟩,
      fun x y he ↦ Subtype.ext (congrArg (fun z : ↥({a,b} : Set E) ↦ z.val) he)⟩
  exact (affineIndependent_pair_set a b).comp_embedding e

lemma cellTriangle_vertex_coordinates (l r : ℝ) (f g : ℝ × ℝ) (side : Bool)
    (p : ℝ × ℝ) (hp : p ∈ cellTriangleFinset l r f g side) :
    (p.1 = l ∨ p.1 = r) ∧ (p.2 = lineHeight f p.1 ∨ p.2 = lineHeight g p.1) := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  cases side <;> fin_cases i <;> simp [cellTriangle]

lemma cellTriangle_vertex_graph (l r : ℝ) (f g k : ℝ × ℝ) (side : Bool)
    (p : ℝ × ℝ) (hp : p ∈ cellTriangleFinset l r f g side)
    (he : p.2 = lineHeight k p.1) :
    p ∈ ({(l,lineHeight k l),(r,lineHeight k r)} : Finset (ℝ × ℝ)) := by
  rcases (cellTriangle_vertex_coordinates l r f g side p hp).1 with h | h
  · apply Finset.mem_insert.mpr; left
    exact Prod.ext h (by simpa only [h] using he)
  · apply Finset.mem_insert.mpr; right
    apply Finset.mem_singleton.mpr
    exact Prod.ext h (by simpa only [h] using he)

/-- Two strip triangles in vertically ordered cells intersect in exactly the
convex hull of their shared vertices. The intervening upper supporting line of
the lower cell separates them, and its endpoint pair contains both faces. -/
theorem cellTriangles_vertical_inter (l r : ℝ) (f g h k : ℝ × ℝ) (s t : Bool)
    (hfg : ∀ u ∈ ({l,r} : Set ℝ), lineHeight f u ≤ lineHeight g u)
    (hgh : ∀ u ∈ ({l,r} : Set ℝ), lineHeight g u ≤ lineHeight h u)
    (hhk : ∀ u ∈ ({l,r} : Set ℝ), lineHeight h u ≤ lineHeight k u) :
    convexHull ℝ (cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset l r h k t : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩ cellTriangleFinset l r h k t) := by
  classical
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ - g.1 • LinearMap.fst ℝ ℝ ℝ
  have hLe (p : ℝ × ℝ) : L p = p.2 - g.1 * p.1 := rfl
  apply finiteHulls_separated_inter _ _ {(l,lineHeight g l),(r,lineHeight g r)} L g.2
  · intro p hp
    obtain ⟨hx,hy⟩ := cellTriangle_vertex_coordinates l r f g s p hp
    have hx' : p.1 ∈ ({l,r} : Set ℝ) := by simpa using hx
    have hh := hfg p.1 hx'
    rw [hLe]
    rcases hy with hy | hy <;> unfold lineHeight at hh hy <;> linarith
  · intro p hp
    obtain ⟨hx,hy⟩ := cellTriangle_vertex_coordinates l r h k t p hp
    have hx' : p.1 ∈ ({l,r} : Set ℝ) := by simpa using hx
    have hh := hgh p.1 hx'
    have hk := hhk p.1 hx'
    rw [hLe]
    rcases hy with hy | hy <;> unfold lineHeight at hh hk hy <;> linarith
  · intro p hp he
    apply cellTriangle_vertex_graph l r f g g s p hp
    rw [hLe] at he
    unfold lineHeight
    linarith
  · intro p hp he
    apply cellTriangle_vertex_graph l r h k g t p hp
    rw [hLe] at he
    unfold lineHeight
    linarith
  · exact affineIndependent_pair_finset _ _

/-- Triangles whose horizontal strips have a positive gap are disjoint, hence
also meet in exactly the hull of their common (empty) vertex set. -/
theorem cellTriangles_strictlySeparated_inter (l r l' r' : ℝ)
    (hlr : l ≤ r) (hlr' : l' ≤ r') (hgap : r < l')
    (f g h k : ℝ × ℝ) (s t : Bool) :
    convexHull ℝ (cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset l' r' h k t : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩ cellTriangleFinset l' r' h k t) := by
  apply subset_antisymm
  · rintro p ⟨hp,hp'⟩
    have hb : p.1 ≤ r := (convexHull_min
      (fun q hq ↦ (cellTriangle_horizontal_bounds l r hlr f g s q hq).2)
      (convex_halfSpace_le (.mk (LinearMap.fst ℝ ℝ ℝ).map_add (LinearMap.fst ℝ ℝ ℝ).map_smul) r)) hp
    have hb' : l' ≤ p.1 := (convexHull_min
      (fun q hq ↦ (cellTriangle_horizontal_bounds l' r' hlr' h k t q hq).1)
      (convex_halfSpace_ge (.mk (LinearMap.fst ℝ ℝ ℝ).map_add (LinearMap.fst ℝ ℝ ℝ).map_smul) l')) hp'
    exact False.elim (by linarith)
  · exact fun p hp ↦ ⟨convexHull_mono inter_subset_left hp,convexHull_mono inter_subset_right hp⟩


lemma triplePair_inter {E : Type*} (a b c d : E) (hbd : b ≠ d) :
    ({a,b,c} : Set E) ∩ {a,c,d} = {a,c} := by
  ext p
  simp only [mem_inter_iff,mem_insert_iff,mem_singleton_iff]
  aesop

/-- The two triangles of one cell meet in their chosen diagonal face. -/
theorem cellTriangles_sameCell_inter (l r : ℝ) (hlr : l < r) (f g : ℝ × ℝ)
    (hl : lineHeight f l ≤ lineHeight g l) (hr : lineHeight f r ≤ lineHeight g r)
    (s t : Bool) :
    convexHull ℝ (cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset l r f g t : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩ cellTriangleFinset l r f g t) := by
  have hft : convexHull ℝ (cellTriangleFinset l r f g false : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset l r f g true : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l r f g false : Set (ℝ × ℝ)) ∩ cellTriangleFinset l r f g true) := by
    rw [coe_cellTriangleFinset,coe_cellTriangleFinset,cellTriangle_range_false,cellTriangle_range_true,
      stripCell_triangles_inter l r hlr f g hl hr,triplePair_inter,convexHull_pair]
    intro he
    exact hlr.ne (congrArg Prod.fst he).symm
  cases s <;> cases t
  · simp
  · exact hft
  · simpa only [inter_comm] using hft
  · simp

lemma lineHeight_eq_in_strip {F : Finset (ℝ × ℝ)} {T : Finset ℝ}
    (hT : crossingLevels F ⊆ T) {l r x : ℝ} (hgap : ConsecutiveLevels T l r)
    (hx : x ∈ Ioo l r) {f g : ℝ × ℝ} (hf : f ∈ F) (hg : g ∈ F)
    (he : lineHeight f x = lineHeight g x) : f = g := by
  by_contra hn
  exact lineHeight_ne_of_not_crossing F f g hf hg hn x
    (fun hm ↦ hgap.not_mem hx (hT hm)) he

lemma lineHeight_le_endpoints_of_le {F : Finset (ℝ × ℝ)} {T : Finset ℝ}
    (hT : crossingLevels F ⊆ T) {l r x : ℝ} (hgap : ConsecutiveLevels T l r)
    (hx : x ∈ Ioo l r) {f g : ℝ × ℝ} (hf : f ∈ F) (hg : g ∈ F)
    (he : lineHeight f x ≤ lineHeight g x) :
    ∀ u ∈ ({l,r} : Set ℝ), lineHeight f u ≤ lineHeight g u := by
  rcases he.eq_or_lt with he | he
  · have hfg := lineHeight_eq_in_strip hT hgap hx hf hg he
    subst g
    exact fun _ _ ↦ le_rfl
  · have ho := lineHeight_order_endpoints f g l r hgap.2.2.1
      (lineHeight_order_in_strip F T hT l r x hgap hx f g hf hg he)
    intro u hu
    rcases hu with rfl | hu
    · exact ho.1
    · exact (mem_singleton_iff.mp hu) ▸ ho.2

/-- Every pair of triangles selected within one strip has an exact shared
vertex face, by the total order of adjacent supporting-line gaps. -/
theorem cellTriangles_sameStrip_inter (F : Finset (ℝ × ℝ)) (T : Finset ℝ)
    (hT : crossingLevels F ⊆ T) (l r x : ℝ) (hgap : ConsecutiveLevels T l r)
    (hx : x ∈ Ioo l r) (f g h k : ℝ × ℝ)
    (ha : AdjacentLines F f g x) (hb : AdjacentLines F h k x) (s t : Bool) :
    convexHull ℝ (cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset l r h k t : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩ cellTriangleFinset l r h k t) := by
  have hfg := lineHeight_le_endpoints_of_le hT hgap hx ha.1 ha.2.1 ha.2.2.1.le
  have hhk := lineHeight_le_endpoints_of_le hT hgap hx hb.1 hb.2.1 hb.2.2.1.le
  rcases ha.heightGap.separated_or_eq hb.heightGap with ⟨hf,hg⟩ | hs | hs
  · have hfh := lineHeight_eq_in_strip hT hgap hx ha.1 hb.1 hf
    have hgk := lineHeight_eq_in_strip hT hgap hx ha.2.1 hb.2.1 hg
    subst h
    subst k
    exact cellTriangles_sameCell_inter l r hgap.2.2.1 f g
      (hfg l (by simp)) (hfg r (by simp)) s t
  · exact cellTriangles_vertical_inter l r f g h k s t hfg
      (lineHeight_le_endpoints_of_le hT hgap hx ha.2.1 hb.1 hs) hhk
  · have he := cellTriangles_vertical_inter l r h k f g t s hhk
      (lineHeight_le_endpoints_of_le hT hgap hx hb.2.1 ha.1 hs) hfg
    simpa only [inter_comm] using he


lemma cellTriangles_orderedStrips_inter (F : Finset (ℝ × ℝ)) (T : Finset ℝ)
    (hT : crossingLevels F ⊆ T) (l r l' r' x x' : ℝ)
    (hgap : ConsecutiveLevels T l r) (hgap' : ConsecutiveLevels T l' r')
    (hx : x ∈ Ioo l r) (hx' : x' ∈ Ioo l' r') (hsep : r ≤ l')
    (f g h k : ℝ × ℝ) (ha : AdjacentLines F f g x) (hb : AdjacentLines F h k x')
    (s t : Bool) :
    convexHull ℝ (cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset l' r' h k t : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩ cellTriangleFinset l' r' h k t) := by
  rcases hsep.eq_or_lt with he | he
  · subst l'
    apply cellTriangles_join_inter l r r' hgap.2.2.1 hgap'.2.2.1 f g h k s t
    · exact lineHeight_le_endpoints_of_le hT hgap hx ha.1 ha.2.1 ha.2.2.1.le r (by simp)
    · exact lineHeight_le_endpoints_of_le hT hgap' hx' hb.1 hb.2.1 hb.2.2.1.le r (by simp)
    · exact adjacentLines_endpoint_gap F T hT l r x hgap hx f g ha r
        ⟨hgap.2.2.1.le,le_rfl⟩ h hb.1
    · exact adjacentLines_endpoint_gap F T hT l r x hgap hx f g ha r
        ⟨hgap.2.2.1.le,le_rfl⟩ k hb.2.1
    · exact adjacentLines_endpoint_gap F T hT r r' x' hgap' hx' h k hb r
        ⟨le_rfl,hgap'.2.2.1.le⟩ f ha.1
    · exact adjacentLines_endpoint_gap F T hT r r' x' hgap' hx' h k hb r
        ⟨le_rfl,hgap'.2.2.1.le⟩ g ha.2.1
  · exact cellTriangles_strictlySeparated_inter l r l' r' hgap.2.2.1.le hgap'.2.2.1.le he f g h k s t

/-- All triangles in the finite supporting-line arrangement have exact common
vertex faces. Horizontal gap comparison reduces to one strip or ordered strips;
adjacent height-gap comparison handles the former, and the vertical endpoint-gap
lemma handles the common boundary of the latter. -/
theorem cellTriangles_arrangement_inter (F : Finset (ℝ × ℝ)) (T : Finset ℝ)
    (hT : crossingLevels F ⊆ T) (l r l' r' x x' : ℝ)
    (hgap : ConsecutiveLevels T l r) (hgap' : ConsecutiveLevels T l' r')
    (hx : x ∈ Ioo l r) (hx' : x' ∈ Ioo l' r')
    (f g h k : ℝ × ℝ) (ha : AdjacentLines F f g x) (hb : AdjacentLines F h k x')
    (s t : Bool) :
    convexHull ℝ (cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩
      convexHull ℝ (cellTriangleFinset l' r' h k t : Set (ℝ × ℝ)) =
      convexHull ℝ ((cellTriangleFinset l r f g s : Set (ℝ × ℝ)) ∩ cellTriangleFinset l' r' h k t) := by
  rcases hgap.separated_or_eq hgap' with ⟨he,he'⟩ | hsep | hsep
  · subst l'
    subst r'
    exact cellTriangles_sameStrip_inter F T hT l r x hgap hx f g h k ha
      (hb.in_strip hT hgap hx' hx) s t
  · exact cellTriangles_orderedStrips_inter F T hT l r l' r' x x' hgap hgap' hx hx' hsep f g h k ha hb s t
  · have he := cellTriangles_orderedStrips_inter F T hT l' r' l r x' x hgap' hgap hx' hx hsep h k f g hb ha t s
    simpa only [inter_comm] using he

/-- The actual nondegenerate selected triangles form a finite geometric
simplicial complex: any two convex hulls meet in precisely their common face. -/
theorem selectedTriangle_inter (D R : Set (ℝ × ℝ)) (T : Finset ℝ)
    (F : Finset (ℝ × ℝ)) (hT : crossingLevels F ⊆ T)
    (s t : SelectedTriangle D R T F) :
    convexHull ℝ (range (selectedTriangleVertices s)) ∩
      convexHull ℝ (range (selectedTriangleVertices t)) =
      convexHull ℝ (range (selectedTriangleVertices s) ∩ range (selectedTriangleVertices t)) := by
  change convexHull ℝ (range (cellTriangle _ _ _ _ _)) ∩
      convexHull ℝ (range (cellTriangle _ _ _ _ _)) =
      convexHull ℝ (range (cellTriangle _ _ _ _ _) ∩ range (cellTriangle _ _ _ _ _))
  simp only [← coe_cellTriangleFinset]
  apply cellTriangles_arrangement_inter F T hT _ _ _ _
    (((s.val.1.val.1 : ℝ) + s.val.1.val.2.1)/2)
    (((t.val.1.val.1 : ℝ) + t.val.1.val.2.1)/2)
    s.val.1.property.1 t.val.1.property.1
  · constructor <;> linarith [s.val.1.property.1.2.2.1]
  · constructor <;> linarith [t.val.1.property.1.2.2.1]
  · exact s.val.1.property.2.1
  · exact t.val.1.property.2.1


/-- A retraction of the ambient space onto a regular closed region, with all
nonfixed points mapped to its boundary, preserves connected exteriors. -/
theorem annulus_connected_of_retraction {X : Type*} [TopologicalSpace X]
    (D R : Set X) (hD : IsClosed D) (hR : IsClosed R)
    (hreg : closure (interior R) = R) (hcontain : D ⊆ interior R)
    (hconn : IsConnected Dᶜ) (f : X → X) (hf : Continuous f)
    (hmem : ∀ x, f x ∈ R) (hfix : ∀ x ∈ R, f x = x)
    (hinner : ∀ x, f x ∈ interior R → f x = x) : IsConnected (R \ interior D) := by
  have himage : f '' Dᶜ = R \ D := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨hmem x,?_⟩
      intro hd
      have he := hinner x (hcontain hd)
      exact hx (he ▸ hd)
    · intro hy
      exact ⟨y,hy.2,hfix y hy.1⟩
  have hc : IsConnected (R \ D) := himage ▸ hconn.image f hf.continuousOn
  have he : closure (R \ D) = R \ interior D := by
    apply subset_antisymm
    · apply closure_minimal
      · exact fun x hx ↦ ⟨hx.1,fun hi ↦ hx.2 (interior_subset hi)⟩
      · exact hR.sdiff isOpen_interior
    · rw [← annulus_closure_open D R hD hR hreg hcontain]
      apply closure_mono
      exact fun x hx ↦ ⟨interior_subset hx.1,hx.2⟩
  exact he ▸ hc.closure

lemma clampReal_mem (a b x : ℝ) (hab : a ≤ b) : max a (min b x) ∈ Icc a b := by
  exact ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

lemma clampReal_eq (a b x : ℝ) (hx : x ∈ Icc a b) : max a (min b x) = x := by
  rw [min_eq_right hx.2,max_eq_right hx.1]

lemma clampReal_eq_of_interior (a b x : ℝ) (hab : a < b)
    (hx : max a (min b x) ∈ Ioo a b) : max a (min b x) = x := by
  apply clampReal_eq
  constructor
  · by_contra ha
    have hxa : x < a := lt_of_not_ge ha
    have he : max a (min b x) = a := max_eq_left ((min_le_right b x).trans hxa.le)
    exact hx.1.ne' he
  · by_contra hb
    have hbx : b < x := lt_of_not_ge hb
    have he : max a (min b x) = b := by rw [min_eq_left hbx.le,max_eq_right hab.le]
    exact hx.2.ne he

/-- Coordinate clamping supplies a retraction of every affine rectangle, and a
point mapped to its interior must already have been fixed. -/
theorem affine_rectangle_retraction (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ)
    (hab : ∀ i, a i < b i) :
    ∃ f : Plane → Plane, Continuous f ∧
      (∀ x, f x ∈ e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) ∧
      (∀ x ∈ e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}, f x = x) ∧
      (∀ x, f x ∈ interior (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) → f x = x) := by
  let B : Set (ℝ × ℝ) := Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)
  let H : (ℝ × ℝ) ≃ₜ Plane := (shear 0).symm.trans e.toHomeomorph
  have hR : e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i} = H '' B := by
    rw [← rectangle_coordinates_image a b]
    rw [image_image]
    rfl
  let c : (ℝ × ℝ) → ℝ × ℝ := fun x ↦
    (max (a 0) (min (b 0) x.1),max (a 1) (min (b 1) x.2))
  have hc : Continuous c :=
    (continuous_const.max (continuous_const.min continuous_fst)).prodMk
      (continuous_const.max (continuous_const.min continuous_snd))
  have hcB (x : ℝ × ℝ) : c x ∈ B :=
    ⟨clampReal_mem _ _ _ (hab 0).le,clampReal_mem _ _ _ (hab 1).le⟩
  have hfix (x : ℝ × ℝ) (hx : x ∈ B) : c x = x :=
    Prod.ext (clampReal_eq _ _ _ hx.1) (clampReal_eq _ _ _ hx.2)
  have hinner (x : ℝ × ℝ) (hx : c x ∈ interior B) : c x = x := by
    rw [interior_prod_eq,interior_Icc,interior_Icc] at hx
    exact Prod.ext (clampReal_eq_of_interior _ _ _ (hab 0) hx.1)
      (clampReal_eq_of_interior _ _ _ (hab 1) hx.2)
  refine ⟨fun x ↦ H (c (H.symm x)),H.continuous.comp (hc.comp H.symm.continuous),?_,?_,?_⟩
  · intro x
    rw [hR]
    exact mem_image_of_mem H (hcB (H.symm x))
  · intro x hx
    rw [hR] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change H (c (H.symm (H y))) = H y
    rw [H.symm_apply_apply,hfix y hy]
  · intro x hx
    change H (c (H.symm x)) ∈ interior _ at hx
    rw [hR,← H.image_interior,H.injective.mem_set_image] at hx
    change H (c (H.symm x)) = x
    rw [hinner (H.symm x) hx,H.apply_symm_apply]

/-- The literal exterior annulus is connected. Coordinate clamping of a
connected ambient exterior onto the outer rectangle gives the punctured closed
rectangle, whose closure is the requested annulus. -/
theorem polygonal_annulus_connected (D R : Set Plane) (hD : IsClosed D)
    (hconn : IsConnected Dᶜ)
    (hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧ R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})
    (hcontain : D ⊆ interior R) : IsConnected (R \ interior D) := by
  obtain ⟨e,a,b,hab,rfl⟩ := hrectangle
  obtain ⟨f,hf,hm,hfix,hin⟩ := affine_rectangle_retraction e a b hab
  exact annulus_connected_of_retraction D _ hD (affine_rectangle_compact e a b).isClosed
    (affine_rectangle_regular e a b hab) hcontain hconn f hf hm hfix hin


/-- Twice the signed area of an ordered planar triangle. -/
def orientedArea (a b c : ℝ × ℝ) : ℝ :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

lemma continuous_orientedArea (a b : ℝ × ℝ) : Continuous (orientedArea a b) := by
  unfold orientedArea
  fun_prop

lemma orientedArea_swap (a b c : ℝ × ℝ) : orientedArea b a c = - orientedArea a b c := by
  unfold orientedArea
  ring

lemma orientedArea_blend (a b u v : ℝ × ℝ) (α β : ℝ) (h : α+β=1) :
    orientedArea a b (α • u + β • v) = α * orientedArea a b u + β * orientedArea a b v := by
  simp only [orientedArea,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  have he : α = 1-β := by linarith
  rw [he]
  ring

lemma orientedArea_segment_zero (a b x : ℝ × ℝ) (hx : x ∈ segment ℝ a b) :
    orientedArea a b x = 0 := by
  obtain ⟨α,β,_,_,hab,rfl⟩ := hx
  rw [orientedArea_blend a b a b α β hab]
  simp only [orientedArea]
  ring

open scoped BigOperators in
/-- The three nonnegative oriented half-plane coordinates are barycentric
coordinates of a positively oriented triangle. -/
theorem mem_triangleHull_of_orientedArea (a b c x : ℝ × ℝ)
    (hA : 0 < orientedArea a b c) (hbc : 0 ≤ orientedArea b c x)
    (hca : 0 ≤ orientedArea c a x) (hab : 0 ≤ orientedArea a b x) :
    x ∈ convexHull ℝ ({a,b,c} : Set (ℝ × ℝ)) := by
  let A := orientedArea a b c
  have hA0 : A ≠ 0 := ne_of_gt hA
  apply mem_convexHull_of_exists_fintype
    ![orientedArea b c x / A,orientedArea c a x / A,orientedArea a b x / A] ![a,b,c]
  · intro i
    fin_cases i
    · exact div_nonneg hbc hA.le
    · exact div_nonneg hca hA.le
    · exact div_nonneg hab hA.le
  · simp only [Fin.sum_univ_three]
    change orientedArea b c x / A + orientedArea c a x / A + orientedArea a b x / A = 1
    rw [← add_div,← add_div]
    apply (div_eq_one_iff_eq hA0).mpr
    unfold A orientedArea
    ring
  · intro i
    fin_cases i <;> simp
  · simp only [Fin.sum_univ_three]
    change (orientedArea b c x / A) • a + (orientedArea c a x / A) • b +
      (orientedArea a b x / A) • c = x
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals
      field_simp
      unfold A orientedArea
      ring

/-- Two positively oriented triangles on the same directed base edge overlap
away from that edge. Near its midpoint the other four side inequalities are
strict, so a small displacement into the common positive side belongs to both. -/
theorem positive_triangles_overlap_off_edge (a b c d : ℝ × ℝ)
    (hc : 0 < orientedArea a b c) (hd : 0 < orientedArea a b d) :
    ∃ x, x ∈ convexHull ℝ ({a,b,c} : Set (ℝ × ℝ)) ∧
      x ∈ convexHull ℝ ({a,b,d} : Set (ℝ × ℝ)) ∧ x ∉ segment ℝ a b := by
  let m : ℝ × ℝ := ((a.1+b.1)/2,(a.2+b.2)/2)
  let U : Set (ℝ × ℝ) := {x | 0 < orientedArea b c x ∧ 0 < orientedArea c a x ∧
    0 < orientedArea b d x ∧ 0 < orientedArea d a x}
  have ho : IsOpen U :=
    (isOpen_lt continuous_const (continuous_orientedArea b c)).inter
      ((isOpen_lt continuous_const (continuous_orientedArea c a)).inter
        ((isOpen_lt continuous_const (continuous_orientedArea b d)).inter
          (isOpen_lt continuous_const (continuous_orientedArea d a))))
  have hm : m ∈ U := by
    have hbc : orientedArea b c m = orientedArea a b c / 2 := by unfold m orientedArea; ring
    have hca : orientedArea c a m = orientedArea a b c / 2 := by unfold m orientedArea; ring
    have hbd : orientedArea b d m = orientedArea a b d / 2 := by unfold m orientedArea; ring
    have hda : orientedArea d a m = orientedArea a b d / 2 := by unfold m orientedArea; ring
    change 0 < orientedArea b c m ∧ 0 < orientedArea c a m ∧
      0 < orientedArea b d m ∧ 0 < orientedArea d a m
    rw [hbc,hca,hbd,hda]
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hmc : m ∈ closure (openSegment ℝ m c) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ m c)
  obtain ⟨x,hxU,hxS⟩ := mem_closure_iff.mp hmc U ho hm
  have hpos : 0 < orientedArea a b x := by
    obtain ⟨α,β,hα,hβ,hsum,rfl⟩ := hxS
    rw [orientedArea_blend a b m c α β hsum]
    have hm0 : orientedArea a b m = 0 := by unfold m orientedArea; ring
    rw [hm0,mul_zero,zero_add]
    exact mul_pos hβ hc
  refine ⟨x,mem_triangleHull_of_orientedArea a b c x hc hxU.1.le hxU.2.1.le hpos.le,
    mem_triangleHull_of_orientedArea a b d x hd hxU.2.2.1.le hxU.2.2.2.le hpos.le,?_⟩
  intro hx
  exact hpos.ne' (orientedArea_segment_zero a b x hx)

/-- Exact common-edge intersections force triangles on opposite sides of that
edge. This is the geometric input for incidence at most two and coherent signs. -/
theorem triangle_sameEdge_area_opposite (a b c d : ℝ × ℝ)
    (hc : orientedArea a b c ≠ 0) (hd : orientedArea a b d ≠ 0)
    (hinter : convexHull ℝ ({a,b,c} : Set (ℝ × ℝ)) ∩
      convexHull ℝ ({a,b,d} : Set (ℝ × ℝ)) ⊆ segment ℝ a b) :
    (0 < orientedArea a b c ∧ orientedArea a b d < 0) ∨
      (orientedArea a b c < 0 ∧ 0 < orientedArea a b d) := by
  have hpos : ¬ (0 < orientedArea a b c ∧ 0 < orientedArea a b d) := by
    rintro ⟨hc',hd'⟩
    obtain ⟨x,hxc,hxd,hxe⟩ := positive_triangles_overlap_off_edge a b c d hc' hd'
    exact hxe (hinter ⟨hxc,hxd⟩)
  have hneg : ¬ (orientedArea a b c < 0 ∧ orientedArea a b d < 0) := by
    rintro ⟨hc',hd'⟩
    obtain ⟨x,hxc,hxd,hxe⟩ := positive_triangles_overlap_off_edge b a c d
      (by rw [orientedArea_swap]; linarith) (by rw [orientedArea_swap]; linarith)
    apply hxe
    rw [segment_symm]
    apply hinter
    constructor
    · simpa only [Set.insert_comm b a] using hxc
    · simpa only [Set.insert_comm b a] using hxd
  rcases lt_or_gt_of_ne hc with hc | hc <;> rcases lt_or_gt_of_ne hd with hd | hd
  · exact False.elim (hneg ⟨hc,hd⟩)
  · exact Or.inr ⟨hc,hd⟩
  · exact Or.inl ⟨hc,hd⟩
  · exact False.elim (hpos ⟨hc,hd⟩)


open scoped BigOperators in
lemma orientedArea_ne_zero_of_affineIndependent (a b c : ℝ × ℝ)
    (hi : AffineIndependent ℝ ![a,b,c]) : orientedArea a b c ≠ 0 := by
  intro he
  have hw₂ : ∑ i : Fin 3, (![b.2-c.2,c.2-a.2,a.2-b.2] i) = 0 := by
    simp only [Fin.sum_univ_three]
    change (b.2-c.2)+(c.2-a.2)+(a.2-b.2)=0
    ring
  have hp₂ : ∑ i : Fin 3, (![b.2-c.2,c.2-a.2,a.2-b.2] i) • (![a,b,c] i) = 0 := by
    simp only [Fin.sum_univ_three]
    change (b.2-c.2) • a + (c.2-a.2) • b + (a.2-b.2) • c = 0
    apply Prod.ext <;>
      simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Prod.fst_zero,Prod.snd_zero]
    · unfold orientedArea at he
      nlinarith [he]
    · ring
  have hw₁ : ∑ i : Fin 3, (![b.1-c.1,c.1-a.1,a.1-b.1] i) = 0 := by
    simp only [Fin.sum_univ_three]
    change (b.1-c.1)+(c.1-a.1)+(a.1-b.1)=0
    ring
  have hp₁ : ∑ i : Fin 3, (![b.1-c.1,c.1-a.1,a.1-b.1] i) • (![a,b,c] i) = 0 := by
    simp only [Fin.sum_univ_three]
    change (b.1-c.1) • a + (c.1-a.1) • b + (a.1-b.1) • c = 0
    apply Prod.ext <;>
      simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Prod.fst_zero,Prod.snd_zero]
    · ring
    · unfold orientedArea at he
      nlinarith [he]
  have h₂ := hi.eq_zero_of_sum_eq_zero hw₂ hp₂ 2 (Finset.mem_univ _)
  have h₁ := hi.eq_zero_of_sum_eq_zero hw₁ hp₁ 2 (Finset.mem_univ _)
  change a.2-b.2=0 at h₂
  change a.1-b.1=0 at h₁
  have hab : a = b := Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂)
  have hh : (0 : Fin 3) = 1 := hi.injective hab
  norm_num at hh


lemma face_triple_orientedArea_ne_zero {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (p : Fin N → ℝ × ℝ)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (u v w : Fin N) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hface : ({u,v,w} : Finset (Fin N)) ∈ K.faces) :
    orientedArea (p u) (p v) (p w) ≠ 0 := by
  classical
  let f : Fin 3 → Fin N := ![u,v,w]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let e : Fin 3 ↪ ↥({u,v,w} : Finset (Fin N)) :=
    ⟨fun i ↦ ⟨f i,by fin_cases i <;> simp [f]⟩,
      fun i j h ↦ hf (congrArg (fun x : ↥({u,v,w} : Finset (Fin N)) ↦ x.val) h)⟩
  apply orientedArea_ne_zero_of_affineIndependent
  convert (hi _ hface).comp_embedding e using 1
  funext i
  fin_cases i <;> rfl

/-- In an embedded pure planar triangle complex, at most one triangle on each
side of a fixed edge can occur. The sign of its third vertex is therefore an
injection of the incident triangles into the two-element set of signs. -/
theorem straightComplex_edge_incidence_le_two {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (u v : Fin N) (huv : u ≠ v) : GallierXu.incidence K {u,v} ≤ 2 := by
  classical
  let C := (GallierXu.simplices K 2).filter (fun s ↦ ({u,v} : Finset (Fin N)) ⊆ s)
  have hdata (s : C) : s.val ∈ K.faces ∧ s.val.card = 3 ∧ ({u,v} : Finset (Fin N)) ⊆ s.val := by
    have hs := Finset.mem_filter.mp s.property
    have hs' := Finset.mem_filter.mp hs.1
    exact ⟨hs'.2.1,hs'.2.2,hs.2⟩
  have hthird (s : C) : ∃ w, w ≠ u ∧ w ≠ v ∧ s.val = {u,v,w} := by
    exact GallierXu.triangle_third_vertex_g9 (hdata s).2.1 huv
      ((hdata s).2.2 (by simp)) ((hdata s).2.2 (by simp))
  choose w hw using hthird
  have hn (s : C) : orientedArea (p u) (p v) (p (w s)) ≠ 0 := by
    apply face_triple_orientedArea_ne_zero K p hi u v (w s) huv (hw s).1.symm (hw s).2.1.symm
    exact (hw s).2.2 ▸ (hdata s).1
  let sign : C → Bool := fun s ↦ decide (0 < orientedArea (p u) (p v) (p (w s)))
  have hinj : Function.Injective sign := by
    intro s t hsign
    by_contra hst
    have hwt : w s ≠ w t := by
      intro he
      apply hst
      apply Subtype.ext
      rw [(hw s).2.2,(hw t).2.2,he]
    have hcommon : s.val ∩ t.val = ({u,v} : Finset (Fin N)) := by
      rw [(hw s).2.2,(hw t).2.2]
      ext z
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      have hh : ¬ (z = w s ∧ z = w t) := fun h ↦ hwt (h.1.symm.trans h.2)
      tauto
    have hgeom : convexHull ℝ ({p u,p v,p (w s)} : Set (ℝ × ℝ)) ∩
        convexHull ℝ ({p u,p v,p (w t)} : Set (ℝ × ℝ)) ⊆ segment ℝ (p u) (p v) := by
      have he := hinter s.val (hdata s).1 t.val (hdata t).1
      rw [hcommon] at he
      rw [(hw s).2.2,(hw t).2.2] at he
      simpa only [Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton,
        convexHull_pair] using he.subset
    have ho := triangle_sameEdge_area_opposite (p u) (p v) (p (w s)) (p (w t)) (hn s) (hn t) hgeom
    change decide (0 < orientedArea (p u) (p v) (p (w s))) =
      decide (0 < orientedArea (p u) (p v) (p (w t))) at hsign
    rcases ho with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · simp [hs,not_lt_of_ge ht.le] at hsign
    · simp [ht,not_lt_of_ge hs.le] at hsign
  have hc := Fintype.card_le_of_injective sign hinj
  change C.card ≤ 2
  simpa only [Fintype.card_coe,Fintype.card_bool] using hc

/-- Purity supplies one incident triangle and planar separation bounds the
number by two, exactly the edge incidence condition for a surface complex. -/
theorem straightComplex_edge_incidence {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hpure : GallierXu.PureTwo K)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N)))) :
    ∀ e ∈ GallierXu.simplices K 1, GallierXu.incidence K e = 1 ∨ GallierXu.incidence K e = 2 := by
  classical
  intro e he
  have hef := (Finset.mem_filter.mp he).2
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp hef.2
  have hle := straightComplex_edge_incidence_le_two K p hi hinter u v huv
  obtain ⟨t,ht,htc,hsub⟩ := hpure {u,v} hef.1
  have hpos : 0 < GallierXu.incidence K {u,v} := by
    apply Finset.card_pos.mpr
    exact ⟨t,by simp [GallierXu.simplices,ht,htc,hsub]⟩
  omega


lemma orientedArea_cyclic (a b c : ℝ × ℝ) : orientedArea b c a = orientedArea a b c := by
  unfold orientedArea
  ring

lemma triangle_order_vertex_set {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : GallierXu.Triangle K) (o : Fin 3 ≃ ↥s.val) :
    s.val = {(o 0).val,(o 1).val,(o 2).val} := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨i,hi⟩ := o.surjective ⟨z,hz⟩
    have he := congrArg (fun x : s.val ↦ x.val) hi
    fin_cases i <;> simp only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
  · rw [s.property.2]
    exact Finset.card_le_three

lemma triangle_order_cyclic_vertex_set {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : GallierXu.Triangle K) (o : Fin 3 ≃ ↥s.val) (i : Fin 3) :
    s.val = {(o i).val,(o (finRotate 3 i)).val,(o (finRotate 3 (finRotate 3 i))).val} := by
  calc
    s.val = {(o 0).val,(o 1).val,(o 2).val} := triangle_order_vertex_set s o
    _ = _ := by
      fin_cases i <;> norm_num [finRotate_apply,Finset.insert_comm]
      all_goals
        ext z
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto

lemma triangle_order_cyclic_positive {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (p : Fin N → ℝ × ℝ) (s : GallierXu.Triangle K) (o : Fin 3 ≃ ↥s.val)
    (hpos : 0 < orientedArea (p (o 0)) (p (o 1)) (p (o 2))) (i : Fin 3) :
    0 < orientedArea (p (o i)) (p (o (finRotate 3 i))) (p (o (finRotate 3 (finRotate 3 i)))) := by
  fin_cases i
  · simpa [finRotate_apply] using hpos
  · change 0 < orientedArea (p (o 1)) (p (o 2)) (p (o 0))
    rw [orientedArea_cyclic]
    exact hpos
  · change 0 < orientedArea (p (o 2)) (p (o 0)) (p (o 1))
    rw [orientedArea_cyclic,orientedArea_cyclic]
    exact hpos

/-- Choose positive cyclic orders for all affinely independent planar faces. -/
theorem straightComplex_positive_orders {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (p : Fin N → ℝ × ℝ)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i)) :
    ∃ o : (s : GallierXu.Triangle K) → Fin 3 ≃ ↥s.val,
      ∀ s, 0 < orientedArea (p (o s 0)) (p (o s 1)) (p (o s 2)) := by
  classical
  have he (s : GallierXu.Triangle K) : ∃ e : Fin 3 ≃ ↥s.val,
      0 < orientedArea (p (e 0)) (p (e 1)) (p (e 2)) := by
    let e : Fin 3 ≃ ↥s.val := Fintype.equivOfCardEq (by simp [s.property.2])
    have hai : AffineIndependent ℝ ![p (e 0),p (e 1),p (e 2)] := by
      convert (hi s.val s.property.1).comp_embedding e.toEmbedding using 1
      funext i
      fin_cases i <;> rfl
    have hn := orientedArea_ne_zero_of_affineIndependent _ _ _ hai
    by_cases hpos : 0 < orientedArea (p (e 0)) (p (e 1)) (p (e 2))
    · exact ⟨e,hpos⟩
    · refine ⟨(Equiv.swap (0 : Fin 3) 1).trans e,?_⟩
      change 0 < orientedArea (p (e ((Equiv.swap (0 : Fin 3) 1) 0)))
        (p (e ((Equiv.swap (0 : Fin 3) 1) 1))) (p (e ((Equiv.swap (0 : Fin 3) 1) 2)))
      norm_num only [Equiv.swap_apply_left,Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne,
        Fin.reduceEq,not_false_eq_true]
      rw [orientedArea_swap]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hn)
  choose o ho using he
  exact ⟨o,ho⟩

lemma edgeDart_endpoints {N : ℕ} {a b u v : Fin N}
    (he : GallierXu.edgeDart a b = GallierXu.edgeDart u v) : a = u ∧ b = v := by
  have hl := Nat.pair_eq_pair.mp (congrArg Prod.fst he)
  have hs := congrArg Prod.snd he
  change decide (a < b) = decide (u < v) at hs
  change min a.val b.val = min u.val v.val ∧ max a.val b.val = max u.val v.val at hl
  by_cases hab : a < b <;> by_cases huv : u < v <;> simp [hab,huv] at hs
  all_goals
    constructor <;> apply Fin.ext <;> simp only [Fin.lt_def] at hab huv <;> omega

/-- Positive planar triangle orders never repeat a directed edge occurrence.
A repeated dart determines both endpoints. Distinct triangles would then lie
on the same side of their exact common edge, contradicting planar separation. -/
theorem straightComplex_directedOccurrence_unique {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (o : (s : GallierXu.Triangle K) → Fin 3 ≃ ↥s.val)
    (hpos : ∀ s, 0 < orientedArea (p (o s 0)) (p (o s 1)) (p (o s 2)))
    (s t : GallierXu.Triangle K) (i j : Fin 3)
    (he : GallierXu.edgeDart (o s i).val (o s (finRotate 3 i)).val =
      GallierXu.edgeDart (o t j).val (o t (finRotate 3 j)).val) : s = t ∧ i = j := by
  classical
  obtain ⟨hu,hv⟩ := edgeDart_endpoints he
  have hst : s = t := by
    by_contra hst
    let u := (o s i).val
    let v := (o s (finRotate 3 i)).val
    let c := (o s (finRotate 3 (finRotate 3 i))).val
    let d := (o t (finRotate 3 (finRotate 3 j))).val
    have hs : s.val = {u,v,c} := triangle_order_cyclic_vertex_set s (o s) i
    have ht : t.val = {u,v,d} := by
      calc
        t.val = {(o t j).val,(o t (finRotate 3 j)).val,d} :=
          triangle_order_cyclic_vertex_set t (o t) j
        _ = _ := by rw [← hu,← hv]
    have hcd : c ≠ d := by
      intro he
      apply hst
      exact Subtype.ext (by rw [hs,ht,he])
    have hc : 0 < orientedArea (p u) (p v) (p c) :=
      triangle_order_cyclic_positive p s (o s) (hpos s) i
    have hd : 0 < orientedArea (p u) (p v) (p d) := by
      have hh := triangle_order_cyclic_positive p t (o t) (hpos t) j
      rw [← hu,← hv] at hh
      exact hh
    have hcommon : s.val ∩ t.val = ({u,v} : Finset (Fin N)) := by
      rw [hs,ht]
      ext z
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      have hh : ¬ (z = c ∧ z = d) := fun h ↦ hcd (h.1.symm.trans h.2)
      tauto
    have hgeom := hinter s.val s.property.1 t.val t.property.1
    rw [hcommon,hs,ht] at hgeom
    simp only [Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton,
      convexHull_pair] at hgeom
    obtain ⟨x,hxc,hxd,hxe⟩ := positive_triangles_overlap_off_edge (p u) (p v) (p c) (p d) hc hd
    exact hxe (hgeom ▸ And.intro hxc hxd)
  subst t
  exact ⟨rfl,(o s).injective (Subtype.ext hu)⟩


/-- Positive geometric orders induce an oriented triangle presentation. Every
signed dart occurs at most once, and each used label has at least one sign. -/
theorem straightComplex_oriented {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (o : (s : GallierXu.Triangle K) → Fin 3 ≃ ↥s.val)
    (hpos : ∀ s, 0 < orientedArea (p (o s 0)) (p (o s 1)) (p (o s 2))) :
    GallierXu.Oriented (GallierXu.trianglePresentation K o) := by
  classical
  let tr : ↥(GallierXu.simplices K 2) → GallierXu.Triangle K :=
    fun s ↦ ⟨s.val,by simpa [GallierXu.simplices] using s.property⟩
  let word : ↥(GallierXu.simplices K 2) → GallierXu.Word :=
    fun s ↦ GallierXu.triangleWord (tr s) (o (tr s))
  let L := (GallierXu.simplices K 2).attach.toList
  have hn : (L.flatMap word).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro s hs
      apply List.Nodup.map
      · intro i j he
        exact (straightComplex_directedOccurrence_unique K p hinter o hpos (tr s) (tr s) i j he).2
      · exact List.nodup_finRange 3
    · apply List.Pairwise.imp _ (Finset.nodup_toList (GallierXu.simplices K 2).attach)
      intro s t hst
      apply List.disjoint_left.mpr
      intro d hds hdt
      obtain ⟨i,_,hi⟩ := List.mem_map.mp hds
      obtain ⟨j,_,hj⟩ := List.mem_map.mp hdt
      have he := (straightComplex_directedOccurrence_unique K p hinter o hpos
        (tr s) (tr t) i j (hi.trans hj.symm)).1
      exact hst (Subtype.ext (congrArg (fun x : GallierXu.Triangle K ↦ x.val) he))
  have hn' : (GallierXu.occurrences (GallierXu.trianglePresentation K o)).Nodup := by
    simpa only [GallierXu.occurrences,GallierXu.trianglePresentation,List.flatMap,L,word,tr] using hn
  constructor
  · intro w hw
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hw
    simp [GallierXu.triangleWord]
  · intro a ha
    have htrue := (List.nodup_iff_count_le_one.mp hn') (a,true)
    have hfalse := (List.nodup_iff_count_le_one.mp hn') (a,false)
    obtain ⟨d,hd,he⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    obtain ⟨label,sign⟩ := d
    change label = a at he
    subst label
    have hc := List.count_pos_iff.mpr hd
    cases sign <;> omega

/-- Every finite straight planar triangle complex carries coherent triangle
orientations, without any surface or boundary hypothesis. -/
theorem straightComplex_exists_orientation {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hinter : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N)))) :
    ∃ o : (s : GallierXu.Triangle K) → Fin 3 ≃ ↥s.val,
      GallierXu.Oriented (GallierXu.trianglePresentation K o) := by
  obtain ⟨o,ho⟩ := straightComplex_positive_orders K p hi
  exact ⟨o,straightComplex_oriented K p hinter o ho⟩


/-- A piecewise linear coordinate change taking the two positive coordinate
rays to the horizontal axis. It straightens a noncollinear polygon corner. -/
def cornerStraightener : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := (x.1-x.2,min x.1 x.2)
  invFun y := (y.2+max y.1 0,y.2+max (-y.1) 0)
  left_inv x := by
    apply Prod.ext <;> simp only
    · by_cases h : x.2 ≤ x.1
      · rw [min_eq_right h,max_eq_left (sub_nonneg.mpr h)]
        ring
      · have h' : x.1 ≤ x.2 := le_of_not_ge h
        rw [min_eq_left h',max_eq_right (sub_nonpos.mpr h')]
        ring
    · by_cases h : x.2 ≤ x.1
      · rw [min_eq_right h,max_eq_right (neg_nonpos.mpr (sub_nonneg.mpr h))]
        ring
      · have h' : x.1 ≤ x.2 := le_of_not_ge h
        rw [min_eq_left h',max_eq_left (neg_nonneg.mpr (sub_nonpos.mpr h'))]
        ring
  right_inv y := by
    apply Prod.ext <;> simp only
    · by_cases h : 0 ≤ y.1
      · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
        ring
      · have h' := le_of_not_ge h
        rw [max_eq_right h',max_eq_left (neg_nonneg.mpr h')]
        ring
    · by_cases h : 0 ≤ y.1
      · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),min_eq_right (by linarith)]
        ring
      · have h' := le_of_not_ge h
        rw [max_eq_right h',max_eq_left (neg_nonneg.mpr h'),min_eq_left (by linarith)]
        ring
  continuous_toFun := (continuous_fst.sub continuous_snd).prodMk (continuous_fst.min continuous_snd)
  continuous_invFun :=
    (continuous_snd.add (continuous_fst.max continuous_const)).prodMk
      (continuous_snd.add (continuous_fst.neg.max continuous_const))

lemma cornerStraightener_axis (x : ℝ × ℝ) :
    (cornerStraightener x).2 = 0 ↔
      (0 ≤ x.1 ∧ x.2 = 0) ∨ (x.1 = 0 ∧ 0 ≤ x.2) := by
  change min x.1 x.2 = 0 ↔ _
  rcases le_total x.1 x.2 with h | h
  · rw [min_eq_left h]
    constructor
    · intro he; exact Or.inr ⟨he,he ▸ h⟩
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
      · linarith
      · exact h1
  · rw [min_eq_right h]
    constructor
    · intro he; exact Or.inl ⟨he ▸ h,he⟩
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
      · exact h2
      · linarith

/-- Linear coordinates along a pair of independent rays. -/
def rayPairCoordinates (a b : ℝ × ℝ) (h : a.1*b.2-a.2*b.1 ≠ 0) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := ((b.2*x.1-b.1*x.2)/(a.1*b.2-a.2*b.1),
    (a.1*x.2-a.2*x.1)/(a.1*b.2-a.2*b.1))
  invFun y := y.1 • a + y.2 • b
  left_inv x := by
    apply Prod.ext
    · change ((b.2*x.1-b.1*x.2)/(a.1*b.2-a.2*b.1))*a.1 +
        ((a.1*x.2-a.2*x.1)/(a.1*b.2-a.2*b.1))*b.1 = x.1
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div]
      apply (div_eq_iff h).mpr
      ring
    · change ((b.2*x.1-b.1*x.2)/(a.1*b.2-a.2*b.1))*a.2 +
        ((a.1*x.2-a.2*x.1)/(a.1*b.2-a.2*b.1))*b.2 = x.2
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div]
      apply (div_eq_iff h).mpr
      ring
  right_inv y := by
    apply Prod.ext
    · change (b.2*(y.1*a.1+y.2*b.1)-b.1*(y.1*a.2+y.2*b.2))/(a.1*b.2-a.2*b.1) = y.1
      apply (div_eq_iff h).mpr
      ring
    · change (a.1*(y.1*a.2+y.2*b.2)-a.2*(y.1*a.1+y.2*b.1))/(a.1*b.2-a.2*b.1) = y.2
      apply (div_eq_iff h).mpr
      ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma rayPairCoordinates_smul_left (a b : ℝ × ℝ) (h : a.1*b.2-a.2*b.1 ≠ 0) (t : ℝ) :
    rayPairCoordinates a b h (t • a) = (t,0) := by
  have hh := (rayPairCoordinates a b h).apply_symm_apply (t,0)
  change rayPairCoordinates a b h (t • a + (0 : ℝ) • b) = (t,0) at hh
  simpa only [zero_smul,add_zero] using hh

lemma rayPairCoordinates_smul_right (a b : ℝ × ℝ) (h : a.1*b.2-a.2*b.1 ≠ 0) (t : ℝ) :
    rayPairCoordinates a b h (t • b) = (0,t) := by
  have hh := (rayPairCoordinates a b h).apply_symm_apply (0,t)
  change rayPairCoordinates a b h ((0 : ℝ) • a + t • b) = (0,t) at hh
  simpa only [zero_smul,zero_add] using hh

/-- For a convex set lying above a supporting axis, deleting a point on that
axis preserves path connectedness whenever the set has a point strictly above
it. Every segment from that point stays off the deleted point. -/
theorem convex_halfPlane_punctured_connected (S : Set (ℝ × ℝ))
    (hS : Convex ℝ S) (hnonneg : ∀ x ∈ S, 0 ≤ x.2)
    (hw : ∃ w ∈ S, 0 < w.2) : IsConnected (S \ {(0,0)}) := by
  obtain ⟨w,hw,hwpos⟩ := hw
  have hstar : StarConvex ℝ w (S \ {(0,0)}) := by
    intro x hx α β hα hβ hsum
    refine ⟨hS hw hx.1 hα hβ hsum,?_⟩
    intro he
    change α • w + β • x = (0,0) at he
    have h2 := congrArg Prod.snd he
    simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul] at h2
    have hxp := hnonneg x hx.1
    have hα0 : α = 0 := by nlinarith [mul_nonneg hβ hxp]
    have hβ1 : β = 1 := by linarith
    rw [hα0,hβ1,zero_smul,one_smul,zero_add] at he
    exact hx.2 he
  have hw' : w ∈ S \ {(0,0)} := ⟨hw,by intro he; have h := congrArg Prod.snd he; simp only at h; linarith⟩
  exact (hstar.isPathConnected hw').isConnected


/-- In a convex open neighborhood where a regular closed set has exactly a
straight frontier, its interior occupies exactly one of the two open halves. -/
theorem local_straight_frontier_sides (D O : Set (ℝ × ℝ))
    (hD : IsClosed D) (hreg : closure (interior D) = D)
    (hO : IsOpen O) (hconv : Convex ℝ O) (hzero : (0,0) ∈ O)
    (hfront : ∀ x ∈ O, x ∈ frontier D ↔ x.2 = 0) :
    (O ∩ {x | 0 < x.2} ⊆ interior D ∧ O ∩ {x | x.2 < 0} ⊆ Dᶜ) ∨
      (O ∩ {x | 0 < x.2} ⊆ Dᶜ ∧ O ∩ {x | x.2 < 0} ⊆ interior D) := by
  let U : Set (ℝ × ℝ) := O ∩ {x | 0 < x.2}
  let L : Set (ℝ × ℝ) := O ∩ {x | x.2 < 0}
  have hUc : IsPreconnected U :=
    (hconv.inter (convex_halfSpace_gt (.mk (LinearMap.snd ℝ ℝ ℝ).map_add
      (LinearMap.snd ℝ ℝ ℝ).map_smul) 0)).isPreconnected
  have hLc : IsPreconnected L :=
    (hconv.inter (convex_halfSpace_lt (.mk (LinearMap.snd ℝ ℝ ℝ).map_add
      (LinearMap.snd ℝ ℝ ℝ).map_smul) 0)).isPreconnected
  have hUd : Disjoint U (frontier D) := by
    apply Set.disjoint_left.mpr
    intro x hx hf
    exact hx.2.ne' ((hfront x hx.1).mp hf)
  have hLd : Disjoint L (frontier D) := by
    apply Set.disjoint_left.mpr
    intro x hx hf
    exact hx.2.ne ((hfront x hx.1).mp hf)
  have hzfront : (0,0) ∈ frontier D := (hfront _ hzero).mpr rfl
  have hzD : (0,0) ∈ D := hD.closure_eq ▸ frontier_subset_closure hzfront
  have hzcl : (0,0) ∈ closure (interior D) := hreg.symm ▸ hzD
  obtain ⟨x,hxO,hxi⟩ := mem_closure_iff.mp hzcl O hO hzero
  have hxne : x.2 ≠ 0 := by
    intro hx0
    exact (hD.frontier_eq ▸ (hfront x hxO).mpr hx0).2 hxi
  have hzout : (0,0) ∈ closure Dᶜ := by
    rw [closure_compl]
    exact (hD.frontier_eq ▸ hzfront).2
  obtain ⟨y,hyO,hyo⟩ := mem_closure_iff.mp hzout O hO hzero
  have hyne : y.2 ≠ 0 := by
    intro hy0
    exact hyo (hD.closure_eq ▸ frontier_subset_closure ((hfront y hyO).mpr hy0))
  rcases band_side D U hD hUc hUd with hUi | hUo <;>
    rcases band_side D L hD hLc hLd with hLi | hLo
  · exfalso
    rcases lt_or_gt_of_ne hyne with hy | hy
    · exact hyo (interior_subset (hLi ⟨hyO,hy⟩))
    · exact hyo (interior_subset (hUi ⟨hyO,hy⟩))
  · exact Or.inl ⟨hUi,hLo⟩
  · exact Or.inr ⟨hUo,hLi⟩
  · exfalso
    rcases lt_or_gt_of_ne hxne with hx | hx
    · exact hLo ⟨hxO,hx⟩ (interior_subset hxi)
    · exact hUo ⟨hxO,hx⟩ (interior_subset hxi)

/-- The exterior of a regular closed set with a straight local frontier is
exactly one closed half of the local convex neighborhood. -/
theorem local_straight_frontier_exterior (D O : Set (ℝ × ℝ))
    (hD : IsClosed D) (hreg : closure (interior D) = D)
    (hO : IsOpen O) (hconv : Convex ℝ O) (hzero : (0,0) ∈ O)
    (hfront : ∀ x ∈ O, x ∈ frontier D ↔ x.2 = 0) :
    O \ interior D = O ∩ {x | 0 ≤ x.2} ∨ O \ interior D = O ∩ {x | x.2 ≤ 0} := by
  rcases local_straight_frontier_sides D O hD hreg hO hconv hzero hfront with ⟨hU,hL⟩ | ⟨hU,hL⟩
  · right
    ext x
    change (x ∈ O ∧ x ∉ interior D) ↔ (x ∈ O ∧ x.2 ≤ 0)
    constructor
    · rintro ⟨hx,hxi⟩
      exact ⟨hx,le_of_not_gt (fun h ↦ hxi (hU ⟨hx,h⟩))⟩
    · rintro ⟨hx,hx2⟩
      refine ⟨hx,?_⟩
      rcases hx2.eq_or_lt with he | he
      · exact (hD.frontier_eq ▸ (hfront x hx).mpr he).2
      · exact fun hi ↦ hL ⟨hx,he⟩ (interior_subset hi)
  · left
    ext x
    change (x ∈ O ∧ x ∉ interior D) ↔ (x ∈ O ∧ 0 ≤ x.2)
    constructor
    · rintro ⟨hx,hxi⟩
      exact ⟨hx,le_of_not_gt (fun h ↦ hxi (hL ⟨hx,h⟩))⟩
    · rintro ⟨hx,hx2⟩
      refine ⟨hx,?_⟩
      rcases hx2.eq_or_lt with he | he
      · exact (hD.frontier_eq ▸ (hfront x hx).mpr he.symm).2
      · exact fun hi ↦ hU ⟨hx,he⟩ (interior_subset hi)


lemma rayPairCoordinates_zero (a b : ℝ × ℝ) (h : a.1*b.2-a.2*b.1 ≠ 0) :
    rayPairCoordinates a b h 0 = 0 := by
  change rayPairCoordinates a b h 0 = (0,0)
  simpa only [zero_smul] using rayPairCoordinates_smul_left a b h 0

/-- Two noncollinear closed segments incident at zero admit a local straight
frontier chart. The coordinate cutoff excludes their remote endpoints. -/
theorem noncollinear_corner_local_chart (a b : ℝ × ℝ)
    (h : a.1*b.2-a.2*b.1 ≠ 0) :
    ∃ H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), H 0 = 0 ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ 0 ∈ V ∧
        ∀ x ∈ V, x ∈ segment ℝ 0 a ∪ segment ℝ 0 b ↔ (H x).2 = 0 := by
  let C := rayPairCoordinates a b h
  let H := C.trans cornerStraightener
  let V : Set (ℝ × ℝ) := {x | (C x).1 < 1 ∧ (C x).2 < 1}
  have hC0 : C 0 = 0 := rayPairCoordinates_zero a b h
  refine ⟨H,?_,V,?_,?_,?_⟩
  · change cornerStraightener (C 0) = 0
    rw [hC0]
    simp [cornerStraightener]
  · exact (isOpen_lt (continuous_fst.comp C.continuous) continuous_const).inter
      (isOpen_lt (continuous_snd.comp C.continuous) continuous_const)
  · change (C 0).1 < 1 ∧ (C 0).2 < 1
    rw [hC0]
    norm_num
  · intro x hx
    change x ∈ segment ℝ 0 a ∪ segment ℝ 0 b ↔ (cornerStraightener (C x)).2 = 0
    rw [cornerStraightener_axis]
    constructor
    · rintro (hs | hs)
      · obtain ⟨α,β,hα,hβ,hsum,he⟩ := hs
        rw [smul_zero,zero_add] at he
        rw [← he]
        have hh : C (β • a) = (β,0) := rayPairCoordinates_smul_left a b h β
        rw [hh]
        exact Or.inl ⟨hβ,rfl⟩
      · obtain ⟨α,β,hα,hβ,hsum,he⟩ := hs
        rw [smul_zero,zero_add] at he
        rw [← he]
        have hh : C (β • b) = (0,β) := rayPairCoordinates_smul_right a b h β
        rw [hh]
        exact Or.inr ⟨rfl,hβ⟩
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
      · left
        refine ⟨1-(C x).1,(C x).1,by linarith [hx.1],h1,by ring,?_⟩
        rw [smul_zero,zero_add]
        apply C.injective
        rw [rayPairCoordinates_smul_left a b h]
        exact Prod.ext rfl h2.symm
      · right
        refine ⟨1-(C x).2,(C x).2,by linarith [hx.2],h2,by ring,?_⟩
        rw [smul_zero,zero_add]
        apply C.injective
        rw [rayPairCoordinates_smul_right a b h]
        exact Prod.ext h1.symm rfl


lemma zero_segment_smul_mem {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : E) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : t • a ∈ segment ℝ 0 a := by
  exact ⟨1-t,t,by linarith [ht.2],ht.1,by ring,by simp⟩

lemma exists_ray_coordinate_partner (a : ℝ × ℝ) (ha : a ≠ 0) :
    ∃ b : ℝ × ℝ, a.1*b.2-a.2*b.1 ≠ 0 := by
  by_cases hx : a.1 = 0
  · have hy : a.2 ≠ 0 := by intro he; exact ha (Prod.ext hx he)
    exact ⟨(1,0),by simpa using hy⟩
  · exact ⟨(0,1),by simpa using hx⟩

/-- Opposite collinear segments form a straight local arc. Simplicity rules
out two segments pointing along the same ray. -/
theorem collinear_corner_local_chart (a b : ℝ × ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcross : a.1*b.2-a.2*b.1 = 0)
    (hinter : segment ℝ 0 a ∩ segment ℝ 0 b ⊆ {0}) :
    ∃ H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), H 0 = 0 ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ 0 ∈ V ∧
        ∀ x ∈ V, x ∈ segment ℝ 0 a ∪ segment ℝ 0 b ↔ (H x).2 = 0 := by
  obtain ⟨q,hq⟩ := exists_ray_coordinate_partner a ha
  let C := rayPairCoordinates a q hq
  let t : ℝ := (C b).1
  have hC0 : C 0 = 0 := rayPairCoordinates_zero a q hq
  have hCb : (C b).2 = 0 := by
    change (a.1*b.2-a.2*b.1)/(a.1*q.2-a.2*q.1)=0
    rw [hcross,zero_div]
  have hbt : b = t • a := by
    apply C.injective
    rw [rayPairCoordinates_smul_left a q hq]
    exact Prod.ext rfl hCb
  have ht0 : t ≠ 0 := by
    intro ht
    exact hb (by rw [hbt,ht,zero_smul])
  have ht : t < 0 := by
    by_contra ht
    have htp : 0 < t := lt_of_le_of_ne (le_of_not_gt ht) ht0.symm
    let ε := min 1 t / 2
    have hε : 0 < ε := div_pos (lt_min zero_lt_one htp) (by norm_num)
    have hε1 : ε ≤ 1 := by dsimp [ε]; linarith [min_le_left (1:ℝ) t]
    have hεt : ε ≤ t := by dsimp [ε]; linarith [min_le_right (1:ℝ) t]
    have hxA := zero_segment_smul_mem a ε ⟨hε.le,hε1⟩
    have hxB : ε • a ∈ segment ℝ 0 b := by
      have hh := zero_segment_smul_mem b (ε/t) ⟨div_nonneg hε.le htp.le,(div_le_one htp).mpr hεt⟩
      rw [hbt,smul_smul,div_mul_cancel₀ _ ht0] at hh
      rwa [← hbt] at hh
    have hx0 : ε • a = 0 := hinter ⟨hxA,hxB⟩
    exact ha ((smul_eq_zero.mp hx0).resolve_left hε.ne')
  let V : Set (ℝ × ℝ) := {x | t < (C x).1 ∧ (C x).1 < 1}
  refine ⟨C,hC0,V,?_,?_,?_⟩
  · exact (isOpen_lt continuous_const (continuous_fst.comp C.continuous)).inter
      (isOpen_lt (continuous_fst.comp C.continuous) continuous_const)
  · change t < (C 0).1 ∧ (C 0).1 < 1
    rw [hC0]
    exact ⟨ht,zero_lt_one⟩
  · intro x hx
    constructor
    · rintro (hs | hs)
      · obtain ⟨α,β,_,_,_,he⟩ := hs
        rw [smul_zero,zero_add] at he
        rw [← he,rayPairCoordinates_smul_left a q hq]
      · obtain ⟨α,β,_,_,_,he⟩ := hs
        rw [smul_zero,zero_add,hbt,smul_smul] at he
        rw [← he,rayPairCoordinates_smul_left a q hq]
    · intro hzero
      by_cases hp : 0 ≤ (C x).1
      · left
        have hh := zero_segment_smul_mem a (C x).1 ⟨hp,hx.2.le⟩
        have he : (C x).1 • a = x := by
          apply C.injective
          rw [rayPairCoordinates_smul_left a q hq]
          exact Prod.ext rfl hzero.symm
        exact he ▸ hh
      · right
        have hn : (C x).1 ≤ 0 := le_of_not_ge hp
        have hquot : (C x).1/t ∈ Icc (0:ℝ) 1 :=
          ⟨div_nonneg_of_nonpos hn ht.le,(div_le_one_of_neg ht).mpr hx.1.le⟩
        have hh := zero_segment_smul_mem b ((C x).1/t) hquot
        have he : ((C x).1/t) • b = x := by
          rw [hbt,smul_smul,div_mul_cancel₀ _ ht0]
          apply C.injective
          rw [rayPairCoordinates_smul_left a q hq]
          exact Prod.ext rfl hzero.symm
        exact he ▸ hh

/-- Every pair of nonoverlapping nondegenerate segments incident at the origin
is locally straightened by a concrete planar homeomorphism. -/
theorem two_segments_local_chart (a b : ℝ × ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hinter : segment ℝ 0 a ∩ segment ℝ 0 b ⊆ {0}) :
    ∃ H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), H 0 = 0 ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ 0 ∈ V ∧
        ∀ x ∈ V, x ∈ segment ℝ 0 a ∪ segment ℝ 0 b ↔ (H x).2 = 0 := by
  by_cases h : a.1*b.2-a.2*b.1 = 0
  · exact collinear_corner_local_chart a b ha hb h hinter
  · exact noncollinear_corner_local_chart a b h


/-- Deleting a supporting-hyperplane point leaves a convex set connected,
provided the set meets the strict supporting halfspace. -/
theorem convex_support_punctured_connected {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Set E) (hS : Convex ℝ S) (f : E →ₗ[ℝ] ℝ)
    (hnonneg : ∀ x ∈ S, 0 ≤ f x) (hw : ∃ w ∈ S, 0 < f w) :
    IsConnected (S \ {0}) := by
  obtain ⟨w,hw,hwpos⟩ := hw
  have hstar : StarConvex ℝ w (S \ {0}) := by
    intro x hx α β hα hβ hsum
    refine ⟨hS hw hx.1 hα hβ hsum,?_⟩
    intro he
    change α • w + β • x = 0 at he
    have hf := congrArg f he
    simp only [map_add,map_smul,map_zero,smul_eq_mul] at hf
    have hxp := hnonneg x hx.1
    have hα0 : α = 0 := by nlinarith [mul_nonneg hβ hxp]
    have hβ1 : β = 1 := by linarith
    rw [hα0,hβ1,zero_smul,one_smul,zero_add] at he
    exact hx.2 he
  have hw' : w ∈ S \ {0} := ⟨hw,by
    intro he
    have hh := congrArg f he
    rw [map_zero] at hh
    exact hwpos.ne' hh⟩
  exact (hstar.isPathConnected hw').isConnected

lemma open_plane_axis_points (O : Set (ℝ × ℝ)) (hO : IsOpen O) (hz : (0,0) ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ (ε,0) ∈ O ∧ (0,ε) ∈ O ∧ (0,-ε) ∈ O := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hO (0,0) hz
  refine ⟨r/2,by linarith,?_,?_,?_⟩ <;> apply hball
  all_goals
    simp only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero,abs_zero,abs_neg,
      abs_of_pos (show 0 < r/2 by linarith),max_eq_left (show 0 ≤ r/2 by linarith),
      max_eq_right (show 0 ≤ r/2 by linarith)]
    linarith

/-- An open convex planar neighborhood remains connected after deleting its
center. Its upper and lower closed halves remain connected and meet on a
nonzero point of the horizontal axis. -/
theorem convex_open_plane_punctured_connected (O : Set (ℝ × ℝ))
    (hO : IsOpen O) (hconv : Convex ℝ O) (hz : (0,0) ∈ O) :
    IsConnected (O \ {0}) := by
  obtain ⟨ε,hε,hx,hu,hl⟩ := open_plane_axis_points O hO hz
  let f : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ
  let U := O ∩ {x | 0 ≤ f x}
  let L := O ∩ {x | 0 ≤ (-f) x}
  have hUconv : Convex ℝ U := hconv.inter
    (convex_halfSpace_ge (.mk f.map_add f.map_smul) 0)
  have hLconv : Convex ℝ L := hconv.inter
    (convex_halfSpace_ge (.mk (-f).map_add (-f).map_smul) 0)
  have hU := convex_support_punctured_connected U hUconv f (fun _ h ↦ h.2)
    ⟨(0,ε),⟨hu,hε.le⟩,hε⟩
  have hL := convex_support_punctured_connected L hLconv (-f) (fun _ h ↦ h.2)
    ⟨(0,-ε),⟨hl,by change 0 ≤ - - ε; linarith⟩,by change 0 < - - ε; linarith⟩
  have hmeet : ((U \ {0}) ∩ (L \ {0})).Nonempty := by
    refine ⟨(ε,0),⟨⟨hx,by change (0:ℝ) ≤ 0; exact le_rfl⟩,?_⟩,⟨⟨hx,by change 0 ≤ -(0:ℝ); simp⟩,?_⟩⟩ <;>
      intro he <;> exact hε.ne' (congrArg Prod.fst he)
  have heq : (U \ {0}) ∪ (L \ {0}) = O \ {0} := by
    ext x
    change ((x ∈ O ∧ 0 ≤ x.2) ∧ x ≠ 0) ∨ ((x ∈ O ∧ 0 ≤ -x.2) ∧ x ≠ 0) ↔
      x ∈ O ∧ x ≠ 0
    constructor
    · rintro (⟨⟨h,_⟩,hn⟩ | ⟨⟨h,_⟩,hn⟩) <;> exact ⟨h,hn⟩
    · rintro ⟨h,hn⟩
      rcases le_total 0 x.2 with ht | ht
      · exact Or.inl ⟨⟨h,ht⟩,hn⟩
      · exact Or.inr ⟨⟨h,by linarith⟩,hn⟩
  rw [← heq]
  exact hU.union hmeet hL


lemma segment_split_at_zero (a b : ℝ × ℝ) (h : (0 : ℝ × ℝ) ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ 0 a ∪ segment ℝ 0 b ∧
      segment ℝ 0 a ∩ segment ℝ 0 b ⊆ {0} := by
  have hbt := mem_segment_iff_wbtw.mp h
  constructor
  · apply Set.Subset.antisymm
    · intro z hz
      rw [← insert_endpoints_openSegment] at hz
      rcases hz with rfl | rfl | hz
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inr (right_mem_segment ℝ _ _)
      · have hline : (0 : ℝ × ℝ) ∈ range (AffineMap.lineMap a b : ℝ → ℝ × ℝ) := by
          rw [segment_eq_image_lineMap] at h
          exact image_subset_range _ _ h
        rcases openSegment_subset_union a b hline hz with rfl | hz | hz
        · exact Or.inl (left_mem_segment ℝ _ _)
        · exact Or.inl (by rw [segment_symm]; exact openSegment_subset_segment ℝ a 0 hz)
        · exact Or.inr (openSegment_subset_segment ℝ 0 b hz)
    · exact union_subset
        ((convex_segment a b).segment_subset h (left_mem_segment ℝ a b))
        ((convex_segment a b).segment_subset h (right_mem_segment ℝ a b))
  · rintro z ⟨hzA,hzB⟩
    have h₁ := hbt.trans_left_right (mem_segment_iff_wbtw.mp hzA).symm
    have h₂ := mem_segment_iff_wbtw.mp hzB
    exact (wbtw_swap_left_iff ℝ b).mp ⟨h₁,h₂⟩

lemma polygon_vertex_edge_iff {n : ℕ} (P : Polygon (ℝ × ℝ) n)
    (hP : Function.Injective P)
    (hsimple : ∀ i j : Fin n, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
      ({P i,P (finRotate n i)} ∩ {P j,P (finRotate n j)} : Set (ℝ × ℝ)))
    (k j : Fin n) : P k ∈ P.edgeSet ℝ j ↔ k = j ∨ k = finRotate n j := by
  constructor
  · intro h
    by_cases he : k = j
    · exact Or.inl he
    · have hk : P k ∈ P.edgeSet ℝ k := by
        simpa only [Polygon.edgeSet,affineSegment_eq_segment] using left_mem_segment ℝ (P k) (P (finRotate n k))
      have hh := (hsimple k j he ⟨hk,h⟩).2
      rcases hh with hh | hh
      · exact Or.inl (hP hh)
      · exact Or.inr (hP hh)
  · rintro (rfl | rfl)
    · simpa only [Polygon.edgeSet,affineSegment_eq_segment] using left_mem_segment ℝ (P k) (P (finRotate n k))
    · simpa only [Polygon.edgeSet,affineSegment_eq_segment] using right_mem_segment ℝ (P j) (P (finRotate n j))

/-- At a point of a simple polygon, the remote edges form a closed set avoiding
the point. The remaining one edge or two incident edges are straightened by
the explicit segment-pair chart. -/
theorem polygon_zero_local_chart {n : ℕ} (hn : 3 ≤ n) (P : Polygon (ℝ × ℝ) n)
    (hP : Function.Injective P)
    (hsimple : ∀ i j : Fin n, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
      ({P i,P (finRotate n i)} ∩ {P j,P (finRotate n j)} : Set (ℝ × ℝ)))
    (hz : (0 : ℝ × ℝ) ∈ P.boundary ℝ) :
    ∃ H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), H 0 = 0 ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ 0 ∈ V ∧
        ∀ x ∈ V, x ∈ P.boundary ℝ ↔ (H x).2 = 0 := by
  classical
  have hedgeClosed (j : Fin n) : IsClosed (P.edgeSet ℝ j) := by
    rw [Polygon.edgeSet_eq_image_edgePath]
    exact (isCompact_Icc.image (by unfold Polygon.edgePath; fun_prop)).isClosed
  have hrot (j : Fin n) : j ≠ finRotate n j := fun he ↦
    GallierXu.finRotate_twice_ne_g9 hn j (he.trans (congrArg (finRotate n) he))
  by_cases hv : ∃ k, P k = 0
  · obtain ⟨k,hk⟩ := hv
    let prev := (finRotate n).symm k
    have hprev : finRotate n prev = k := (finRotate n).apply_symm_apply k
    have hpk : prev ≠ k := by intro he; exact hrot prev (hprev.trans he.symm).symm
    have hpn : prev ≠ finRotate n k := by
      intro he
      exact GallierXu.finRotate_twice_ne_g9 hn prev (by rw [hprev]; exact he)
    have ha : P (finRotate n k) ≠ 0 := fun he ↦ hrot k (hP (hk.trans he.symm))
    have hb : P prev ≠ 0 := fun he ↦ hpk (hP (he.trans hk.symm))
    have hinter : segment ℝ 0 (P (finRotate n k)) ∩ segment ℝ 0 (P prev) ⊆ {0} := by
      intro x hx
      have he₁ : x ∈ P.edgeSet ℝ k := by simpa [Polygon.edgeSet,affineSegment_eq_segment,hk] using hx.1
      have he₂ : x ∈ P.edgeSet ℝ prev := by
        simpa only [Polygon.edgeSet,affineSegment_eq_segment,hprev,hk,segment_symm ℝ (P prev) 0] using hx.2
      have hh := hsimple k prev hpk.symm ⟨he₁,he₂⟩
      simp only [Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff,hk,hprev] at hh
      rcases hh.1 with he | he
      · exact he
      · rcases hh.2 with he' | he'
        · exact (hpn (hP (he'.symm.trans he))).elim
        · exact he'
    obtain ⟨H,hH,V,hV,hVz,hchart⟩ := two_segments_local_chart _ _ ha hb hinter
    let F : Set (ℝ × ℝ) := ⋃ j : {j : Fin n // j ≠ k ∧ j ≠ prev}, P.edgeSet ℝ j.val
    have hF : IsClosed F := isClosed_iUnion_of_finite (fun j ↦ hedgeClosed j.val)
    have hzF : (0 : ℝ × ℝ) ∉ F := by
      intro hh
      obtain ⟨j,hj⟩ := mem_iUnion.mp hh
      rw [← hk,polygon_vertex_edge_iff P hP hsimple] at hj
      rcases hj with hj | hj
      · exact j.property.1 hj.symm
      · exact j.property.2 ((finRotate n).injective (hj.symm.trans hprev.symm))
    refine ⟨H,hH,V ∩ Fᶜ,hV.inter hF.isOpen_compl,⟨hVz,hzF⟩,?_⟩
    intro x hx
    rw [← hchart x hx.1]
    constructor
    · intro hp
      obtain ⟨j,hj⟩ := mem_iUnion.mp hp
      by_cases hjk : j = k
      · subst j
        exact Or.inl (by simpa [Polygon.edgeSet,affineSegment_eq_segment,hk] using hj)
      · by_cases hjp : j = prev
        · subst j
          exact Or.inr (by simpa only [Polygon.edgeSet,affineSegment_eq_segment,hprev,hk,
                          segment_symm ℝ (P prev) 0] using hj)
        · exact (hx.2 (mem_iUnion.mpr ⟨⟨j,hjk,hjp⟩,hj⟩)).elim
    · rintro (hs | hs)
      · exact mem_iUnion.mpr ⟨k,by simpa [Polygon.edgeSet,affineSegment_eq_segment,hk] using hs⟩
      · exact mem_iUnion.mpr ⟨prev,by simpa only [Polygon.edgeSet,affineSegment_eq_segment,hprev,hk,
                          segment_symm ℝ (P prev) 0] using hs⟩
  · push Not at hv
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hs : (0 : ℝ × ℝ) ∈ segment ℝ (P i) (P (finRotate n i)) := by
      simpa only [Polygon.edgeSet,affineSegment_eq_segment] using hi
    obtain ⟨hsplit,hinter⟩ := segment_split_at_zero _ _ hs
    obtain ⟨H,hH,V,hV,hVz,hchart⟩ := two_segments_local_chart _ _ (hv i) (hv _) hinter
    let F : Set (ℝ × ℝ) := ⋃ j : {j : Fin n // j ≠ i}, P.edgeSet ℝ j.val
    have hF : IsClosed F := isClosed_iUnion_of_finite (fun j ↦ hedgeClosed j.val)
    have hzF : (0 : ℝ × ℝ) ∉ F := by
      intro hh
      obtain ⟨j,hj⟩ := mem_iUnion.mp hh
      have hh := (hsimple i j.val j.property.symm ⟨hi,hj⟩).1
      rcases hh with hh | hh
      · exact hv i hh.symm
      · exact hv _ hh.symm
    refine ⟨H,hH,V ∩ Fᶜ,hV.inter hF.isOpen_compl,⟨hVz,hzF⟩,?_⟩
    intro x hx
    rw [← hchart x hx.1,← hsplit]
    constructor
    · intro hp
      obtain ⟨j,hj⟩ := mem_iUnion.mp hp
      by_cases he : j = i
      · subst j
        simpa only [Polygon.edgeSet,affineSegment_eq_segment] using hj
      · exact (hx.2 (mem_iUnion.mpr ⟨⟨j,he⟩,hj⟩)).elim
    · intro hs
      exact mem_iUnion.mpr ⟨i,by simpa only [Polygon.edgeSet,affineSegment_eq_segment] using hs⟩


/-- Local straight frontier charts are preserved by any ambient homeomorphism
that maps straight segments to straight segments. -/
theorem polygon_local_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₜ (ℝ × ℝ))
    (heseg : ∀ a b, e '' segment ℝ a b = segment ℝ (e a) (e b))
    {n : ℕ} (hn : 3 ≤ n) (P : Polygon E n) (hP : Function.Injective P)
    (hsimple : ∀ i j : Fin n, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
      ({P i,P (finRotate n i)} ∩ {P j,P (finRotate n j)} : Set E))
    (x : E) (hx : x ∈ P.boundary ℝ) :
    ∃ H : E ≃ₜ (ℝ × ℝ), H x = 0 ∧
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, y ∈ P.boundary ℝ ↔ (H y).2 = 0 := by
  let T := AffineIsometryEquiv.constVAdd ℝ (ℝ × ℝ) (-e x)
  let C := e.trans T.toHomeomorph
  have hC0 : C x = 0 := neg_add_cancel (e x)
  have hCseg (a b : E) : C '' segment ℝ a b = segment ℝ (C a) (C b) := by
    change (T.toHomeomorph ∘ e) '' _ = _
    rw [Set.image_comp,heseg]
    exact image_segment ℝ T.toAffineMap (e a) (e b)
  let Q : Polygon (ℝ × ℝ) n := ⟨fun i ↦ C (P i)⟩
  have hQedge (i : Fin n) : Q.edgeSet ℝ i = C '' P.edgeSet ℝ i := by
    simpa only [Polygon.edgeSet,affineSegment_eq_segment] using (hCseg (P i) (P (finRotate n i))).symm
  have hQsimple : ∀ i j : Fin n, i ≠ j → Q.edgeSet ℝ i ∩ Q.edgeSet ℝ j ⊆
      ({Q i,Q (finRotate n i)} ∩ {Q j,Q (finRotate n j)} : Set (ℝ × ℝ)) := by
    intro i j hij y hy
    rw [hQedge i] at hy
    obtain ⟨z,hzi,hzy⟩ := hy.1
    have hzj : z ∈ P.edgeSet ℝ j := C.injective.mem_set_image.mp (by
      rw [hzy]
      exact hQedge j ▸ hy.2)
    have hh := hsimple i j hij ⟨hzi,hzj⟩
    rw [← hzy]
    constructor
    · rcases hh.1 with hh | hh
      · exact Or.inl (congrArg C hh)
      · exact Or.inr (congrArg C hh)
    · rcases hh.2 with hh | hh
      · exact Or.inl (congrArg C hh)
      · exact Or.inr (congrArg C hh)
  have hQboundary : Q.boundary ℝ = C '' P.boundary ℝ := by
    simp only [Polygon.boundary,Set.image_iUnion,hQedge]
  have hzQ : (0 : ℝ × ℝ) ∈ Q.boundary ℝ := by
    rw [hQboundary,← hC0]
    exact mem_image_of_mem C hx
  obtain ⟨H,hH,V,hV,hVz,hchart⟩ := polygon_zero_local_chart hn Q
    (C.injective.comp hP) hQsimple hzQ
  refine ⟨C.trans H,by change H (C x) = 0; rw [hC0,hH],
    C ⁻¹' V,hV.preimage C.continuous,by change C x ∈ V; rwa [hC0],?_⟩
  intro y hy
  change y ∈ P.boundary ℝ ↔ (H (C y)).2 = 0
  rw [← hchart (C y) hy,hQboundary]
  exact C.injective.mem_set_image.symm

/-- The shear is linear, hence sends every closed segment onto its endpoint
segment. -/
lemma shear_image_segment (t : ℝ) (a b : Plane) :
    shear t '' segment ℝ a b = segment ℝ (shear t a) (shear t b) := by
  let L : Plane →ₗ[ℝ] ℝ × ℝ :=
    { toFun := shear t
      map_add' := fun x y ↦ by
        apply Prod.ext <;> simp [shear,projection,PiLp.add_apply]; ring
      map_smul' := fun r x ↦ by
        apply Prod.ext <;> simp [shear,projection,PiLp.smul_apply]; ring }
  exact image_segment ℝ L.toAffineMap a b


lemma convex_open_half_punctured_connected (O : Set (ℝ × ℝ))
    (hO : IsOpen O) (hconv : Convex ℝ O) (hz : (0,0) ∈ O) :
    IsConnected ((O ∩ {x | 0 ≤ x.2}) \ {0}) ∧
      IsConnected ((O ∩ {x | x.2 ≤ 0}) \ {0}) := by
  obtain ⟨ε,hε,_,hu,hl⟩ := open_plane_axis_points O hO hz
  let f : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ
  constructor
  · exact convex_support_punctured_connected _
      (hconv.inter (convex_halfSpace_ge (.mk f.map_add f.map_smul) 0)) f
      (fun _ h ↦ h.2) ⟨(0,ε),⟨hu,hε.le⟩,hε⟩
  · apply convex_support_punctured_connected _
      (hconv.inter (convex_halfSpace_le (.mk f.map_add f.map_smul) 0)) (-f)
    · intro x hx
      change 0 ≤ -x.2
      exact neg_nonneg.mpr hx.2
    · exact ⟨(0,-ε),⟨hl,by change -ε ≤ 0; linarith⟩,by change 0 < - - ε; linarith⟩

/-- A straight frontier chart gives a basis of connected punctured
neighborhoods in the closed exterior. The chart sends the regular closed set
to one half of a small convex neighborhood, and the supporting-axis argument
proves connectedness after the center is removed. -/
theorem frontier_chart_punctured_exterior {E : Type*} [TopologicalSpace E]
    (D : Set E) (hD : IsClosed D) (hreg : closure (interior D) = D)
    (x : E) (H : E ≃ₜ (ℝ × ℝ)) (hHx : H x = 0)
    (V : Set E) (hV : IsOpen V) (hxV : x ∈ V)
    (hfront : ∀ y ∈ V, y ∈ frontier D ↔ (H y).2 = 0)
    (W : Set E) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      IsConnected (((interior D)ᶜ ∩ U) \ {x}) := by
  let D' := H '' D
  have hD' : IsClosed D' := H.isClosedMap D hD
  have hreg' : closure (interior D') = D' := by
    rw [← H.image_interior,← H.image_closure,hreg]
  have hzero : (0 : ℝ × ℝ) ∈ H '' (V ∩ W) := hHx ▸ mem_image_of_mem H ⟨hxV,hxW⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (H.isOpenMap _ (hV.inter hW)) 0 hzero
  let O : Set (ℝ × ℝ) := Metric.ball 0 r
  have hpre (z : ℝ × ℝ) (hz : z ∈ O) : H.symm z ∈ V ∩ W := by
    obtain ⟨y,hy,he⟩ := hball hz
    rw [← he,H.symm_apply_apply]
    exact hy
  have hf' : ∀ z ∈ O, z ∈ frontier D' ↔ z.2 = 0 := by
    intro z hz
    rw [← H.image_frontier,H.image_eq_preimage_symm]
    change H.symm z ∈ frontier D ↔ z.2 = 0
    simpa only [H.apply_symm_apply] using hfront (H.symm z) (hpre z hz).1
  have hconn : IsConnected ((O \ interior D') \ {0}) := by
    obtain h | h := local_straight_frontier_exterior D' O hD' hreg'
      Metric.isOpen_ball (convex_ball 0 r) (Metric.mem_ball_self hr) hf'
    · rw [h]
      exact (convex_open_half_punctured_connected O Metric.isOpen_ball
        (convex_ball 0 r) (Metric.mem_ball_self hr)).1
    · rw [h]
      exact (convex_open_half_punctured_connected O Metric.isOpen_ball
        (convex_ball 0 r) (Metric.mem_ball_self hr)).2
  let U := H ⁻¹' O
  refine ⟨U,Metric.isOpen_ball.preimage H.continuous,?_,?_,?_⟩
  · change H x ∈ O
    rw [hHx]
    exact Metric.mem_ball_self hr
  · intro y hy
    have hh := (hpre (H y) hy).2
    simpa only [H.symm_apply_apply] using hh
  · have hh := hconn.image H.symm H.symm.continuous.continuousOn
    convert hh using 1
    rw [H.image_symm]
    ext y
    change (y ∉ interior D ∧ H y ∈ O) ∧ y ≠ x ↔
      (H y ∈ O ∧ H y ∉ interior D') ∧ H y ≠ 0
    have hi : H y ∈ interior D' ↔ y ∈ interior D := by
      rw [← H.image_interior]
      exact H.injective.mem_set_image
    have hz : H y = 0 ↔ y = x := by rw [← hHx]; exact H.injective.eq_iff
    simp only [hi,ne_eq,hz,and_comm]


/-- The same local chart controls the closed side of a regular closed set,
by applying the exterior theorem to the closed complementary side. -/
theorem frontier_chart_punctured_closed {E : Type*} [TopologicalSpace E]
    (D : Set E) (hD : IsClosed D) (hreg : closure (interior D) = D)
    (x : E) (H : E ≃ₜ (ℝ × ℝ)) (hHx : H x = 0)
    (V : Set E) (hV : IsOpen V) (hxV : x ∈ V)
    (hfront : ∀ y ∈ V, y ∈ frontier D ↔ (H y).2 = 0)
    (W : Set E) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      IsConnected ((D ∩ U) \ {x}) := by
  let D' := (interior D)ᶜ
  have hi : interior D' = Dᶜ := by rw [interior_compl,hreg]
  have hr : closure (interior D') = D' := by rw [hi,closure_compl]
  have hf : frontier D' = frontier D := by
    rw [frontier_compl,frontier,interior_interior,hreg,hD.frontier_eq]
  have hc := frontier_chart_punctured_exterior D' isOpen_interior.isClosed_compl hr
    x H hHx V hV hxV (by intro y hy; rw [hf]; exact hfront y hy) W hW hxW
  simpa only [hi,compl_compl] using hc

/-- Every point in a topological plane has arbitrarily small connected
punctured neighborhoods, using convex coordinate balls. -/
theorem plane_punctured_neighborhood {E : Type*} [TopologicalSpace E]
    (e : E ≃ₜ (ℝ × ℝ)) (x : E) (W : Set E) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧ IsConnected (U \ {x}) := by
  let T := AffineIsometryEquiv.constVAdd ℝ (ℝ × ℝ) (-e x)
  let H := e.trans T.toHomeomorph
  have hHx : H x = 0 := neg_add_cancel (e x)
  have hz : (0 : ℝ × ℝ) ∈ H '' W := hHx ▸ mem_image_of_mem H hxW
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (H.isOpenMap W hW) 0 hz
  let O : Set (ℝ × ℝ) := Metric.ball 0 r
  let U := H ⁻¹' O
  have hpre (y : E) (hy : y ∈ U) : y ∈ W := H.injective.mem_set_image.mp (hball hy)
  refine ⟨U,Metric.isOpen_ball.preimage H.continuous,?_,hpre,?_⟩
  · change H x ∈ O
    rw [hHx]
    exact Metric.mem_ball_self hr
  · have hh := (convex_open_plane_punctured_connected O Metric.isOpen_ball
      (convex_ball 0 r) (Metric.mem_ball_self hr)).image H.symm H.symm.continuous.continuousOn
    convert hh using 1
    rw [H.image_symm]
    ext y
    change (H y ∈ O ∧ y ≠ x) ↔ (H y ∈ O ∧ H y ≠ 0)
    have hz : H y = 0 ↔ y = x := by rw [← hHx]; exact H.injective.eq_iff
    simp only [ne_eq,hz]


/-- Injective affine maps preserve the literal simple-polygon intersection
condition. -/
lemma affinePolygon_simple {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {n : ℕ} (P : Polygon E n)
    (hsimple : ∀ i j : Fin n, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
      ({P i,P (finRotate n i)} ∩ {P j,P (finRotate n j)} : Set E)) :
    let Q : Polygon F n := ⟨fun i ↦ f (P i)⟩
    ∀ i j : Fin n, i ≠ j → Q.edgeSet ℝ i ∩ Q.edgeSet ℝ j ⊆
      ({Q i,Q (finRotate n i)} ∩ {Q j,Q (finRotate n j)} : Set F) := by
  intro Q i j hij
  have hedge k : Q.edgeSet ℝ k = f '' P.edgeSet ℝ k := by
    simpa only [Polygon.edgeSet,affineSegment_eq_segment] using
      (image_segment ℝ f (P k) (P (finRotate n k))).symm
  rw [hedge i,hedge j,← Set.image_inter hf]
  intro y hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hh := hsimple i j hij hx
  constructor
  · rcases hh.1 with h | h
    · exact Or.inl (congrArg f h)
    · exact Or.inr (congrArg f h)
  · rcases hh.2 with h | h
    · exact Or.inl (congrArg f h)
    · exact Or.inr (congrArg f h)

/-- An affine rectangle has a literal simple four-vertex polygon as its
frontier. This transports the existing complex rectangle certificate. -/
theorem affine_rectangle_polygon (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 2 → ℝ)
    (hab : ∀ i, a i < b i) :
    ∃ P : Polygon Plane 4, Function.Injective P ∧
      (∀ i j : Fin 4, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
        ({P i,P (finRotate 4 i)} ∩ {P j,P (finRotate 4 j)} : Set Plane)) ∧
      frontier (e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}) = P.boundary ℝ := by
  let P := cairnsRectanglePolygon (a 0) (b 0) (a 1) (b 1) (hab 0) (hab 1)
  let f : ℂ →ᵃ[ℝ] Plane := e.toAffineMap.comp
    (planeCoordinates.comp Complex.equivRealProdCLM.toLinearMap).toAffineMap
  let H : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph.trans
    ((shear 0).symm.trans e.toHomeomorph)
  have hf : Function.Injective f := by
    have heq : (f : ℂ → Plane) = H := by
      funext z
      exact congrArg e (planeCoordinates_eq _)
    rw [heq]
    exact H.injective
  let Q : Polygon Plane 4 := ⟨fun i ↦ f (P i)⟩
  have hP := cairns_rectangle_polygon_vertices_injective (a 0) (b 0) (a 1) (b 1) (hab 0) (hab 1)
  have hs : ∀ i j : Fin 4, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
      ({P i,P (finRotate 4 i)} ∩ {P j,P (finRotate 4 j)} : Set ℂ) := by
    intro i j hij
    simpa only [Set.image_inter hP,Set.image_pair] using
      cairns_rectangle_edge_intersection_subset (a 0) (b 0) (a 1) (b 1) (hab 0) (hab 1) i j hij
  refine ⟨Q,hf.comp hP,affinePolygon_simple f hf P hs,?_⟩
  have hpoint (u v : ℝ) : f ((u : ℂ) + v*Complex.I) = e (planeCoordinates (u,v)) := by
    change e (planeCoordinates (Complex.equivRealProdCLM ((u : ℂ) + v*Complex.I))) = _
    apply congrArg e
    apply congrArg planeCoordinates
    change (((u : ℂ) + v*Complex.I).re,((u : ℂ) + v*Complex.I).im) = (u,v)
    simp
  have hQ : Q.vertices = ![e (planeCoordinates (a 0,a 1)),e (planeCoordinates (b 0,a 1)),
      e (planeCoordinates (b 0,b 1)),e (planeCoordinates (a 0,b 1))] := by
    funext i
    fin_cases i <;> exact hpoint _ _
  rw [affine_rectangle_frontier e a b hab]
  ext y
  simp only [Polygon.boundary,Set.mem_iUnion,Polygon.edgeSet,affineSegment_eq_segment,
    Fin.exists_fin_succ]
  simp only [hQ]
  norm_num [finRotate_apply,Fin.succ]
  rw [segment_symm ℝ (e (planeCoordinates (b 0,b 1))) (e (planeCoordinates (a 0,b 1))),
    segment_symm ℝ (e (planeCoordinates (a 0,b 1))) (e (planeCoordinates (a 0,a 1)))]
  tauto


/-- Every point of the literal polygonal annulus has arbitrarily small
connected punctured neighborhoods. Interior points use planar balls; points
on either boundary use the exact local straight frontier charts. -/
theorem polygonal_annulus_punctured_neighborhood
    (D R : Set Plane) (hD : IsClosed D) (hregular : closure (interior D) = D)
    (hpolygon : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n, Function.Injective P ∧
      (∀ i j : Fin n, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
        ({P i,P (finRotate n i)} ∩ {P j,P (finRotate n j)} : Set Plane)) ∧
      frontier D = P.boundary ℝ)
    (hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧ R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})
    (hcontain : D ⊆ interior R) (x : Plane) (hx : x ∈ R \ interior D)
    (W : Set Plane) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      IsConnected (((R \ interior D) ∩ U) \ {x}) := by
  by_cases hxR : x ∈ interior R
  · by_cases hxD : x ∈ D
    · obtain ⟨n,hn,P,hP,hs,hf⟩ := hpolygon
      have hxfront : x ∈ frontier D := hD.frontier_eq ▸ ⟨hxD,hx.2⟩
      obtain ⟨H,hHx,V,hV,hxV,hchart⟩ := polygon_local_chart (shear 0) (shear_image_segment 0)
        hn P hP hs x (hf ▸ hxfront)
      obtain ⟨U,hU,hxU,hsub,hconn⟩ := frontier_chart_punctured_exterior D hD hregular
        x H hHx V hV hxV (by intro y hy; rw [hf]; exact hchart y hy)
        (W ∩ interior R) (hW.inter isOpen_interior) ⟨hxW,hxR⟩
      refine ⟨U,hU,hxU,fun y hy ↦ (hsub hy).1,?_⟩
      have heq : (R \ interior D) ∩ U = (interior D)ᶜ ∩ U := by
        ext y
        constructor
        · rintro ⟨⟨_,hn⟩,hy⟩; exact ⟨hn,hy⟩
        · rintro ⟨hn,hy⟩; exact ⟨⟨interior_subset (hsub hy).2,hn⟩,hy⟩
      rwa [heq]
    · obtain ⟨U,hU,hxU,hsub,hconn⟩ := plane_punctured_neighborhood (shear 0) x
        (W ∩ (interior R ∩ Dᶜ)) (hW.inter (isOpen_interior.inter hD.isOpen_compl))
        ⟨hxW,hxR,hxD⟩
      refine ⟨U,hU,hxU,fun y hy ↦ (hsub hy).1,?_⟩
      have heq : (R \ interior D) ∩ U = U := by
        apply inter_eq_right.mpr
        intro y hy
        exact ⟨interior_subset (hsub hy).2.1,fun hi ↦ (hsub hy).2.2 (interior_subset hi)⟩
      rwa [heq]
  · obtain ⟨e,a,b,hab,rfl⟩ := hrectangle
    let R := e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i}
    have hR : IsClosed R := (affine_rectangle_compact e a b).isClosed
    have hr : closure (interior R) = R := affine_rectangle_regular e a b hab
    have hxfront : x ∈ frontier R := hR.frontier_eq ▸ ⟨hx.1,hxR⟩
    have hxD : x ∉ D := fun hd ↦ hxR (hcontain hd)
    obtain ⟨P,hP,hs,hf⟩ := affine_rectangle_polygon e a b hab
    obtain ⟨H,hHx,V,hV,hxV,hchart⟩ := polygon_local_chart (shear 0) (shear_image_segment 0)
      (by decide : 3 ≤ 4) P hP hs x (hf ▸ hxfront)
    obtain ⟨U,hU,hxU,hsub,hconn⟩ := frontier_chart_punctured_closed R hR hr
      x H hHx V hV hxV (by intro y hy; rw [hf]; exact hchart y hy)
      (W ∩ Dᶜ) (hW.inter hD.isOpen_compl) ⟨hxW,hxD⟩
    refine ⟨U,hU,hxU,fun y hy ↦ (hsub hy).1,?_⟩
    have heq : (R \ interior D) ∩ U = R ∩ U := by
      ext y
      constructor
      · rintro ⟨hy,hu⟩; exact ⟨hy.1,hu⟩
      · rintro ⟨hy,hu⟩; exact ⟨⟨hy,fun hi ↦ (hsub hu).2 (interior_subset hi)⟩,hu⟩
    change IsConnected (((R \ interior D) ∩ U) \ {x})
    rwa [heq]

/-- Ambient homeomorphisms transport the connected punctured-neighborhood
basis needed to recognize vertex links. -/
theorem punctured_neighborhood_image {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (e : E ≃ₜ F) (A : Set E)
    (hlocal : ∀ x ∈ A, ∀ W : Set E, IsOpen W → x ∈ W →
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧ IsConnected ((A ∩ U) \ {x})) :
    ∀ y ∈ e '' A, ∀ W : Set F, IsOpen W → y ∈ W →
      ∃ U : Set F, IsOpen U ∧ y ∈ U ∧ U ⊆ W ∧ IsConnected (((e '' A) ∩ U) \ {y}) := by
  rintro _ ⟨x,hx,rfl⟩ W hW hxW
  obtain ⟨U,hU,hxU,hsub,hconn⟩ := hlocal x hx (e ⁻¹' W) (hW.preimage e.continuous) hxW
  refine ⟨e '' U,e.isOpenMap U hU,mem_image_of_mem e hxU,?_,?_⟩
  · rintro y ⟨z,hz,rfl⟩
    exact hsub hz
  · have hh := hconn.image e e.continuous.continuousOn
    convert hh using 1
    rw [Set.image_sdiff e.injective,Set.image_inter e.injective,Set.image_singleton]


lemma openSegment_face_contains_endpoints {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hp : Function.Injective p)
    (hfaces : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (u v : Fin N) (huv : u ≠ v) (he : ({u,v} : Finset (Fin N)) ∈ K.faces)
    (s : Finset (Fin N)) (hs : s ∈ K.faces) (x : ℝ × ℝ)
    (hx : x ∈ openSegment ℝ (p u) (p v)) (hxs : x ∈ convexHull ℝ (p '' (s : Set (Fin N)))) :
    ({u,v} : Finset (Fin N)) ⊆ s := by
  classical
  have hxe : x ∈ convexHull ℝ (p '' (({u,v} : Finset (Fin N)) : Set (Fin N))) := by
    simpa only [Finset.coe_pair,Set.image_pair,convexHull_pair] using openSegment_subset_segment ℝ _ _ hx
  have hh : x ∈ convexHull ℝ (p '' ((({u,v} : Finset (Fin N)) ∩ s : Finset (Fin N)) : Set (Fin N))) := by
    rw [← hfaces {u,v} he s hs]
    exact ⟨hxe,hxs⟩
  have hend (a b : Fin N) (hab : a ≠ b) (heq : ({u,v} : Finset (Fin N)) = {a,b})
      (hxopen : x ∈ openSegment ℝ (p a) (p b)) : a ∈ s := by
    by_contra ha
    have hsub : (({u,v} : Finset (Fin N)) ∩ s : Finset (Fin N)) ⊆ {b} := by
      intro z hz
      rw [heq] at hz
      have hz' := Finset.mem_inter.mp hz
      rcases Finset.mem_insert.mp hz'.1 with rfl | hz
      · exact (ha hz'.2).elim
      · exact hz
    have hh' := convexHull_mono (Set.image_mono (show
      ((({u,v} : Finset (Fin N)) ∩ s : Finset (Fin N)) : Set (Fin N)) ⊆ {b} from fun z hz ↦ Finset.mem_singleton.mp (hsub hz))) hh
    have hxb : x = p b := by simpa only [Set.image_singleton,convexHull_singleton,Set.mem_singleton_iff] using hh'
    rw [hxb] at hxopen
    exact hab (hp ((right_mem_openSegment_iff).mp hxopen))
  have hu := hend u v huv rfl hx
  have hv := hend v u huv.symm (Finset.pair_comm u v) (by rwa [openSegment_symm])
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hu
  · exact (Finset.mem_singleton.mp hz) ▸ hv

lemma boundary_edge_unique_triangle {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (hpure : GallierXu.PureTwo K) (u v : Fin N) (he : GallierXu.boundaryEdge K u v) :
    ∃ t : Finset (Fin N), t ∈ K.faces ∧ t.card = 3 ∧ ({u,v} : Finset (Fin N)) ⊆ t ∧
      ∀ s ∈ K.faces, ({u,v} : Finset (Fin N)) ⊆ s → s ⊆ t := by
  classical
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp he.2.2
  have htm : t ∈ (GallierXu.simplices K 2).filter
      (fun s ↦ ({u,v} : Finset (Fin N)) ⊆ s) := by rw [ht]; simp
  have hdata := Finset.mem_filter.mp htm
  have htdata : t ∈ K.faces ∧ t.card = 3 := by
    simpa only [GallierXu.simplices,Finset.mem_filter,Finset.mem_univ,true_and] using hdata.1
  refine ⟨t,htdata.1,htdata.2,hdata.2,?_⟩
  intro s hs hes
  obtain ⟨q,hq,hqc,hsq⟩ := hpure s hs
  have hqm : q ∈ (GallierXu.simplices K 2).filter
      (fun s ↦ ({u,v} : Finset (Fin N)) ⊆ s) := by
    simp only [GallierXu.simplices,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨⟨hq,hqc⟩,hes.trans hsq⟩
  rw [ht,Finset.mem_singleton] at hqm
  exact hqm ▸ hsq

/-- An exposed supporting-line point of a convex hull is not an interior
point. A segment toward the opposite side enters every neighborhood and
contradicts the supporting inequality. -/
lemma orientedArea_support_not_interior (a b w x : ℝ × ℝ) (S : Set (ℝ × ℝ))
    (hw : orientedArea a b w ≠ 0) (hx : orientedArea a b x = 0)
    (hS : ∀ y ∈ S, 0 ≤ orientedArea a b y * orientedArea a b w) : x ∉ interior S := by
  intro hxi
  let q := (2:ℝ) • x + (-1:ℝ) • w
  have hq : orientedArea a b q = -orientedArea a b w := by
    rw [orientedArea_blend a b x w 2 (-1) (by norm_num),hx]
    ring
  have hcl : x ∈ closure (openSegment ℝ x q) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ x q)
  obtain ⟨y,hyi,hy⟩ := mem_closure_iff.mp hcl (interior S) isOpen_interior hxi
  obtain ⟨α,β,hα,hβ,hsum,rfl⟩ := hy
  have hh := hS _ (interior_subset hyi)
  rw [orientedArea_blend a b x q α β hsum,hx,hq] at hh
  have hsq : 0 < (orientedArea a b w)^2 := sq_pos_of_ne_zero hw
  nlinarith [mul_pos hβ hsq]

/-- In an exact straight triangle complex, each one-triangle edge lies on the
ambient frontier of the geometric union. Away from its endpoints the other
faces can be excluded by a finite closed set; the remaining triangle has
that edge on a supporting line. Closure includes both endpoints. -/
theorem straightComplex_boundaryEdge_frontier {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hp : Function.Injective p) (hpure : GallierXu.PureTwo K)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hfaces : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (u v : Fin N) (he : GallierXu.boundaryEdge K u v) :
    segment ℝ (p u) (p v) ⊆
      frontier (⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N)))) := by
  classical
  let A := ⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N)))
  obtain ⟨t,ht,htc,het,hunique⟩ := boundary_edge_unique_triangle K hpure u v he
  obtain ⟨w,hwu,hwv,htw⟩ := GallierXu.triangle_third_vertex_g9 htc he.1
    (het (by simp)) (het (by simp))
  have hw := face_triple_orientedArea_ne_zero K p hi u v w he.1 hwu.symm hwv.symm (htw ▸ ht)
  let weight := fun y ↦ orientedArea (p u) (p v) y * orientedArea (p u) (p v) (p w)
  have hhalf : Convex ℝ {y | 0 ≤ weight y} := by
    intro a ha b hb α β hα hβ hsum
    change 0 ≤ orientedArea (p u) (p v) (α • a + β • b) * _
    rw [orientedArea_blend _ _ a b α β hsum,add_mul]
    exact add_nonneg (by simpa only [mul_assoc] using mul_nonneg hα ha)
      (by simpa only [mul_assoc] using mul_nonneg hβ hb)
  have htsub : convexHull ℝ (p '' (t : Set (Fin N))) ⊆ {y | 0 ≤ weight y} := by
    apply convexHull_min _ hhalf
    rintro y ⟨z,hz,rfl⟩
    rw [htw] at hz
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simp [weight,orientedArea,mul_comm]
    · simp [weight,orientedArea,mul_comm]
    · change 0 ≤ orientedArea (p u) (p v) (p z) * orientedArea (p u) (p v) (p z)
      exact mul_self_nonneg _
  have hopenSub : openSegment ℝ (p u) (p v) ⊆ frontier A := by
    intro x hx
    let J := {s : Finset (Fin N) // s ∈ K.faces ∧ ¬ ({u,v} : Finset (Fin N)) ⊆ s}
    let F : Set (ℝ × ℝ) := ⋃ s : J, convexHull ℝ (p '' (s.val : Set (Fin N)))
    have hF : IsClosed F := isClosed_iUnion_of_finite (fun s ↦
      (s.val.finite_toSet.image p).isClosed_convexHull ℝ)
    have hxF : x ∉ F := by
      intro hh
      obtain ⟨s,hs⟩ := mem_iUnion.mp hh
      exact s.property.2 (openSegment_face_contains_endpoints K p hp hfaces u v he.1 he.2.1
        s.val s.property.1 x hx hs)
    have hxA : x ∈ A := by
      refine mem_iUnion.mpr ⟨{u,v},mem_iUnion.mpr ⟨he.2.1,?_⟩⟩
      simpa only [Finset.coe_pair,Set.image_pair,convexHull_pair] using openSegment_subset_segment ℝ _ _ hx
    refine ⟨subset_closure hxA,?_⟩
    intro hxi
    have hsub : interior A ∩ Fᶜ ⊆ convexHull ℝ (p '' (t : Set (Fin N))) := by
      rintro y ⟨hy,hyF⟩
      obtain ⟨s,hs,hys⟩ := mem_iUnion₂.mp (interior_subset hy)
      by_cases hes : ({u,v} : Finset (Fin N)) ⊆ s
      · exact convexHull_mono (Set.image_mono (hunique s hs hes)) hys
      · exact (hyF (mem_iUnion.mpr ⟨⟨s,hs,hes⟩,hys⟩)).elim
    have hxi' : x ∈ interior (convexHull ℝ (p '' (t : Set (Fin N)))) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
        ((isOpen_interior.inter hF.isOpen_compl).mem_nhds ⟨hxi,hxF⟩) hsub)
    exact orientedArea_support_not_interior (p u) (p v) (p w) x _ hw
      (orientedArea_segment_zero _ _ x (openSegment_subset_segment ℝ _ _ hx)) htsub hxi'
  rw [← closure_openSegment (𝕜 := ℝ) (p u) (p v)]
  exact closure_minimal hopenSub isClosed_frontier


/-- Consecutive polygon edges give paths from the first vertex to every
boundary point, without any simplicity assumption. -/
theorem polygon_boundary_isPathConnected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (P : Polygon E n) : IsPathConnected (P.boundary ℝ) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hedge (i : Fin (m+1)) : segment ℝ (P i) (P (finRotate (m+1) i)) ⊆ P.boundary ℝ := by
    intro x hx
    exact mem_iUnion.mpr ⟨i,by simpa only [Polygon.edgeSet,affineSegment_eq_segment] using hx⟩
  have hvertex (i : Fin (m+1)) : P i ∈ P.boundary ℝ := hedge i (left_mem_segment ℝ _ _)
  have hpaths : ∀ i : Fin (m+1), JoinedIn (P.boundary ℝ) (P 0) (P i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact JoinedIn.refl (hvertex 0)
    | succ i ih =>
      have hr : finRotate (m+1) i.castSucc = i.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (by exact Fin.castSucc_ne_last i)]
        rfl
      apply ih.trans
      apply JoinedIn.of_segment_subset
      simpa only [hr] using hedge i.castSucc
  refine ⟨P 0,hvertex 0,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hs : x ∈ segment ℝ (P i) (P (finRotate (m+1) i)) := by
    simpa only [Polygon.edgeSet,affineSegment_eq_segment] using hi
  exact (hpaths i).trans (JoinedIn.of_segment_subset
    (((convex_segment (P i) (P (finRotate (m+1) i))).segment_subset
      (left_mem_segment ℝ _ _) hs).trans (hedge i)))

end HolomorphicAnosov.Topology.CairnsStrip
