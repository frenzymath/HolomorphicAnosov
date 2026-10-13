import HolomorphicAnosov.Topology.GallierXuIntervalLinkAdapter
import HolomorphicAnosov.Topology.BoundaryConeCompactG9
import HolomorphicAnosov.Topology.BoundaryCycleCircleG9
import Mathlib.Topology.Homeomorph.Quotient
import HolomorphicAnosov.Topology.HatcherPlanarEmbeddingOpenImage

/-!
# Local charts and frontier detection for a finite surface

Gallier--Xu §3.1, Definition 3.3, pp.32--34: a circular vertex link has a disk
star and an interval link has a half-disk star. The explicit barycentric
radial coordinates below show that every point outside the listed boundary
cycles has an open disk or strip chart. Hatcher Theorem 2B.3, p.172, makes
its image under a planar embedding interior. Compactness then puts the
entire ambient frontier on the listed cycles.
-/

open Set
namespace HolomorphicAnosov.Topology.GallierXu

/-- Polar coordinates for the closed disk, with height zero on the boundary. -/
noncomputable def circleConeDiskMap : C(Circle × Icc (0 : ℝ) 1, ℂ) where
  toFun p := (1 - (p.2 : ℝ)) • (p.1 : ℂ)
  continuous_toFun := (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
    (continuous_subtype_val.comp continuous_fst)

/-- The radial norm recovers one minus the cone height. -/
theorem circleConeDiskMap_norm (p : Circle × Icc (0 : ℝ) 1) :
    ‖circleConeDiskMap p‖ = 1 - (p.2 : ℝ) := by
  change ‖(1 - (p.2 : ℝ)) • (p.1 : ℂ)‖ = _
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr p.2.property.2)]

/-- Radial disk coordinates identify precisely the upper rim of the cylinder. -/
theorem circleConeDiskMap_eq_iff (p q : Circle × Icc (0 : ℝ) 1) :
    circleConeDiskMap p = circleConeDiskMap q ↔
      p.2 = q.2 ∧ ((p.2 : ℝ) = 1 ∨ p.1 = q.1) := by
  constructor
  · intro h
    have hn := congrArg norm h
    rw [circleConeDiskMap_norm, circleConeDiskMap_norm] at hn
    have ht : p.2 = q.2 := Subtype.ext (by linarith)
    refine ⟨ht, ?_⟩
    by_cases hp : (p.2 : ℝ) = 1
    · exact Or.inl hp
    · right
      apply Subtype.ext
      change (1 - (p.2 : ℝ)) • (p.1 : ℂ) = (1 - (q.2 : ℝ)) • (q.1 : ℂ) at h
      rw [← ht] at h
      exact (smul_right_injective _ (sub_ne_zero.mpr (Ne.symm hp))) h
  · rintro ⟨ht, hp | hbase⟩
    · change (1 - (p.2 : ℝ)) • (p.1 : ℂ) = (1 - (q.2 : ℝ)) • (q.1 : ℂ)
      rw [← ht, hp]
      simp
    · change (1 - (p.2 : ℝ)) • (p.1 : ℂ) = (1 - (q.2 : ℝ)) • (q.1 : ℂ)
      rw [ht, hbase]

/-- Every point of the unit disk has radial coordinates. At zero choose any
circle point; elsewhere divide the point by its positive norm. -/
theorem circleConeDiskMap_range : range circleConeDiskMap = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, circleConeDiskMap_norm]
    linarith [p.2.property.1]
  · intro hz
    have hnorm : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    by_cases hzero : z = 0
    · subst z
      exact ⟨(1, ⟨1, by simp⟩), by simp [circleConeDiskMap]⟩
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
      let u : Circle := ⟨‖z‖⁻¹ • z, by
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z),
          inv_mul_cancel₀ hn]⟩
      refine ⟨(u, ⟨1 - ‖z‖, sub_nonneg.mpr hnorm, by linarith [norm_nonneg z]⟩), ?_⟩
      change (1 - (1 - ‖z‖)) • (‖z‖⁻¹ • z) = z
      rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ hn, one_smul]


/-- Compact quotient maps with the same fibers identify their Hausdorff targets. -/
noncomputable def compactFiberHomeomorph_g9 {A Y Z : Type*}
    [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : C(A, Y)) (g : C(A, Z))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) : Y ≃ₜ Z := by
  let ef : Quotient (Setoid.ker f) ≃ₜ Y :=
    (Homeomorph.quotientKerEquivRange
      (f.continuous.isClosedMap.isStrictMap f.continuous)).trans
        ((Homeomorph.setCongr hf.range_eq).trans (Homeomorph.Set.univ Y))
  let eg : Quotient (Setoid.ker g) ≃ₜ Z :=
    (Homeomorph.quotientKerEquivRange
      (g.continuous.isClosedMap.isStrictMap g.continuous)).trans
        ((Homeomorph.setCongr hg.range_eq).trans (Homeomorph.Set.univ Z))
  exact ef.symm.trans ((Homeomorph.Quotient.congrRight hfg).trans eg)

/-- The compact quotient homeomorphism agrees with the two original quotient maps. -/
theorem compactFiberHomeomorph_apply_g9 {A Y Z : Type*}
    [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : C(A, Y)) (g : C(A, Z))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    compactFiberHomeomorph_g9 f g hf hg hfg (f a) = g a := by
  let ef : Quotient (Setoid.ker f) ≃ₜ Y :=
    (Homeomorph.quotientKerEquivRange
      (f.continuous.isClosedMap.isStrictMap f.continuous)).trans
        ((Homeomorph.setCongr hf.range_eq).trans (Homeomorph.Set.univ Y))
  have he : ef (Quotient.mk _ a) = f a := rfl
  rw [← he]
  simp only [compactFiberHomeomorph_g9, Homeomorph.trans_apply]
  erw [ef.symm_apply_apply]
  rfl


/-- A cycle omitting a vertex has zero barycentric coordinate at that vertex. -/
theorem cycleCarrier_coordinate_zero_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (v : Fin N) (hv : v ∉ l) (x : ↥(cycleCarrier (K := K) l)) : x.val.val v = 0 := by
  obtain ⟨a, b, ⟨i, hi | hi⟩, α, β, _, _, _, he⟩ := x.property
  all_goals
    have ha : v ≠ a := by
      intro h
      apply hv
      first | rw [h, ← hi.1]; exact List.get_mem _ _
            | rw [h, ← hi.2]; exact List.get_mem _ _
    have hb : v ≠ b := by
      intro h
      apply hv
      first | rw [h, ← hi.2]; exact List.get_mem _ _
            | rw [h, ← hi.1]; exact List.get_mem _ _
    have hh := congrFun he v
    simpa [ha, hb] using hh.symm

/-- Radial coordinates for a vertex fan whose link is the given cycle. -/
def vertexCycleRadial_g9 {N : ℕ} (v : Fin N) (x : Fin N → ℝ) (t : ℝ) : Fin N → ℝ :=
  (1 - t) • x + t • Pi.single v 1

/-- The fan radial map has exactly the usual cone fibers. -/
theorem vertexCycleRadial_eq_iff_g9 {N : ℕ}
    (v : Fin N) (x y : Fin N → ℝ) (hx : x v = 0) (hy : y v = 0) (t s : ℝ) :
    vertexCycleRadial_g9 v x t = vertexCycleRadial_g9 v y s ↔
      t = s ∧ (t = 1 ∨ x = y) := by
  constructor
  · intro h
    have ht : t = s := by
      have hh := congrFun h v
      simpa [vertexCycleRadial_g9, hx, hy] using hh
    refine ⟨ht, ?_⟩
    by_cases hone : t = 1
    · exact Or.inl hone
    · right
      subst s
      apply smul_right_injective (Fin N → ℝ) (sub_ne_zero.mpr (Ne.symm hone))
      exact add_right_cancel h
  · rintro ⟨rfl, ht | rfl⟩
    · simp [vertexCycleRadial_g9, ht]
    · rfl

/-- Coning every edge of a vertex link gives points in the original carrier. -/
theorem vertexCycleRadial_mem_carrier_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) (v : Fin N)
    (hfan : ∀ i : Fin l.length,
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces)
    (x : ↥(cycleCarrier (K := K) l)) {t : ℝ} (ht : t ∈ Icc 0 1) :
    vertexCycleRadial_g9 v x.val.val t ∈ carrier K := by
  have hconv : Convex ℝ {f : Fin N → ℝ | (∀ w, 0 ≤ f w) ∧ ∑ w, f w = 1} := by
    intro f hf g hg a b ha hb hab
    refine ⟨fun w ↦ add_nonneg (mul_nonneg ha (hf.1 w)) (mul_nonneg hb (hg.1 w)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]
  refine ⟨hconv x.val.property.1
    (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩)
    (sub_nonneg.mpr ht.2) ht.1 (by ring), ?_⟩
  obtain ⟨a, b, ⟨i, hi | hi⟩, α, β, _, _, _, he⟩ := x.property
  all_goals
    refine ⟨_, hfan i, ?_⟩
    intro w hw
    have hn : w ≠ v ∧ w ≠ l.get i ∧ w ≠ l.get (finRotate l.length i) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hw
    have hxa : w ≠ a := by first | exact hi.1 ▸ hn.2.1 | exact hi.2 ▸ hn.2.2
    have hxb : w ≠ b := by first | exact hi.2 ▸ hn.2.2 | exact hi.1 ▸ hn.2.1
    have hxw : x.val.val w = 0 := by
      have hh := congrFun he w
      simpa [hxa, hxb] using hh.symm
    simp [vertexCycleRadial_g9, hxw, hn.1]

/-- The cycle-link cone is a continuous map into the original surface. -/
def vertexCycleRadialMap_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) (v : Fin N)
    (hfan : ∀ i : Fin l.length,
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces) :
    C(↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1, ↥(carrier K)) where
  toFun p := ⟨vertexCycleRadial_g9 v p.1.val.val p.2.val,
    vertexCycleRadial_mem_carrier_g9 K l v hfan p.1 p.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))).add
        ((continuous_subtype_val.comp continuous_snd).smul continuous_const)

/-- A vertex fan with an embedded circular link is a disk, with exact radial
coordinates. The base cycle omits the apex, so its apex coordinate is zero;
the coordinate at the apex then recovers the radial height. The remaining
coordinates recover the base except at height one. Thus the fan map and polar
disk map have exactly the same fibers, and compactness identifies their images.
Source: Gallier--Xu Definition 3.3 and the vertex-star neighborhoods in §3.1,
pp.32--34; the radial formula of Proposition 3.2 / Note F.4, pp.31,167.
-/
theorem vertexCycle_disk_homeomorph_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) (v : Fin N)
    (hv : v ∉ l)
    (hfan : ∀ i : Fin l.length,
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces)
    (e : Circle ≃ₜ ↥(cycleCarrier (K := K) l)) :
    ∃ H : ↥(range (vertexCycleRadialMap_g9 K l v hfan)) ≃ₜ Metric.closedBall (0 : ℂ) 1,
      ∀ p : ↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1,
        (H ⟨vertexCycleRadialMap_g9 K l v hfan p, ⟨p, rfl⟩⟩ : ℂ) =
          (1 - (p.2 : ℝ)) • (e.symm p.1 : ℂ) := by
  have : CompactSpace ↥(cycleCarrier (K := K) l) :=
    isCompact_iff_compactSpace.mp (cycleCarrier_isCompact_g9 K l)
  let f : C(↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1,
      ↥(range (vertexCycleRadialMap_g9 K l v hfan))) :=
    ⟨Set.rangeFactorization (vertexCycleRadialMap_g9 K l v hfan),
      (vertexCycleRadialMap_g9 K l v hfan).continuous.rangeFactorization⟩
  let polar : C(↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun p ↦ circleConeDiskMap (e.symm p.1, p.2), circleConeDiskMap.continuous.comp
      ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hpolar (p) : polar p ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [← circleConeDiskMap_range]
    exact ⟨(e.symm p.1, p.2), rfl⟩
  let g : C(↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1, Metric.closedBall (0 : ℂ) 1) :=
    ⟨fun p ↦ ⟨polar p, hpolar p⟩, polar.continuous.subtype_mk _⟩
  have hf : Function.Surjective f := Set.rangeFactorization_surjective
  have hg : Function.Surjective g := by
    intro z
    have hz : z.val ∈ range circleConeDiskMap := by
      rw [circleConeDiskMap_range]
      exact z.property
    obtain ⟨p, hp⟩ := hz
    refine ⟨(e p.1, p.2), ?_⟩
    apply Subtype.ext
    change circleConeDiskMap (e.symm (e p.1), p.2) = z.val
    simpa only [e.symm_apply_apply, Prod.eta] using hp
  have hker (p q) : f p = f q ↔ g p = g q := by
    have he : f p = f q ↔
        vertexCycleRadial_g9 v p.1.val.val p.2.val =
          vertexCycleRadial_g9 v q.1.val.val q.2.val :=
      ⟨fun h ↦ congrArg (fun z ↦ z.val.val) h, fun h ↦ Subtype.ext (Subtype.ext h)⟩
    have he' : g p = g q ↔
        circleConeDiskMap (e.symm p.1, p.2) = circleConeDiskMap (e.symm q.1, q.2) :=
      ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
    rw [he, he']
    rw [vertexCycleRadial_eq_iff_g9 v _ _ (cycleCarrier_coordinate_zero_g9 K l v hv p.1)
      (cycleCarrier_coordinate_zero_g9 K l v hv q.1), circleConeDiskMap_eq_iff]
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.ext_iff]
  refine ⟨compactFiberHomeomorph_g9 f g hf hg hker, fun p ↦ ?_⟩
  exact congrArg Subtype.val (compactFiberHomeomorph_apply_g9 f g hf hg hker p)

/-- Every point supported on a triangle of a vertex fan is reached by radial
coordinates. At apex mass one the old coordinates vanish. Otherwise divide the
two edge coordinates by one minus the apex mass to recover the base edge point.
Source: Gallier--Xu Definition 3.3, p.32, barycentric realization.
-/
theorem vertexCycleRadial_covers_triangle_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) (v : Fin N)
    (hv : v ∉ l)
    (hfan : ∀ i : Fin l.length,
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces)
    (i : Fin l.length) (hne : l.get i ≠ l.get (finRotate l.length i))
    (x : ↥(carrier K))
    (hsupport : ∀ w ∉ ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)),
      x.val w = 0) :
    ∃ p : ↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1,
      vertexCycleRadialMap_g9 K l v hfan p = x := by
  classical
  let a := l.get i
  let b := l.get (finRotate l.length i)
  have hva : v ≠ a := fun h ↦ hv (h ▸ List.get_mem _ _)
  have hvb : v ≠ b := fun h ↦ hv (h ▸ List.get_mem _ _)
  have hab : a ≠ b := hne
  have hface : ({a, b} : Finset (Fin N)) ∈ K.faces :=
    (K.isRelLowerSet_faces (hfan i)).2 (by intro w hw; simp_all [a, b]) (by simp)
  have hedge : cycleEdge l a b := ⟨i, Or.inl ⟨rfl, rfl⟩⟩
  have hsum : x.val v + x.val a + x.val b = 1 := by
    have hh : ∑ w ∈ ({v, a, b} : Finset (Fin N)), x.val w = ∑ w, x.val w := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      exact hsupport w hw
    simpa [hva, hvb, hab, add_assoc, x.property.1.2] using hh
  let t := x.val v
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨x.property.1.1 v, x.property.1.2 ▸
    Finset.single_le_sum (fun w _ ↦ x.property.1.1 w) (Finset.mem_univ v)⟩
  have hzero (w : Fin N) (hwv : w ≠ v) (hwa : w ≠ a) (hwb : w ≠ b) : x.val w = 0 :=
    hsupport w (by change w ∉ ({v, a, b} : Finset (Fin N)); simp [hwv, hwa, hwb])
  by_cases htone : t = 1
  · have hza : x.val a = 0 := by linarith [x.property.1.1 a, x.property.1.1 b]
    have hzb : x.val b = 0 := by linarith [x.property.1.1 a, x.property.1.1 b]
    let y : ↥(carrier K) := ⟨Pi.single a 1,
      (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩),
      {a}, K.singleton_mem a, by intro w hw; simp_all⟩
    have hy : y ∈ cycleCarrier l := ⟨a, b, hedge, left_mem_segment ℝ _ _⟩
    refine ⟨(⟨y, hy⟩, ⟨1, by simp⟩), ?_⟩
    apply Subtype.ext
    funext w
    change vertexCycleRadial_g9 v y.val 1 w = x.val w
    by_cases hwv : w = v
    · subst w
      simpa [vertexCycleRadial_g9] using htone.symm
    by_cases hwa : w = a
    · subst w
      simp [vertexCycleRadial_g9, Ne.symm hva, hza]
    by_cases hwb : w = b
    · subst w
      simp [vertexCycleRadial_g9, Ne.symm hvb, hzb]
    · simp [vertexCycleRadial_g9, hwv, hzero w hwv hwa hwb]
  · have hden : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 htone)
    let α := x.val a / (1 - t)
    let β := x.val b / (1 - t)
    have hα : 0 ≤ α := div_nonneg (x.property.1.1 a) hden.le
    have hβ : 0 ≤ β := div_nonneg (x.property.1.1 b) hden.le
    have hαβ : α + β = 1 := by
      dsimp [α, β]
      rw [← add_div]
      apply (div_eq_one_iff_eq hden.ne').mpr
      dsimp [t]
      linarith
    let yvec := α • Pi.single a 1 + β • Pi.single b 1
    have hyseg : yvec ∈ segment ℝ (Pi.single a 1) (Pi.single b 1) :=
      ⟨α, β, hα, hβ, hαβ, rfl⟩
    have hconv : Convex ℝ {f : Fin N → ℝ | (∀ w, 0 ≤ f w) ∧ ∑ w, f w = 1} := by
      intro f hf g hg a b ha hb hab
      refine ⟨fun w ↦ add_nonneg (mul_nonneg ha (hf.1 w)) (mul_nonneg hb (hg.1 w)), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]
    let y : ↥(carrier K) := ⟨yvec, hconv.segment_subset
      (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩)
      (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩) hyseg,
      {a, b}, hface, by intro w hw; simp [yvec, not_or.mp (by simpa using hw)]⟩
    have hy : y ∈ cycleCarrier l := ⟨a, b, hedge, hyseg⟩
    refine ⟨(⟨y, hy⟩, ⟨t, ht⟩), ?_⟩
    apply Subtype.ext
    funext w
    change vertexCycleRadial_g9 v yvec t w = x.val w
    by_cases hwv : w = v
    · subst w
      simp [vertexCycleRadial_g9, yvec, hva, hvb, t]
    by_cases hwa : w = a
    · subst w
      simp [vertexCycleRadial_g9, yvec, hab, Ne.symm hva, α,
        mul_div_cancel₀ _ hden.ne']
    by_cases hwb : w = b
    · subst w
      simp [vertexCycleRadial_g9, yvec, Ne.symm hab, Ne.symm hvb, β,
        mul_div_cancel₀ _ hden.ne']
    · simp [vertexCycleRadial_g9, yvec, hwv, hwa, hwb, hzero w hwv hwa hwb]

/-- The radial fan contains the open star of a vertex with the specified link.
A positive vertex coordinate forces that vertex into every supporting simplex.
Purity extends the support to a triangle. Removing the vertex leaves a link
edge, hence one of the cyclic fan triangles, whose radial coverage was proved
above. Source: Gallier--Xu §3.1, Definition 3.3 and stars, pp.32--34.
-/
theorem vertexCycleRadial_covers_positive_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) (v : Fin N)
    (hv : v ∉ l) (hpure : PureTwo K)
    (hlink : ∀ a b, linkEdge K v a b ↔ cycleEdge l a b)
    (hfan : ∀ i : Fin l.length,
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces)
    (x : ↥(carrier K)) (hxv : 0 < x.val v) :
    ∃ p : ↥(cycleCarrier (K := K) l) × Icc (0 : ℝ) 1,
      vertexCycleRadialMap_g9 K l v hfan p = x := by
  obtain ⟨s, hs, hsupport⟩ := x.property.2
  have hsv : v ∈ s := by
    by_contra hv
    exact (ne_of_gt hxv) (hsupport v hv)
  obtain ⟨t, ht, hcard, hst⟩ := hpure s hs
  have htv : v ∈ t := hst hsv
  have hecard : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem htv, hcard]
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hecard
  have hta : a ∈ t.erase v := by rw [he]; simp
  have htb : b ∈ t.erase v := by rw [he]; simp
  have hteq : t = {v, a, b} := by
    rw [← he, Finset.insert_erase htv]
  have htri : ({v, a, b} : Finset (Fin N)) ∈ K.faces := hteq ▸ ht
  have hledge : linkEdge K v a b :=
    ⟨hab, (Finset.mem_erase.mp hta).1, (Finset.mem_erase.mp htb).1, htri⟩
  obtain ⟨i, hi | hi⟩ := (hlink a b).mp hledge
  all_goals
    have hne : l.get i ≠ l.get (finRotate l.length i) :=
      ((hlink _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩).1
    apply vertexCycleRadial_covers_triangle_g9 K l v hv hfan i hne x
    intro w hw
    apply hsupport
    intro hws
    have hwt := hst hws
    rw [hteq] at hwt
    apply hw
    first | simpa only [hi.1, hi.2] using hwt
          | simpa only [hi.1, hi.2, Finset.pair_comm b a] using hwt

/-- A circular vertex link gives an open-disk chart on its positive-coordinate
star. The disk norm is one minus the vertex coordinate, so restricting the fan
homeomorphism to positive coordinate gives the open unit disk.
Source: Gallier--Xu §3.1 vertex stars, pp.32--34; explicit barycentric proof.
-/
theorem vertexCycle_open_star_disk_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) (v : Fin N)
    (hv : v ∉ l) (hpure : PureTwo K)
    (hlink : ∀ a b, linkEdge K v a b ↔ cycleEdge l a b)
    (hfan : ∀ i : Fin l.length,
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces)
    (e : Circle ≃ₜ ↥(cycleCarrier (K := K) l)) :
    Nonempty (↥{x : ↥(carrier K) | 0 < x.val v} ≃ₜ Metric.ball (0 : ℂ) 1) := by
  obtain ⟨H, hH⟩ := vertexCycle_disk_homeomorph_g9 K l v hv hfan e
  let U : Set ↥(carrier K) := {x | 0 < x.val v}
  let V : Set ↥(range (vertexCycleRadialMap_g9 K l v hfan)) := {x | 0 < x.val.val v}
  let W : Set (Metric.closedBall (0 : ℂ) 1) := {z | ‖(z : ℂ)‖ < 1}
  have he : ∀ x, x ∈ V ↔ H x ∈ W := by
    intro x
    obtain ⟨p, hp⟩ := x.property
    have hxeq : x = ⟨vertexCycleRadialMap_g9 K l v hfan p, ⟨p, rfl⟩⟩ := Subtype.ext hp.symm
    have hcoord : x.val.val v = (p.2 : ℝ) := by
      rw [hxeq]
      change vertexCycleRadial_g9 v p.1.val.val p.2.val v = _
      simp [vertexCycleRadial_g9, cycleCarrier_coordinate_zero_g9 K l v hv p.1]
    change 0 < x.val.val v ↔ ‖(H x : ℂ)‖ < 1
    rw [hxeq, hH, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr p.2.property.2)]
    change 0 < vertexCycleRadial_g9 v p.1.val.val p.2.val v ↔ _
    simp only [vertexCycleRadial_g9, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      cycleCarrier_coordinate_zero_g9 K l v hv p.1, Pi.single_eq_same, mul_zero, mul_one, zero_add]
    constructor <;> intro hp <;> linarith
  let a : U ≃ₜ V := {
    toFun x := ⟨⟨x.val, vertexCycleRadial_covers_positive_g9 K l v hv hpure hlink hfan
      x.val x.property⟩, x.property⟩
    invFun x := ⟨x.val.val, x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _)
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let b : W ≃ₜ Metric.ball (0 : ℂ) 1 := {
    toFun z := ⟨z.val.val, by simpa only [W, Set.mem_ofPred_eq, Metric.mem_ball,
      dist_zero_right] using z.property⟩
    invFun z := ⟨⟨z.val, Metric.ball_subset_closedBall z.property⟩, by
      simpa only [W, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] using z.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val }
  exact ⟨a.trans ((H.subtype he).trans b)⟩

/-- In a planar embedding, a vertex with circular link maps to an interior
point. Parametrize its positive-coordinate star by an open disk, convert complex
coordinates to the real Euclidean plane, and apply planar invariance of domain.
The vertex belongs to that star and its image is contained in the surface image.
Source: Gallier--Xu §3.1, pp.32--34; Hatcher Theorem 2B.3, p.172.
-/
theorem vertexCycle_image_interior_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N)) (v : Fin N)
    (hv : v ∉ l) (hpure : PureTwo K)
    (hlink : ∀ a b, linkEdge K v a b ↔ cycleEdge l a b)
    (hfan : ∀ i : Fin l.length,
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces)
    (e : Circle ≃ₜ ↥(cycleCarrier (K := K) l))
    (f : C(↥(carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f)
    (x : ↥(carrier K)) (hxv : 0 < x.val v) :
    f x ∈ interior (range f) := by
  obtain ⟨H⟩ := vertexCycle_open_star_disk_g9 K l v hv hpure hlink hfan e
  let eplane := Complex.orthonormalBasisOneI.repr.symm.toHomeomorph
  let U : Set (EuclideanSpace ℝ (Fin 2)) := eplane ⁻¹' Metric.ball (0 : ℂ) 1
  have hU : IsOpen U := Metric.isOpen_ball.preimage eplane.continuous
  let b : U ≃ₜ Metric.ball (0 : ℂ) 1 := eplane.subtype (fun _ ↦ Iff.rfl)
  let g : U → EuclideanSpace ℝ (Fin 2) := fun z ↦ f (H.symm (b z)).val
  have hg : Continuous g := f.continuous.comp
    (continuous_subtype_val.comp (H.symm.continuous.comp b.continuous))
  have hginj : Function.Injective g := hf.comp (Subtype.val_injective.comp
    (H.symm.injective.comp b.injective))
  have hopen : IsOpen (range g) := HolomorphicAnosov.hatcher_planar_embedding_open_image U hU g hg hginj
  have hsub : range g ⊆ range f := by rintro _ ⟨z, rfl⟩; exact ⟨_, rfl⟩
  apply interior_mono hsub
  rw [hopen.interior_eq]
  refine ⟨b.symm (H ⟨x, hxv⟩), ?_⟩
  simp only [g, b.apply_symm_apply, H.symm_apply_apply]

/-- The circular alternative in `SurfaceLinks` supplies a disk chart, with no
extra geometric hypothesis on the link. The vertex list contains every adjacent
vertex and omits the apex; its cycle edges are exactly the incident triangles.
Source: Gallier--Xu §3.1 vertex stars, pp.32--34 and §4.1 surface links.
-/
theorem circularLink_open_star_disk_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N) (hpure : PureTwo K)
    (l : List (Fin N)) (hnd : l.Nodup) (hlen : 3 ≤ l.length)
    (hvertices : ∀ a, a ∈ l ↔ a ≠ v ∧ ({v, a} : Finset (Fin N)) ∈ K.faces)
    (hlink : ∀ a b, linkEdge K v a b ↔ cycleEdge l a b) :
    Nonempty (↥{x : ↥(carrier K) | 0 < x.val v} ≃ₜ Metric.ball (0 : ℂ) 1) := by
  have hv : v ∉ l := fun h ↦ ((hvertices v).mp h).1 rfl
  have hfan (i : Fin l.length) :
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces :=
    ((hlink _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩).2.2.2
  have hcycle (i : Fin l.length) :
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces :=
    (K.isRelLowerSet_faces (hfan i)).2 (Finset.subset_insert _ _) (by simp)
  obtain ⟨e⟩ := boundaryCycle_circle_homeomorph_g9 K l hnd hlen hcycle
  exact vertexCycle_open_star_disk_g9 K l v hv hpure hlink hfan e

/-- Circular-link vertices lie in the interior of any planar embedded surface.
Source: Gallier--Xu's vertex stars and Hatcher Theorem 2B.3, p.172.
-/
theorem circularLink_image_interior_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N) (hpure : PureTwo K)
    (l : List (Fin N)) (hnd : l.Nodup) (hlen : 3 ≤ l.length)
    (hvertices : ∀ a, a ∈ l ↔ a ≠ v ∧ ({v, a} : Finset (Fin N)) ∈ K.faces)
    (hlink : ∀ a b, linkEdge K v a b ↔ cycleEdge l a b)
    (f : C(↥(carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f)
    (x : ↥(carrier K)) (hxv : 0 < x.val v) :
    f x ∈ interior (range f) := by
  have hv : v ∉ l := fun h ↦ ((hvertices v).mp h).1 rfl
  have hfan (i : Fin l.length) :
      ({v, l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces :=
    ((hlink _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩).2.2.2
  have hcycle (i : Fin l.length) :
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces :=
    (K.isRelLowerSet_faces (hfan i)).2 (Finset.subset_insert _ _) (by simp)
  obtain ⟨e⟩ := boundaryCycle_circle_homeomorph_g9 K l hnd hlen hcycle
  exact vertexCycle_image_interior_g9 K l v hv hpure hlink hfan e f hf x hxv


/-- A triangle containing two distinct vertices has a unique remaining vertex. -/
lemma triangle_third_vertex_g9 {N : ℕ} {t : Finset (Fin N)}
    (ht : t.card = 3) {v a : Fin N} (hva : v ≠ a)
    (hv : v ∈ t) (ha : a ∈ t) :
    ∃ b, b ≠ v ∧ b ≠ a ∧ t = {v, a, b} := by
  have hac : a ∈ t.erase v := Finset.mem_erase.mpr ⟨Ne.symm hva, ha⟩
  have hc : ((t.erase v).erase a).card = 1 := by
    rw [Finset.card_erase_of_mem hac, Finset.card_erase_of_mem hv, ht]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hc
  have hbm : b ∈ (t.erase v).erase a := by rw [hb]; simp
  refine ⟨b, (Finset.mem_erase.mp (Finset.mem_erase.mp hbm).2).1,
    (Finset.mem_erase.mp hbm).1, ?_⟩
  rw [← hb, Finset.insert_erase hac, Finset.insert_erase hv]

/-- The first vertex of a simple interval has only its next vertex as a neighbor. -/
lemma pathEdge_first_iff_g9 {N : ℕ} (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 2 ≤ l.length) (b : Fin N) :
    pathEdge l (l.get ⟨0, by omega⟩) b ↔ b = l.get ⟨1, by omega⟩ := by
  constructor
  · rintro ⟨i, hi, h | h⟩
    · have he := (List.nodup_iff_injective_get.mp hnd) h.1
      have hi0 : i = 0 := congrArg Fin.val he
      subst i
      exact h.2.symm
    · have he := (List.nodup_iff_injective_get.mp hnd) h.2
      have hf : i + 1 = 0 := congrArg Fin.val he
      omega
  · intro hb
    subst b
    exact ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩

/-- A surface edge whose link has a unique adjacent vertex lies in one
triangle and is therefore a boundary edge. -/
lemma uniqueLinkNeighbor_boundaryEdge_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v a b : Fin N)
    (htri : linkEdge K v a b)
    (hunique : ∀ c, linkEdge K v a c → c = b) : boundaryEdge K v a := by
  classical
  have hva : v ≠ a := Ne.symm htri.2.1
  have hvb : v ≠ b := Ne.symm htri.2.2.1
  have hab : a ≠ b := htri.1
  refine ⟨hva, (linkEdge_edge_faces K v a b htri).1, ?_⟩
  have heq : (simplices K 2).filter (fun t ↦ ({v, a} : Finset (Fin N)) ⊆ t) =
      {({v, a, b} : Finset (Fin N))} := by
    ext t
    simp only [Finset.mem_filter, simplices, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ht, hc⟩, hsub⟩
      obtain ⟨c, hcv, hca, htc⟩ := triangle_third_vertex_g9 hc hva
        (hsub (by simp)) (hsub (by simp))
      have hcLink : linkEdge K v a c := ⟨Ne.symm hca, Ne.symm hva, hcv, htc ▸ ht⟩
      have hcb : c = b := hunique c hcLink
      simpa [hcb] using htc
    · rintro rfl
      exact ⟨⟨htri.2.2.2, by simp [hva, hvb, hab]⟩, by simp⟩
  change ((simplices K 2).filter fun t ↦ ({v, a} : Finset (Fin N)) ⊆ t).card = 1
  rw [heq, Finset.card_singleton]

/-- The first edge of an interval vertex fan is a boundary edge: it lies in
exactly its first triangle. Source: Gallier--Xu §3.1 vertex-link description.
The proof enumerates incident triangles by their third vertices and uses the
unique neighbor of the first endpoint in the interval link.
-/
theorem intervalLink_first_boundaryEdge_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N) (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 2 ≤ l.length)
    (hlink : ∀ a b, linkEdge K v a b ↔ pathEdge l a b) :
    boundaryEdge K v (l.get ⟨0, by omega⟩) := by
  apply uniqueLinkNeighbor_boundaryEdge_g9 K v _ (l.get ⟨1, by omega⟩)
  · exact (hlink _ _).mpr ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩
  · intro c hc
    exact (pathEdge_first_iff_g9 l hnd hlen c).mp ((hlink _ _).mp hc)

/-- The last vertex of a simple interval has only its preceding neighbor. -/
lemma pathEdge_last_iff_g9 {N : ℕ} (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 2 ≤ l.length) (b : Fin N) :
    pathEdge l (l.get ⟨l.length-1, by omega⟩) b ↔
      b = l.get ⟨l.length-2, by omega⟩ := by
  constructor
  · rintro ⟨i, hi, h | h⟩
    · have he : i = l.length-1 := congrArg Fin.val (hnd.injective_get h.1)
      omega
    · have he : i+1 = l.length-1 := congrArg Fin.val (hnd.injective_get h.2)
      have hei : i = l.length-2 := by omega
      subst i
      exact h.1.symm
  · intro hb
    subst b
    refine ⟨l.length-2, by omega, Or.inr ⟨rfl, ?_⟩⟩
    apply congrArg l.get
    apply Fin.ext
    dsimp
    omega

/-- The last edge of an interval vertex fan is also a boundary edge.
The unique-neighbor incidence calculation is identical at the other endpoint.
Source: Gallier--Xu §3.1 vertex stars and boundary links.
-/
theorem intervalLink_last_boundaryEdge_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N) (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 2 ≤ l.length)
    (hlink : ∀ a b, linkEdge K v a b ↔ pathEdge l a b) :
    boundaryEdge K v (l.get ⟨l.length-1, by omega⟩) := by
  apply uniqueLinkNeighbor_boundaryEdge_g9 K v _ (l.get ⟨l.length-2, by omega⟩)
  · apply (hlink _ _).mpr
    exact (pathEdge_last_iff_g9 l hnd hlen _).mpr rfl
  · intro c hc
    exact (pathEdge_last_iff_g9 l hnd hlen c).mp ((hlink _ _).mp hc)

/-- Away from the listed boundary vertices the link alternative must be a
circle. An interval link would give a one-triangle edge through the vertex;
`BoundaryCycles` puts both endpoints of this edge on one listed cycle.
Source: Gallier--Xu §3.1 vertex stars and boundary links.
-/
theorem nonboundaryVertex_circularLink_g9 {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hlinks : SurfaceLinks K) (hboundary : BoundaryCycles K B)
    (v : Fin N) (hv : ∀ j, v ∉ B j) :
    ∃ l : List (Fin N), l.Nodup ∧ 3 ≤ l.length ∧
      (∀ a, a ∈ l ↔ a ≠ v ∧ ({v, a} : Finset (Fin N)) ∈ K.faces) ∧
      ∀ a b, linkEdge K v a b ↔ cycleEdge l a b := by
  obtain ⟨l, hnd, hvertices, hcircle | hpath⟩ := hlinks v
  · exact ⟨l, hnd, hcircle.1, hvertices, hcircle.2⟩
  · have he := intervalLink_first_boundaryEdge_g9 K v l hnd hpath.1 hpath.2
    obtain ⟨j, i, hi | hi⟩ := (hboundary.2.2 _ _).mp he
    · exact (hv j (hi.1 ▸ List.get_mem _ _)).elim
    · exact (hv j (hi.2 ▸ List.get_mem _ _)).elim


/-- An interval link has an injective traversal with its original endpoint
vertices and precisely the original edge-chain image. Source: Gallier--Xu
§3.1 barycentric realization of a finite simplicial interval.
-/
theorem coordinate_path_interval_g9 {N : ℕ} (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 2 ≤ l.length) :
    ∃ p : Path (Pi.single (l.get ⟨0, by omega⟩) (1 : ℝ))
      (Pi.single (l.get ⟨l.length - 1, by omega⟩) 1),
      Function.Injective p ∧
      range p = {x | ∃ a b, pathEdge l a b ∧ x ∈ segment ℝ (Pi.single a 1) (Pi.single b 1)} := by
  have generic (m : ℕ) (v : Fin m → Fin N) (hm : 2 ≤ m)
      (hv : Function.Injective v) :
      ∃ p : Path (Pi.single (v ⟨0, by omega⟩) (1 : ℝ))
        (Pi.single (v ⟨m-1, by omega⟩) 1),
        Function.Injective p ∧
        range p = ⋃ (i : ℕ) (hi : i+1 < m),
          segment ℝ (Pi.single (v ⟨i, by omega⟩) 1) (Pi.single (v ⟨i+1, hi⟩) 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n+2 := ⟨m-2, by omega⟩
    obtain ⟨p, hp, hr⟩ := coordinate_edge_chain_g9 v hv
    refine ⟨p, hp, hr.trans ?_⟩
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.val, by omega, hi⟩
    · rintro ⟨i, hi, hx⟩
      exact ⟨⟨i, by omega⟩, hx⟩
  obtain ⟨p, hp, hr⟩ := generic l.length l.get hlen hnd.injective_get
  refine ⟨p, hp, hr.trans ?_⟩
  ext x
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨_, _, ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩, hx⟩
  · rintro ⟨a, b, ⟨i, hi, h | h⟩, hx⟩
    · exact ⟨i, hi, by simpa only [h.1, h.2] using hx⟩
    · exact ⟨i, hi, by simpa only [h.1, h.2, segment_symm] using hx⟩

/-- The affine cone over a link-edge point lies in the corresponding triangle.
Source: Gallier--Xu §3.1, barycentric realization.
-/
theorem intervalFan_mem_carrier_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v a b : Fin N)
    (htri : ({v,a,b} : Finset (Fin N)) ∈ K.faces)
    (x : Fin N → ℝ) (hx : x ∈ segment ℝ (Pi.single a 1) (Pi.single b 1))
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    (1-t) • x + t • Pi.single v 1 ∈ carrier K := by
  have hconv : Convex ℝ {f : Fin N → ℝ | (∀ w, 0 ≤ f w) ∧ ∑ w, f w = 1} := by
    intro f hf g hg a b ha hb hab
    refine ⟨fun w ↦ add_nonneg (mul_nonneg ha (hf.1 w)) (mul_nonneg hb (hg.1 w)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]
  refine ⟨hconv (hconv.segment_subset
    (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩)
      (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩) hx)
    (by exact ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩)
    (sub_nonneg.mpr ht.2) ht.1 (by ring),
    {v,a,b}, htri, ?_⟩
  intro w hw
  have hn : w ≠ v ∧ w ≠ a ∧ w ≠ b := by simpa [not_or] using hw
  obtain ⟨α, β, _, _, _, he⟩ := hx
  have hxw : x w = 0 := by
    have hh := congrFun he w
    simpa [hn.2.1, hn.2.2] using hh.symm
  simp [hxw, hn.1]

/-- Any point of a link edge has zero apex coordinate. -/
lemma linkEdge_segment_apex_zero_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v a b : Fin N)
    (hab : linkEdge K v a b) {x : Fin N → ℝ}
    (hx : x ∈ segment ℝ (Pi.single a 1) (Pi.single b 1)) : x v = 0 := by
  obtain ⟨α, β, _, _, _, he⟩ := hx
  have hh := congrFun he v
  simpa [Ne.symm hab.2.1, Ne.symm hab.2.2.1] using hh.symm

/-- The interior of an injective radial strip maps into the interior of any
planar embedding of the surface. The apex coordinate recovers radial height,
and injectivity of the link arc recovers the other coordinate. Thus the
open parameter square embeds continuously in the plane and has open image
by Hatcher Theorem 2B.3, p.172.
-/
theorem radialStrip_image_interior_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N)
    (p : C(unitInterval, Fin N → ℝ)) (hp : Function.Injective p)
    (hpv : ∀ s, p s v = 0)
    (hm : ∀ (s t : unitInterval), (1-(t : ℝ)) • p s + (t : ℝ) • Pi.single v 1 ∈ carrier K)
    (f : C(↥(carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f)
    (s t : unitInterval) (hs : (s : ℝ) ∈ Ioo 0 1) (ht : (t : ℝ) ∈ Ioo 0 1) :
    f ⟨(1-(t : ℝ)) • p s + (t : ℝ) • Pi.single v 1, hm s t⟩ ∈
      interior (range f) := by
  let U : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ∈ Ioo 0 1 ∧ z 1 ∈ Ioo 0 1}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_Ioo.preimage (by fun_prop)
    · exact isOpen_Ioo.preimage (by fun_prop)
  let a : U → unitInterval := fun z ↦ ⟨z.val 0, le_of_lt z.property.1.1, le_of_lt z.property.1.2⟩
  let b : U → unitInterval := fun z ↦ ⟨z.val 1, le_of_lt z.property.2.1, le_of_lt z.property.2.2⟩
  have ha : Continuous a := by fun_prop
  have hb : Continuous b := by fun_prop
  let g : U → ↥(carrier K) := fun z ↦
    ⟨(1-(b z : ℝ)) • p (a z) + (b z : ℝ) • Pi.single v 1, hm (a z) (b z)⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp hb)).smul
      (p.continuous.comp ha)).add ((continuous_subtype_val.comp hb).smul continuous_const)
  have hginj : Function.Injective g := by
    intro x y h
    have he := congrArg Subtype.val h
    have hv := congrFun he v
    have ht' : (b x : ℝ) = (b y : ℝ) := by simpa [g, hpv] using hv
    have hbase : p (a x) = p (a y) := by
      apply smul_right_injective (Fin N → ℝ) (sub_ne_zero.mpr (ne_of_gt x.property.2.2))
      change (1-(b x : ℝ)) • p (a x) = (1-(b x : ℝ)) • p (a y)
      dsimp [g] at he
      rw [← ht'] at he
      exact add_right_cancel he
    have hs' : (a x : ℝ) = (a y : ℝ) := congrArg Subtype.val (hp hbase)
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hs'
    · exact ht'
  have hopen : IsOpen (range (fun z ↦ f (g z))) :=
    HolomorphicAnosov.hatcher_planar_embedding_open_image U hU _
      (f.continuous.comp hg) (hf.comp hginj)
  apply interior_mono (show range (fun z ↦ f (g z)) ⊆ range f by
    rintro _ ⟨z, rfl⟩; exact ⟨g z, rfl⟩)
  rw [hopen.interior_eq]
  refine ⟨⟨WithLp.toLp 2 ![(s : ℝ), (t : ℝ)], hs, ht⟩, ?_⟩
  rfl

/-- A non-apex point in a simplex fan has a normalized point on its opposite
edge. Divide the other two barycentric coordinates by one minus the apex
coordinate; they are nonnegative and sum to one. Source: Gallier--Xu §3.1,
Definition 3.3, p.32.
-/
theorem triangle_radial_coordinates_g9 {N : ℕ}
    (v a b : Fin N) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (x : Fin N → ℝ) (hx : x ∈ { f : Fin N → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 }) (hv : x v < 1)
    (hsupport : ∀ w ∉ ({v,a,b} : Finset (Fin N)), x w = 0) :
    ∃ y ∈ segment ℝ (Pi.single a 1) (Pi.single b 1),
      (1-x v) • y + x v • Pi.single v 1 = x := by
  classical
  have hsum : x v + x a + x b = 1 := by
    have hh : ∑ w ∈ ({v,a,b} : Finset (Fin N)), x w = ∑ w, x w := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      exact hsupport w hw
    simpa [hva, hvb, hab, add_assoc, hx.2] using hh
  have hden : 0 < 1-x v := sub_pos.mpr hv
  let α := x a / (1-x v)
  let β := x b / (1-x v)
  have hα : 0 ≤ α := div_nonneg (hx.1 a) hden.le
  have hβ : 0 ≤ β := div_nonneg (hx.1 b) hden.le
  have hαβ : α+β = 1 := by
    dsimp [α,β]
    rw [← add_div]
    apply (div_eq_one_iff_eq hden.ne').mpr
    linarith
  refine ⟨α • Pi.single a 1 + β • Pi.single b 1,
    ⟨α, β, hα, hβ, hαβ, rfl⟩, ?_⟩
  funext w
  by_cases hwv : w = v
  · subst w
    simp [hva,hvb]
  by_cases hwa : w = a
  · subst w
    simp [hab, Ne.symm hva, α, mul_div_cancel₀ _ hden.ne']
  by_cases hwb : w = b
  · subst w
    simp [Ne.symm hab, Ne.symm hvb, β, mul_div_cancel₀ _ hden.ne']
  · have hw0 := hsupport w (by simp [hwv,hwa,hwb])
    simp [hwv,hwa,hwb,hw0]

/-- Positive apex mass puts a point in one of its incident triangles. If
the mass is below one, radial normalization lands on an actual link edge.
Purity first extends the supporting face to a triangle and its other two
vertices give the link edge. Source: Gallier--Xu §3.1 vertex-star description.
-/
theorem vertex_positive_radial_coordinates_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N) (hpure : PureTwo K)
    (x : ↥(carrier K)) (hxv : 0 < x.val v) (hxv1 : x.val v < 1) :
    ∃ a b, linkEdge K v a b ∧ ∃ y ∈ segment ℝ (Pi.single a 1) (Pi.single b 1),
      (1-x.val v) • y + x.val v • Pi.single v 1 = x.val := by
  obtain ⟨s, hs, hsupport⟩ := x.property.2
  have hsv : v ∈ s := by
    by_contra hv
    exact (ne_of_gt hxv) (hsupport v hv)
  obtain ⟨t, ht, hc, hst⟩ := hpure s hs
  have htv := hst hsv
  have hecard : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem htv, hc]
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp hecard
  have hta : a ∈ t.erase v := by rw [he]; simp
  have htb : b ∈ t.erase v := by rw [he]; simp
  have hteq : t = {v,a,b} := by rw [← he, Finset.insert_erase htv]
  have hav := (Finset.mem_erase.mp hta).1
  have hbv := (Finset.mem_erase.mp htb).1
  refine ⟨a,b,⟨hab,hav,hbv,hteq ▸ ht⟩,?_⟩
  apply triangle_radial_coordinates_g9 v a b (Ne.symm hav) (Ne.symm hbv) hab
    x.val x.property.1 hxv1
  intro w hw
  apply hsupport
  intro hws
  exact hw (hteq ▸ hst hws)

/-- In an interval fan, every positive-apex point off the apex and the two
endpoint rays maps into the planar interior. Normalize to the link arc,
exclude its endpoints using the ray hypotheses, then use the open radial
strip chart. Source: Gallier--Xu §3.1 and Hatcher Theorem 2B.3.
-/
theorem intervalLink_image_interior_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N) (hpure : PureTwo K)
    (l : List (Fin N)) (hnd : l.Nodup) (hlen : 2 ≤ l.length)
    (hlink : ∀ a b, linkEdge K v a b ↔ pathEdge l a b)
    (f : C(↥(carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f)
    (x : ↥(carrier K)) (hxv : 0 < x.val v) (hxv1 : x.val v < 1)
    (hfirst : x.val ∉ segment ℝ (Pi.single (l.get ⟨0, by omega⟩) 1) (Pi.single v 1))
    (hlast : x.val ∉ segment ℝ (Pi.single (l.get ⟨l.length-1, by omega⟩) 1) (Pi.single v 1)) :
    f x ∈ interior (range f) := by
  obtain ⟨p, hp, hr⟩ := coordinate_path_interval_g9 l hnd hlen
  have hm (s t : unitInterval) :
      (1-(t : ℝ)) • p s + (t : ℝ) • Pi.single v 1 ∈ carrier K := by
    have hps : p s ∈ range p := ⟨s,rfl⟩
    rw [hr] at hps
    obtain ⟨a,b,hab,hseg⟩ := hps
    exact intervalFan_mem_carrier_g9 K v a b ((hlink a b).mpr hab).2.2.2
      (p s) hseg t.property
  have hpv (s : unitInterval) : p s v = 0 := by
    have hps : p s ∈ range p := ⟨s,rfl⟩
    rw [hr] at hps
    obtain ⟨a,b,hab,hseg⟩ := hps
    exact linkEdge_segment_apex_zero_g9 K v a b ((hlink a b).mpr hab) hseg
  obtain ⟨a,b,hab,y,hy,hyeq⟩ := vertex_positive_radial_coordinates_g9 K v hpure x hxv hxv1
  have hyimage : y ∈ range p := by rw [hr]; exact ⟨a,b,(hlink a b).mp hab,hy⟩
  obtain ⟨s,rfl⟩ := hyimage
  let t : unitInterval := ⟨x.val v, hxv.le, hxv1.le⟩
  have ht : (t : ℝ) ∈ Ioo 0 1 := ⟨hxv,hxv1⟩
  have hs : (s : ℝ) ∈ Ioo 0 1 := by
    constructor
    · by_contra hs
      have he : s = 0 := Subtype.ext (le_antisymm (not_lt.mp hs) s.property.1)
      apply hfirst
      rw [← hyeq,he,Path.source]
      exact ⟨1-x.val v,x.val v,sub_nonneg.mpr hxv1.le,hxv.le,by ring,rfl⟩
    · by_contra hs
      have he : s = 1 := Subtype.ext (le_antisymm s.property.2 (not_lt.mp hs))
      apply hlast
      rw [← hyeq,he,Path.target]
      exact ⟨1-x.val v,x.val v,sub_nonneg.mpr hxv1.le,hxv.le,by ring,rfl⟩
  have hres := radialStrip_image_interior_g9 K v p.toContinuousMap hp hpv hm f hf s t hs ht
  have hxeq : (⟨(1-(t : ℝ)) • p s + (t : ℝ) • Pi.single v 1,hm s t⟩ : ↥(carrier K)) = x :=
    Subtype.ext hyeq
  change f ⟨(1-(t : ℝ)) • p s + (t : ℝ) • Pi.single v 1,hm s t⟩ ∈ interior (range f) at hres
  rwa [hxeq] at hres

/-- Unit mass at one vertex forces all other barycentric coordinates to vanish. -/
lemma simplex_eq_single_of_coordinate_one_g9 {N : ℕ} (x : Fin N → ℝ)
    (hx : x ∈ { f : Fin N → ℝ | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1 }) (v : Fin N) (hv : x v = 1) :
    x = Pi.single v 1 := by
  classical
  have hsum : ∑ w ∈ Finset.univ.erase v, x w = 0 := by
    have hh := Finset.sum_erase_add Finset.univ x (Finset.mem_univ v)
    rw [hx.2,hv] at hh
    linarith
  funext w
  by_cases hw : w = v
  · subst w; simpa using hv
  · have hz : x w = 0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ hx.1 i)).mp hsum w (Finset.mem_erase.mpr ⟨hw,Finset.mem_univ _⟩)
    simpa [hw] using hz

/-- Every point on a boundary edge belongs to a listed boundary cycle. -/
lemma boundaryEdge_point_cycleCarrier_g9 {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hB : BoundaryCycles K B) {v a : Fin N} (he : boundaryEdge K v a)
    (x : ↥(carrier K))
    (hx : x.val ∈ segment ℝ (Pi.single v 1) (Pi.single a 1)) :
    ∃ j, x ∈ cycleCarrier (B j) := by
  obtain ⟨j,hj⟩ := (hB.2.2 v a).mp he
  exact ⟨j,v,a,hj,hx⟩

/-- A planar embedding of a finite surface has no extra frontier away from
its listed boundary cycles. Pick a positive barycentric coordinate. A circular
link gives an open disk chart. An interval link gives a radial strip chart;
its two endpoint rays and its apex belong to boundary edges, hence are
excluded. Invariance of domain makes either chart image open in the plane.
Source: Gallier--Xu §3.1 vertex stars and Hatcher Theorem 2B.3, p.172.
-/
theorem surface_image_interior_of_not_boundary_g9 {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hpure : PureTwo K) (hlinks : SurfaceLinks K) (hB : BoundaryCycles K B)
    (f : C(↥(carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f)
    (x : ↥(carrier K)) (hx : ∀ j, x ∉ cycleCarrier (B j)) :
    f x ∈ interior (range f) := by
  have hv : ∃ v, 0 < x.val v := by
    by_contra! h
    have hz : ∀ v, x.val v = 0 := fun v ↦ le_antisymm (h v) (x.property.1.1 v)
    have hh := x.property.1.2
    simp [hz] at hh
  obtain ⟨v,hv⟩ := hv
  obtain ⟨l,hnd,hvertices,hcircle | hpath⟩ := hlinks v
  · exact circularLink_image_interior_g9 K v hpure l hnd hcircle.1 hvertices
      hcircle.2 f hf x hv
  · have hfirst := intervalLink_first_boundaryEdge_g9 K v l hnd hpath.1 hpath.2
    have hlast := intervalLink_last_boundaryEdge_g9 K v l hnd hpath.1 hpath.2
    have hnotfirst : x.val ∉ segment ℝ
        (Pi.single (l.get ⟨0, by omega⟩) 1) (Pi.single v 1) := by
      intro hseg
      obtain ⟨j,hj⟩ := boundaryEdge_point_cycleCarrier_g9 K B hB hfirst x
        (by simpa only [segment_symm] using hseg)
      exact hx j hj
    have hnotlast : x.val ∉ segment ℝ
        (Pi.single (l.get ⟨l.length-1, by omega⟩) 1) (Pi.single v 1) := by
      intro hseg
      obtain ⟨j,hj⟩ := boundaryEdge_point_cycleCarrier_g9 K B hB hlast x
        (by simpa only [segment_symm] using hseg)
      exact hx j hj
    have hv1 : x.val v < 1 := by
      have hle := x.property.1.2 ▸ Finset.single_le_sum (fun w _ ↦ x.property.1.1 w)
        (Finset.mem_univ v)
      apply lt_of_le_of_ne hle
      intro hone
      apply hnotfirst
      rw [simplex_eq_single_of_coordinate_one_g9 x.val x.property.1 v hone]
      exact right_mem_segment ℝ _ _
    exact intervalLink_image_interior_g9 K v hpure l hnd hpath.1 hpath.2
      f hf x hv hv1 hnotfirst hnotlast

/-- The frontier of a compact embedded triangulated surface is contained in
the union of the images of its prescribed boundary cycles. Compactness puts
every frontier point in the image, and the interior chart theorem excludes
all points outside the cycles. Source: Gallier--Xu §3.1 and Hatcher 2B.3.
-/
theorem surface_image_frontier_subset_boundary_g9 {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (B : Fin b → List (Fin N))
    (hpure : PureTwo K) (hlinks : SurfaceLinks K) (hB : BoundaryCycles K B)
    (f : C(↥(carrier K), EuclideanSpace ℝ (Fin 2))) (hf : Function.Injective f) :
    frontier (range f) ⊆ ⋃ j, f '' cycleCarrier (B j) := by
  let : CompactSpace ↥(carrier K) := isCompact_iff_compactSpace.mp (triangle_carrier_compact K)
  have hc : IsClosed (range f) := (isCompact_range f.continuous).isClosed
  intro y hy
  have hym : y ∈ range f := hc.closure_eq ▸ frontier_subset_closure hy
  obtain ⟨x,rfl⟩ := hym
  by_contra hnot
  have hx : ∀ j, x ∉ cycleCarrier (B j) := by
    intro j hxj
    exact hnot (mem_iUnion.mpr ⟨j,mem_image_of_mem f hxj⟩)
  exact hy.2 (surface_image_interior_of_not_boundary_g9 K B hpure hlinks hB f hf x hx)


end HolomorphicAnosov.Topology.GallierXu
