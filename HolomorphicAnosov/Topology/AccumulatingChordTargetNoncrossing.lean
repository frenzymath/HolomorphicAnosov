import HolomorphicAnosov.Analysis.UnitCircleChordBoundaryZeroDeterminant
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas

namespace HolomorphicAnosov
open Set
open scoped ComplexConjugate

/-- The target chord interiors in the accumulating-chord construction are
pairwise disjoint.

Source: Cairns (1951), §3(E)--§4(A), pp.863--864, circle-chord cyclic order
step in the countable-chord omission expansion. The map p ↦ h(σ(p)) is a
homeomorphism of Circle, so it sends the disjoint source parameter arcs to
disjoint open circle arcs with the corresponding endpoint pairs. Endpoints of
two disjoint open arcs cannot alternate in cyclic order. The two straight
chords of a circle intersect in their relative interiors only when their
four endpoints alternate; shared endpoints alone cannot create an interior
intersection, by strict convexity of the disk. Finally, equal unordered endpoint
pairs would give equal nonempty source open chords, contradicting source
pairwise disjointness. These observations prove the displayed pairwise
noncrossing statement, including arcs with a shared endpoint. -/
theorem accumulatingChord_target_noncrossing
    {ι : Type*} [Countable ι]
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (h : (Set.range σ) ≃ₜ Circle)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (hOpen : ∀ i, IsOpen (arcs i))
    (hConnected : ∀ i, IsConnected (arcs i))
    (_hProper : ∀ i, arcs i ≠ Set.univ)
    (hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (hDistinct : ∀ i, u i ≠ v i)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j))
    (_hAvoid : ∀ i, Disjoint (openSegment ℝ (σ (u i)) (σ (v i))) (Set.range σ))
    (hChordsDisjoint : Pairwise fun i j ↦
      Disjoint (openSegment ℝ (σ (u i)) (σ (v i)))
        (openSegment ℝ (σ (u j)) (σ (v j)))) :
    Pairwise (fun i j ↦
      Disjoint
        (openSegment ℝ (h ⟨σ (u i), ⟨u i, rfl⟩⟩ : ℂ)
          (h ⟨σ (v i), ⟨v i, rfl⟩⟩ : ℂ))
        (openSegment ℝ (h ⟨σ (u j), ⟨u j, rfl⟩⟩ : ℂ)
          (h ⟨σ (v j), ⟨v j, rfl⟩⟩ : ℂ))) := by
  classical
  let g : Circle → Circle := fun p ↦ h ⟨σ p, ⟨p, rfl⟩⟩
  have hg : Continuous g := h.continuous.comp
    (hσ.continuous.subtype_mk (fun p ↦ ⟨p, rfl⟩))
  have hgi : Function.Injective g := by
    intro p q hpq
    exact hσ.injective (congrArg Subtype.val (h.injective hpq))
  intro i j hij
  let L : ℂ → ℝ := fun z ↦ (conj ((g (v i) : ℂ) - g (u i)) *
    (z - g (u i))).im
  let f : Circle → ℝ := fun p ↦ L (g p)
  have hfc : Continuous f := by
    dsimp only [f, L]
    fun_prop
  have hui : L (g (u i)) = 0 := by simp [L]
  have hvi : L (g (v i)) = 0 := by
    dsimp only [L]
    rw [← Complex.normSq_eq_conj_mul_self]
    simp
  have htargetNe : (g (u i) : ℂ) ≠ g (v i) := by
    intro heq
    exact hDistinct i (hgi (Circle.coe_injective heq))
  have hzero (p : Circle) (hp : f p = 0) : p = u i ∨ p = v i := by
    rcases Analysis.unit_circle_chord_boundary_zero_determinant
      (g (u i)) (g (v i)) (g p) htargetNe (Circle.norm_coe _) (Circle.norm_coe _)
      (Circle.norm_coe _) hp with hu | hv
    · exact Or.inl (hgi (Circle.coe_injective hu))
    · exact Or.inr (hgi (Circle.coe_injective hv))
  have houtside : closure (arcs i) ⊆ (arcs j)ᶜ :=
    closure_minimal (fun p hp ↦ Set.disjoint_left.mp (hArcsDisjoint hij) hp)
      (hOpen j).isClosed_compl
  have hfront (k : ι) : u k ∈ closure (arcs k) ∧ v k ∈ closure (arcs k) := by
    constructor <;> apply frontier_subset_closure <;> rw [hEndpoints k] <;> simp
  have hnonzero (p : Circle) (hp : p ∈ arcs j) : f p ≠ 0 := by
    intro hz
    rcases hzero p hz with rfl | rfl
    · exact houtside (hfront i).1 hp
    · exact houtside (hfront i).2 hp
  have hside : (f (u j) ≤ 0 ∧ f (v j) ≤ 0) ∨
      (0 ≤ f (u j) ∧ 0 ≤ f (v j)) := by
    have hpre := (hConnected j).isPreconnected.image f hfc.continuousOn
    have hcover : f '' arcs j ⊆ Iio 0 ∪ Ioi 0 := by
      rintro _ ⟨p, hp, rfl⟩
      exact lt_or_gt_of_ne (hnonzero p hp)
    have hdisj : (f '' arcs j) ∩ (Iio 0 ∩ Ioi 0) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact (lt_asymm (show r < 0 from hr.2.1) (show 0 < r from hr.2.2))
    rcases isPreconnected_iff_subset_of_disjoint.mp hpre _ _
      isOpen_Iio isOpen_Ioi hcover hdisj with hneg | hpos
    · have hclosure : closure (arcs j) ⊆ {p | f p ≤ 0} :=
        closure_minimal (fun p hp ↦ (show f p < 0 from hneg (mem_image_of_mem f hp)).le)
          (isClosed_le hfc continuous_const)
      exact Or.inl ⟨hclosure (hfront j).1, hclosure (hfront j).2⟩
    · have hclosure : closure (arcs j) ⊆ {p | 0 ≤ f p} :=
        closure_minimal (fun p hp ↦ (show 0 < f p from hpos (mem_image_of_mem f hp)).le)
          (isClosed_le continuous_const hfc)
      exact Or.inr ⟨hclosure (hfront j).1, hclosure (hfront j).2⟩
  have hlin (a b : ℂ) (t : ℝ) :
      L (AffineMap.lineMap a b t) = (1 - t) * L a + t * L b := by
    dsimp only [L]
    simp only [AffineMap.lineMap_apply_module, Complex.real_smul, Complex.mul_im,
      Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  rw [openSegment_eq_image_lineMap] at hzi hzj
  obtain ⟨s, hs, hes⟩ := hzi
  obtain ⟨t, ht, het⟩ := hzj
  have hLz : L z = 0 := by
    rw [← hes, hlin, hui, hvi]
    ring
  have hsum : (1 - t) * f (u j) + t * f (v j) = 0 := by
    change (1 - t) * L (g (u j)) + t * L (g (v j)) = 0
    rw [← hlin, het]
    exact hLz
  have hends : f (u j) = 0 ∧ f (v j) = 0 := by
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht1 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
    have hzeroProd : (1 - t) * f (u j) = 0 ∧ t * f (v j) = 0 := by
      rcases hside with hneg | hpos
      · have ha := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr ht.2).le hneg.1
        have hb := mul_nonpos_of_nonneg_of_nonpos ht.1.le hneg.2
        constructor <;> linarith
      · have ha := mul_nonneg (sub_pos.mpr ht.2).le hpos.1
        have hb := mul_nonneg ht.1.le hpos.2
        constructor <;> linarith
    exact ⟨(mul_eq_zero.mp hzeroProd.1).resolve_left ht1,
      (mul_eq_zero.mp hzeroProd.2).resolve_left ht0⟩
  have hu := hzero (u j) hends.1
  have hv := hzero (v j) hends.2
  have hpair : (u j = u i ∧ v j = v i) ∨ (u j = v i ∧ v j = u i) := by
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (hDistinct j (hu.trans hv.symm)).elim
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
    · exact (hDistinct j (hu.trans hv.symm)).elim
  have hm := midpoint_mem_openSegment (𝕜 := ℝ) (σ (u i)) (σ (v i))
  have hmj : midpoint ℝ (σ (u i)) (σ (v i)) ∈
      openSegment ℝ (σ (u j)) (σ (v j)) := by
    rcases hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simpa only [hu, hv] using hm
    · simpa only [hu, hv, openSegment_symm] using hm
  exact Set.disjoint_left.mp (hChordsDisjoint hij) hm hmj


end HolomorphicAnosov
