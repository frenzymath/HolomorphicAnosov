import HolomorphicAnosov.Topology.TwoArcsCircleEmbedding
import HolomorphicAnosov.Topology.GallierXuSurfacePresentation
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Traversing chains of coordinate edges

Gallier--Xu Chapter 2 geometric realizations. Distinct coordinate vertices
form an embedded edge chain. Concatenating successive affine segment paths
parametrizes it injectively: a new edge intersects the previous chain only
at their common endpoint, as witnessed by its fresh vertex coordinate.
-/
open Set
namespace HolomorphicAnosov.Topology.GallierXu

/-- Concatenation of two injective paths remains injective when their only
intersection is their prescribed common endpoint. -/
theorem path_trans_injective_g9 {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hc : ∀ s t, p s = q t → s = 1 ∧ t = 0) :
    Function.Injective (p.trans q) := by
  intro s t h
  rw [Path.trans_apply, Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have he := congrArg Subtype.val (hp h)
    apply Subtype.ext
    dsimp at he
    linarith
  · have he := congrArg Subtype.val (hc _ _ h).2
    dsimp at he
    have := t.property.1
    linarith
  · have he := congrArg Subtype.val (hc _ _ h.symm).2
    dsimp at he
    linarith
  · have he := congrArg Subtype.val (hq h)
    apply Subtype.ext
    dsimp at he
    linarith

/-- A finite list of distinct coordinate vertices admits an injective path
whose image is exactly the union of the successive affine edges. -/
theorem coordinate_edge_chain_g9 {N n : ℕ}
    (v : Fin (n + 2) → Fin N) (hv : Function.Injective v) :
    ∃ p : Path (Pi.single (v 0) (1 : ℝ)) (Pi.single (v (Fin.last (n+1))) 1),
      Function.Injective p ∧
      range p = ⋃ i : Fin (n+1),
        segment ℝ (Pi.single (v i.castSucc) 1) (Pi.single (v i.succ) 1) := by
  induction n with
  | zero =>
    refine ⟨Path.segment _ _, Path.segment_injective_of_ne ?_, ?_⟩
    · intro h
      have he := congrFun h (v 0)
      have hne : v (0 : Fin 2) ≠ v (1 : Fin 2) := hv.ne (by decide)
      simp [hne] at he
    · simp only [Path.range_segment]
      ext x
      simp only [mem_iUnion]
      constructor
      · exact fun hx ↦ ⟨0, hx⟩
      · rintro ⟨i, hi⟩
        have hi0 : i = 0 := by omega
        simpa [hi0] using hi
  | succ n ih =>
    let v' : Fin (n+2) → Fin N := fun i ↦ v i.castSucc
    have hv' : Function.Injective v' := hv.comp (Fin.castSucc_injective _)
    obtain ⟨p, hp, hr⟩ := ih v' hv'
    let q : Path (X := Fin N → ℝ) (Pi.single (v' (Fin.last (n+1))) (1 : ℝ))
        (Pi.single (v (Fin.last (n+2))) 1) := Path.segment _ _
    have hnew (i : Fin (n+2)) : v i.castSucc ≠ v (Fin.last (n+2)) := by
      apply hv.ne
      exact Fin.castSucc_ne_last i
    have hz (s : unitInterval) : p s (v (Fin.last (n+2))) = 0 := by
      have hm : p s ∈ range p := ⟨s, rfl⟩
      rw [hr] at hm
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm
      obtain ⟨a, b, _, _, _, he⟩ := hi
      rw [← he]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hu := hnew i.castSucc
      have hv := hnew i.succ
      simp only [v', Pi.single_eq_of_ne hu.symm, Pi.single_eq_of_ne hv.symm, mul_zero, add_zero]
    have hq : Function.Injective q := by
      apply Path.segment_injective_of_ne
      intro he
      have hh := congrFun he (v (Fin.last (n+2)))
      simp [v', hnew] at hh
    have hc (s t : unitInterval) (he : p s = q t) : s = 1 ∧ t = 0 := by
      have hh := congrFun he (v (Fin.last (n+2)))
      rw [hz] at hh
      have ht : t = 0 := by
        apply Subtype.ext
        simpa [q, Path.segment_apply, AffineMap.lineMap_apply_module, v', hnew] using hh.symm
      subst t
      refine ⟨hp ?_, rfl⟩
      simpa using he
    refine ⟨p.trans q, path_trans_injective_g9 p q hp hq hc, ?_⟩
    change range (p.trans q) = _
    rw [Path.trans_range, hr, show range q = _ from Path.range_segment _ _]
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨i, hi⟩ | hi)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n+1), hi⟩
    · rintro ⟨i, hi⟩
      cases i using Fin.lastCases with
      | last => exact Or.inr hi
      | cast i => exact Or.inl ⟨i, hi⟩

/-- A simple cyclic list of coordinate vertices parametrizes an embedded circle.
Traverse all but the closing edge as the injective chain above. The closing
segment meets this chain only at its two endpoints by coordinate support.
The two-arc circle theorem supplies the endpoint-identified parametrization. -/
theorem coordinate_cycle_circle_g9 {N n : ℕ}
    (v : Fin (n+3) → Fin N) (hv : Function.Injective v) :
    ∃ j : Circle → (Fin N → ℝ), _root_.Topology.IsEmbedding j ∧
      range j = ⋃ i : Fin (n+3),
        segment ℝ (Pi.single (v i) 1) (Pi.single (v (finRotate (n+3) i)) 1) := by
  obtain ⟨p, hp, hr⟩ := coordinate_edge_chain_g9 (n := n+1) v hv
  let q : Path (X := Fin N → ℝ) (Pi.single (v 0) 1)
      (Pi.single (v (Fin.last (n+2))) 1) := Path.segment _ _
  have hend : v 0 ≠ v (Fin.last (n+2)) := hv.ne (by intro h; have := congrArg Fin.val h; simp at this)
  have hq : Function.Injective q := by
    apply Path.segment_injective_of_ne
    intro h
    have hh := congrFun h (v 0)
    simp [hend] at hh
  have hc (s t : unitInterval) (he : p s = q t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have hm : p s ∈ range p := ⟨s, rfl⟩
    rw [hr] at hm
    obtain ⟨i, a, b, _, _, hab, heq⟩ := mem_iUnion.mp hm
    by_cases hi : i.castSucc = 0
    · have hlast : v i.castSucc ≠ v (Fin.last (n+2)) := hv.ne (by rw [hi]; intro h; have := congrArg Fin.val h; simp at this)
      have hnext : v i.succ ≠ v (Fin.last (n+2)) := hv.ne (by
        intro h
        have hh := congrArg Fin.val hi
        have hh' := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_succ, Fin.val_last] at hh hh'
        omega)
      have hz : p s (v (Fin.last (n+2))) = 0 := by
        rw [← heq]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.single_eq_of_ne hlast.symm, Pi.single_eq_of_ne hnext.symm, mul_zero, add_zero]
      have ht : t = 0 := by
        apply Subtype.ext
        have hh := congrFun he (v (Fin.last (n+2)))
        rw [hz] at hh
        simpa [q, Path.segment_apply, AffineMap.lineMap_apply_module, hend] using hh.symm
      subst t
      exact Or.inl ⟨hp (by simpa using he), rfl⟩
    · have hfirst : v i.castSucc ≠ v 0 := hv.ne hi
      have hnext : v i.succ ≠ v 0 := hv.ne (Fin.succ_ne_zero _)
      have hz : p s (v 0) = 0 := by
        rw [← heq]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.single_eq_of_ne hfirst.symm, Pi.single_eq_of_ne hnext.symm, mul_zero, add_zero]
      have ht : t = 1 := by
        apply Subtype.ext
        have hh := congrFun he (v 0)
        rw [hz] at hh
        simp [q, Path.segment_apply, AffineMap.lineMap_apply_module, hend] at hh
        change (t : ℝ) = 1
        linarith
      subst t
      exact Or.inr ⟨hp (by simpa using he), rfl⟩
  obtain ⟨j, hj, hjr⟩ := HolomorphicAnosov.twoArcs_circle_embedding p q p.continuous
    q.continuous hp hq (by simp) (by simp) hc
  refine ⟨j, hj, hjr.trans ?_⟩
  rw [hr, show range q = _ from Path.range_segment _ _]
  ext x
  simp only [mem_union, mem_iUnion]
  have hrot (i : Fin (n+2)) : finRotate (n+3) i.castSucc = i.succ :=
    finRotate_of_lt i.isLt
  constructor
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, by simpa only [hrot] using hi⟩
    · exact ⟨Fin.last (n+2), by simpa only [finRotate_last, segment_symm] using hi⟩
  · rintro ⟨i, hi⟩
    cases i using Fin.lastCases with
    | last => exact Or.inr (by simpa only [finRotate_last, segment_symm] using hi)
    | cast i => exact Or.inl ⟨i, by simpa only [hrot] using hi⟩

/-- Every simple coordinate boundary cycle with at least three vertices is
homeomorphic to the standard circle. The homeomorphism has the original
carrier-side contour as its target, with its actual subtype topology. -/
theorem boundaryCycle_circle_homeomorph_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (l : List (Fin N))
    (hnd : l.Nodup) (hlen : 3 ≤ l.length)
    (hcycle : ∀ i : Fin l.length,
      ({l.get i, l.get (finRotate l.length i)} : Finset (Fin N)) ∈ K.faces) :
    Nonempty (Circle ≃ₜ ↥(cycleCarrier (K := K) l)) := by
  classical
  have generic (m : ℕ) (v : Fin m → Fin N) (hm : 3 ≤ m) (hv : Function.Injective v) :
      ∃ j : Circle → (Fin N → ℝ), _root_.Topology.IsEmbedding j ∧
        range j = ⋃ i : Fin m,
          segment ℝ (Pi.single (v i) 1) (Pi.single (v (finRotate m i)) 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n+3 := ⟨m-3, by omega⟩
    exact coordinate_cycle_circle_g9 v hv
  obtain ⟨j, hj, hr⟩ := generic l.length l.get hlen hnd.injective_get
  have hchar (x : Fin N → ℝ) : x ∈ range j ↔
      ∃ y : ↥(cycleCarrier (K := K) l), y.val.val = x := by
    constructor
    · intro hx
      rw [hr] at hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hxK : x ∈ carrier K := by
        have hs : (∀ w, 0 ≤ x w) ∧ ∑ w, x w = 1 := by
          obtain ⟨a, b, ha, hb, hab, he⟩ := hi
          rw [← he]
          constructor
          · intro w
            exact add_nonneg (mul_nonneg ha (by simp [Pi.single_apply]; positivity))
              (mul_nonneg hb (by simp [Pi.single_apply]; positivity))
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
              ← Finset.mul_sum]
            simp only [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
            exact hab
        refine ⟨hs, _, hcycle i, ?_⟩
        intro w hw
        have hh : w ≠ l.get i ∧ w ≠ l.get (finRotate l.length i) := by simpa using hw
        obtain ⟨a, b, _, _, _, he⟩ := hi
        rw [← he]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.single_eq_of_ne hh.1, Pi.single_eq_of_ne hh.2, mul_zero, add_zero]
      refine ⟨⟨⟨x, hxK⟩, ?_⟩, rfl⟩
      exact ⟨_, _, ⟨i, Or.inl ⟨rfl, rfl⟩⟩, hi⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨u, v, ⟨i, hi | hi⟩, hseg⟩ := y.property
      · rw [hr]
        exact mem_iUnion.mpr ⟨i, by simpa only [hi.1, hi.2] using hseg⟩
      · rw [hr]
        exact mem_iUnion.mpr ⟨i, by simpa only [hi.1, hi.2, segment_symm] using hseg⟩
  have hpre (z : Circle) : ∃ y : ↥(cycleCarrier (K := K) l), y.val.val = j z :=
    (hchar (j z)).mp ⟨z, rfl⟩
  choose f hf using hpre
  have hcont : Continuous f := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have he : (fun z ↦ (f z).val.val) = j := funext hf
    rw [he]
    exact hj.continuous
  have hinj : Function.Injective f := by
    intro z w h
    apply hj.injective
    rw [← hf z, ← hf w, h]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := (hchar y.val.val).mpr ⟨y, rfl⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (hf z).trans hz
  exact ⟨(hcont.isClosedEmbedding hinj).isEmbedding.toHomeomorphOfSurjective hsurj⟩

end HolomorphicAnosov.Topology.GallierXu


