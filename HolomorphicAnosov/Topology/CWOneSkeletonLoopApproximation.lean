import HolomorphicAnosov.Topology.CWComplex.CellularApproximation
import HolomorphicAnosov.Topology.CWIntervalProduct
import Mathlib.Topology.Homotopy.Path

/-!
# Based loops admit one-skeleton approximations

Source: Hatcher, Algebraic Topology, relative Cellular Approximation Theorem 4.8,
pp.349–351, applied to the interval relative to its endpoints. The interval CW
structure is the existing interval-product theorem. DAG node:
`topo.cw_one_skeleton_loop_approximation_g7`.
-/

namespace HolomorphicAnosov
open _root_.Topology

/-- Every loop at a vertex of a Hausdorff CW complex is based homotopic to a loop
in its original one-skeleton. Equip Unit × [0,1] with the existing product CW
structure and take its endpoint subcomplex. The loop is cellular on this
subcomplex since both endpoints map to the vertex. Relative cellular approximation
fixes these endpoints, and cellularity maps the entire interval into the target
one-skeleton. Restrict that approximant to the subspace topology and precompose
the relative homotopy with t ↦ ((),t). This supplies the required based homotopy.
No finiteness or connectedness assumption is needed. Source: Hatcher Theorem 4.8,
pp.349–351. -/
theorem cw_one_skeleton_loop_approximation
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] (x0 : X)
    (hx0 : x0 ∈ (CWComplex.skeletonLT (Set.univ : Set X) 1 : Set X))
    (α : Path x0 x0) :
    let K1 := ↥(CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X)
    let k1 : K1 :=
      ⟨x0, CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hx0⟩
    ∃ β : Path k1 k1, (β.map continuous_subtype_val).Homotopic α := by
  classical
  let C : Set X := Set.univ
  let S : Set X := CWComplex.skeletonLT C 2
  obtain ⟨K, labels, hend, hprism, _, ⟨A, hA, _⟩, _⟩ :=
    Topology.cw_interval_product (X := Unit)
  let : CWComplex (Set.univ : Set (Unit × unitInterval)) := K
  let V := RelCWComplex.cell (Set.univ : Set Unit) 0
  let vertex : V := ⟨(), Set.mem_univ ()⟩
  have hv (i : V) : RelCWComplex.closedCell 0 i = (Set.univ : Set Unit) := by
    rw [RelCWComplex.closedCell_zero_eq_singleton]
    exact Set.eq_univ_of_forall fun x ↦ Subsingleton.elim x _
  have hfull (z : Unit × unitInterval) :
      z ∈ (RelCWComplex.skeleton (Set.univ : Set (Unit × unitInterval)) 1 : Set _) := by
    apply RelCWComplex.closedCell_subset_skeleton 1
      (labels 1 (Sum.inr ⟨0, ⟨vertex, rfl⟩⟩))
    rw [(hprism 0 vertex).2.1, hv]
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  let f : C(Unit × unitInterval, X) := ⟨fun z ↦ α z.2,
    α.continuous.comp continuous_snd⟩
  have hxzero : x0 ∈ (RelCWComplex.skeleton C 0 : Set X) := hx0
  have hf : ∀ n : ℕ, Set.MapsTo f
      ((A : Set (Unit × unitInterval)) ∩
        (RelCWComplex.skeleton (Set.univ : Set (Unit × unitInterval)) n : Set _))
      (RelCWComplex.skeleton C n : Set X) := by
    intro n z hz
    have hz' := hz.1
    rw [hA] at hz'
    have hp : f z = x0 := by
      rcases hz'.2 with h | h
      · exact (congrArg α h).trans α.source
      · exact (congrArg α (Set.mem_singleton_iff.mp h)).trans α.target
    rw [hp]
    exact RelCWComplex.skeleton_mono (by simp) hxzero
  obtain ⟨c, hc, ⟨H⟩⟩ := Topology.CWComplex.cellularApproximation A f hf
  have hendpoint (t : unitInterval) (ht : t = 0 ∨ t = 1) : c ((), t) = x0 := by
    have ha : ((), t) ∈ (A : Set (Unit × unitInterval)) := by
      rw [hA]
      exact ⟨Set.mem_univ _, by simpa using ht⟩
    have heq := H.eq_fst 1 ha
    rw [H.apply_one] at heq
    change c ((), t) = α t at heq
    rcases ht with rfl | rfl
    · exact heq.trans α.source
    · exact heq.trans α.target
  let β : Path
      (⟨x0, CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hx0⟩ : S)
      (⟨x0, CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hx0⟩ : S) :=
    { toFun := fun t ↦ ⟨c ((), t), hc 1 (hfull ((), t))⟩
      continuous_toFun := (c.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
      source' := Subtype.ext (hendpoint 0 (Or.inl rfl))
      target' := Subtype.ext (hendpoint 1 (Or.inr rfl)) }
  refine ⟨β, ⟨?_⟩⟩
  refine
    { toFun := fun z ↦ H.symm (z.1, ((), z.2))
      continuous_toFun := H.symm.continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    exact H.symm.apply_zero ((), t)
  · intro t
    exact H.symm.apply_one ((), t)
  · intro t s hs
    have ha : ((), s) ∈ (A : Set (Unit × unitInterval)) := by
      rw [hA]
      exact ⟨Set.mem_univ _, hs⟩
    exact H.symm.eq_fst t ha

end HolomorphicAnosov
