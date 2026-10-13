import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.CellularSkeletalHomotopy
import HolomorphicAnosov.Topology.CWComplex.HomotopyExtension

namespace HolomorphicAnosov

/-- Extend the cellular deformation on A union the n-skeleton to the whole
source, preserving A and all lower skeleta. Source: Hatcher Theorem 4.8,
p.349, applying the homotopy extension property of Proposition 0.16.
The local skeletal homotopy starts at the restricted original map and
is constant on A and the lower skeleton. Extend it from its union subcomplex
by CW homotopy extension. Its time-one slice is the improved global map;
restriction back to the union proves both fixedness and n-cellularity. -/
theorem cw_skeletal_improvement
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (q : C(X, Y))
    (hA : Set.MapsTo q ((A : Set X) ∩
      (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X))
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y))
    (hbelow : ∀ m : ℕ, m < n → Set.MapsTo q
      (Topology.CWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X)
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (m : ℕ∞) : Set Y)) :
    ∃ r : C(X, Y), ∃ H : ContinuousMap.HomotopyRel q r (A : Set X),
      (∀ (m : ℕ), m < n → ∀ t x,
        x ∈ (Topology.CWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X) →
        H (t, x) = q x) ∧
      Set.MapsTo r
        (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)
        (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y) := by
  obtain ⟨B, hB, h, hzero, hfixed, hend⟩ := cw_cellular_skeletal_homotopy A n q hA hbelow
  obtain ⟨H, Hzero, Hres, _⟩ := cw_pair_homotopy_extension B q h hzero
  have hAB : (A : Set X) ⊆ (B : Set X) := by
    rw [hB]
    exact Set.subset_union_left
  have hSB : (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) ⊆
      (B : Set X) := by
    rw [hB]
    exact Set.subset_union_right
  let r : C(X, Y) := ⟨fun x ↦ H (1, x),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let G : ContinuousMap.HomotopyRel q r (A : Set X) := {
    toContinuousMap := H
    map_zero_left := Hzero
    map_one_left := fun _ ↦ rfl
    prop' := by
      intro t x hx
      change H (t, x) = q x
      rw [Hres t ⟨x, hAB hx⟩]
      exact hfixed t ⟨x, hAB hx⟩ (Or.inl hx) }
  refine ⟨r, G, ?_, ?_⟩
  · intro m hm t x hx
    have hxS := Topology.CWComplex.skeleton_mono (C := (Set.univ : Set X))
      (show (m : ℕ∞) ≤ (n : ℕ∞) by exact_mod_cast hm.le) hx
    have hxL : x ∈ (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
      obtain ⟨l, hl, i, hi⟩ := Topology.CWComplex.mem_skeleton_iff.mp hx
      exact Topology.CWComplex.mem_skeletonLT_iff.mpr
        ⟨l, hl.trans_lt (by exact_mod_cast hm), i, hi⟩
    change H (t, x) = q x
    rw [Hres t ⟨x, hSB hxS⟩]
    exact hfixed t ⟨x, hSB hxS⟩ (Or.inr hxL)
  · intro x hx
    change H (1, x) ∈ _
    rw [Hres 1 ⟨x, hSB hx⟩]
    exact hend ⟨x, hSB hx⟩ hx

end HolomorphicAnosov
