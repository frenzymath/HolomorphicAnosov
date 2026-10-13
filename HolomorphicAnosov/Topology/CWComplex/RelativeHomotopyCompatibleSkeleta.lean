import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeleta

namespace HolomorphicAnosov
universe u v

/-- Relative version of Hatcher's characteristic-prism gluing, used in Theorem
4.8, pp.349–351 and Appendix A.2/A.17, pp.520–521, 532–533. Compatible jointly
continuous homotopies on all finite skeleta glue over the original CW space.
The relative set can be arbitrary: closedness and the subcomplex property are
not needed once compatibility and fixedness have been supplied.

Proof: use the continuous compatible-skeleton prism descent. Every point lies
in a finite skeleton, so the prescribed zero and one slices and every fixed-set
equality pass from that skeleton to the descended map. -/
theorem cw_relative_homotopy_of_compatible_skeleta
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)]
    (A : Set K) (f g : C(K, Y))
    (H : ∀ n : ℕ, C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (hzero : ∀ n x, H n (0, x) = f x.val)
    (hone : ∀ n x, H n (1, x) = g x.val)
    (hfixed : ∀ n t x, x.val ∈ A → H n (t, x) = f x.val)
    (hcompat : ∀ (m n : ℕ) (hmn : m ≤ n) (t : unitInterval)
      (x : (Topology.CWComplex.skeleton (Set.univ : Set K) (m : ℕ∞) : Set K)),
      H m (t, x) = H n (t, ⟨x.val, Topology.CWComplex.skeleton_mono
        (by exact_mod_cast hmn) x.property⟩)) :
    ∃ F : ContinuousMap.HomotopyRel f g A, ∀ n t x, F (t, x.val) = H n (t, x) := by
  obtain ⟨U, hagree⟩ := cw_prism_of_compatible_skeleta H hcompat
  have hcover (x : K) : ∃ n : ℕ,
      x ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) := by
    apply Set.mem_iUnion.mp
    rw [Topology.CWComplex.iUnion_skeleton_eq_complex]
    exact Set.mem_univ x
  refine ⟨{
    toFun := U
    continuous_toFun := U.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }, ?_⟩
  · intro x
    obtain ⟨n, hx⟩ := hcover x
    exact (hagree n 0 ⟨x, hx⟩).trans (hzero n ⟨x, hx⟩)
  · intro x
    obtain ⟨n, hx⟩ := hcover x
    exact (hagree n 1 ⟨x, hx⟩).trans (hone n ⟨x, hx⟩)
  · intro t x hxA
    obtain ⟨n, hx⟩ := hcover x
    exact (hagree n t ⟨x, hx⟩).trans (hfixed n t ⟨x, hx⟩ hxA)
  · exact hagree

end HolomorphicAnosov
