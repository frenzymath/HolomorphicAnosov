import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeleta

namespace HolomorphicAnosov
universe u v

/-- Compatible continuous maps on all finite skeleta descend to a continuous map
on the original CW space, with exactly their prescribed restrictions.

Source: Hatcher, Algebraic Topology, Appendix A.2, pp.520–523. Apply the existing
characteristic-prism descent to maps constant in the interval coordinate and
restrict the resulting continuous prism to time zero. No finite-dimensional or
locally finite hypothesis is required; empty skeleta cause no difficulty. -/
theorem cw_map_of_compatible_skeleta
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [_root_.Topology.CWComplex (Set.univ : Set K)]
    (F : ∀ n : ℕ, C((_root_.Topology.RelCWComplex.skeleton
      (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (hcompat : ∀ (m n : ℕ) (hmn : m ≤ n)
      (x : (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set K) (m : ℕ∞) : Set K)),
      F m x = F n ⟨x.val, _root_.Topology.RelCWComplex.skeleton_mono
        (by exact_mod_cast hmn) x.property⟩) :
    ∃ f : C(K, Y), ∀ (n : ℕ)
      (x : (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
      f x.val = F n x := by
  let P (n : ℕ) : C(unitInterval ×
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y) :=
    ⟨fun x ↦ F n x.2, (F n).continuous.comp continuous_snd⟩
  obtain ⟨U, hU⟩ := cw_prism_of_compatible_skeleta P
    (fun m n hmn _ x ↦ hcompat m n hmn x)
  exact ⟨⟨fun x ↦ U (0, x), U.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    fun n x ↦ hU n 0 x⟩

end HolomorphicAnosov
