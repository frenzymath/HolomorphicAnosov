import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeleta

/-!
# Descent of compatible interval extensions on CW skeleta

Source: Fritsch–Piccinini, *Cellular Structures in Topology* (1990),
Appendix A.5.1(iv), p. 274: compatible extensions on successive skeleta
assemble to an extension on the weak-topology union. The characteristic-prism
descent is supplied by the existing CW topology interface.
-/

namespace HolomorphicAnosov.Topology.CWComplex

universe u

/-- Successor-compatible interval maps on all finite skeleta that extend given
subspace data descend to a continuous extension on the original CW carrier.
Iterating successor agreement yields agreement at any pair of comparable
stages; the existing characteristic-prism gluing theorem then applies to
maps constant in the interval parameter. Skeletal exhaustion proves agreement
with the prescribed data at every point of its domain. No closedness of that
domain is needed once the continuous skeletal extensions have been supplied. -/
theorem exists_extension_of_compatible_skeletal_extensions
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)]
    (A : Set X) (g : C(A, unitInterval))
    (f : ∀ n : ℕ,
      C((_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X),
        unitInterval))
    (hstep : ∀ (n : ℕ)
      (x : (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)),
      f n x = f (n + 1) ⟨x.val, _root_.Topology.RelCWComplex.skeleton_mono
        (by exact_mod_cast Nat.le_succ n) x.property⟩)
    (hdata : ∀ (n : ℕ)
      (x : (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X))
      (hx : x.val ∈ A), f n x = g ⟨x.val, hx⟩) :
    ∃ F : C(X, unitInterval), ∀ x : A, F x = g x := by
  have hcompat : ∀ (m n : ℕ) (hmn : m ≤ n)
      (x : (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X)),
      f m x = f n ⟨x.val, _root_.Topology.RelCWComplex.skeleton_mono
        (by exact_mod_cast hmn) x.property⟩ := by
    intro m n hmn x
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      exact ih.trans (hstep n ⟨x.val, _root_.Topology.RelCWComplex.skeleton_mono
        (by exact_mod_cast hmn) x.property⟩)
  obtain ⟨H, hH⟩ := HolomorphicAnosov.cw_prism_of_compatible_skeleta
    (K := X) (Y := unitInterval)
    (fun n ↦ ⟨fun q ↦ f n q.2,
      (f n).continuous.comp continuous_snd⟩)
    (by
      intro m n hmn t x
      exact hcompat m n hmn x)
  refine ⟨⟨fun x ↦ H (0, x), H.continuous.comp (continuous_const.prodMk continuous_id)⟩, ?_⟩
  intro x
  have hx : x.val ∈ ⋃ n : ℕ,
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) := by
    rw [_root_.Topology.CWComplex.iUnion_skeleton_eq_complex]
    exact Set.mem_univ _
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact (hH n 0 ⟨x.val, hn⟩).trans (hdata n ⟨x.val, hn⟩ x.property)

end HolomorphicAnosov.Topology.CWComplex

