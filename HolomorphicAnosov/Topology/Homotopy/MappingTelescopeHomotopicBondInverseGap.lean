import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeEndpointVaryingCancellation

/-! # Relative inverse homotopies for the homotopic-bond comparison
Source: Hatcher, *Algebraic Topology*, Proposition A.11(1), p.528, and the
relative attaching-map comparison of Proposition 0.18, p.16.
-/

universe u

namespace HolomorphicAnosov.MappingTelescope.Sequence

open ContinuousMap

/-- The two explicitly defined comparison maps are inverse up to homotopies
fixed on every canonical level.

Source: Hatcher, Proposition A.11(1), p.528, using Proposition 0.18, p.16.
The following spells out the cancellation in the cylinder model. Write `c_n`
for a canonical cylinder path and `h_n` for the bond homotopy in level `n+1`.
The forward comparison follows `c_n(g)` and then `h_n` backwards. The reverse
comparison follows `c_n(f)` and then `h_n`. Both comparisons are the identity
on each level, by `homotopicBondMap_level`. Therefore their composite on a
source cylinder follows `(c_n(f) * h_n) * reverse(h_n)`, with time lengths
one quarter, one quarter, and one half. First vary these lengths linearly to
one half, one quarter, and one quarter, keeping all breakpoints strictly
ordered. Closed pasting gives a jointly continuous reparametrization homotopy.
Next contract the last two pieces: for contraction parameter s, on the first
of these pieces evaluate h_n at `(1-s)u`, and on the second evaluate it at
`(1-s)(1-u)`. The shared value at their middle is `h_n(1-s)`, and their outer
endpoints remain `h_n(0)`. At s=1 this is a constant final half. Finally stretch
the first cylinder half to the full interval, equivalently deform its time
parameter from `min(2t,1)` to `t` by convex interpolation. All three homotopies
fix the cylinder endpoints. Their endpoint values agree on every telescope
seam and are constant in the homotopy parameter, so they fix all canonical
levels. Take the disjoint union of these formulas and descend through the
quotient. Joint continuity follows by currying the compact homotopy interval,
continuous quotient descent, and continuous evaluation; no local compactness
of the spaces X_n is used. Replacing h_n by its reverse gives the second
inverse homotopy by the identical construction. Empty spaces need no exception.
-/
/- The two comparison composites fix every canonical level pointwise.

This is the endpoint calculation used by the relative inverse homotopies below;
source: Hatcher, Proposition A.11(1), p.528. -/
theorem homotopicBondMap_inverse_level
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    {f g : ∀ n, C(X n, X (n + 1))} (H : ∀ n, (f n).Homotopy (g n))
    (n : ℕ) (x : X n) :
    (homotopicBondMap (fun n ↦ (H n).symm))
        (homotopicBondMap H (level f n x)) = level f n x ∧
    (homotopicBondMap H)
        (homotopicBondMap (fun n ↦ (H n).symm) (level g n x)) = level g n x := by
  constructor
  · rw [homotopicBondMap_level H]
    exact homotopicBondMap_level (fun n ↦ (H n).symm) n x
  · rw [homotopicBondMap_level (fun n ↦ (H n).symm)]
    exact homotopicBondMap_level H n x

theorem homotopicBondMap_inverse_gap
    {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    {f g : ∀ n, C(X n, X (n + 1))} (H : ∀ n, (f n).Homotopy (g n)) :
    ((homotopicBondMap (fun n ↦ (H n).symm)).comp (homotopicBondMap H)).HomotopicRel
      (ContinuousMap.id (telescope f)) (⋃ n, Set.range (level f n)) ∧
    ((homotopicBondMap H).comp (homotopicBondMap (fun n ↦ (H n).symm))).HomotopicRel
      (ContinuousMap.id (telescope g)) (⋃ n, Set.range (level g n)) := by
  obtain ⟨F, G, _⟩ := exists_endpoint_varying_cylinder_cancellation H
  exact ⟨⟨F⟩, ⟨G⟩⟩

end HolomorphicAnosov.MappingTelescope.Sequence
