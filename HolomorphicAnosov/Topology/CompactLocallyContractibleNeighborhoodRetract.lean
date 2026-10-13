import HolomorphicAnosov.Topology.HatcherControlledPartialRetraction
import HolomorphicAnosov.Topology.NeighborhoodRetractOfControl

/-!
# Compact weakly locally contractible Euclidean sets are neighborhood retracts

Source: Allen Hatcher, *Algebraic Topology*, Theorem A.7, printed pp. 525--527,
specifically the harder implication and its controlled extension argument on p. 526.
The local hypothesis below concerns null-homotopies of inclusions, with the native
subspace topologies; the conclusion is an actual retraction from an open Euclidean set.
-/

namespace HolomorphicAnosov

/--
Hatcher, *Algebraic Topology*, Theorem A.7 (harder implication), pp. 525--527.

Proof. If `C` is empty, choose the empty open neighborhood and its unique map to
`C`. If `N=0` and `C` is nonempty, the Euclidean space is a point; the identity
map retracts it onto `C`. For positive `N` and nonempty `C`, use the dyadic
complement construction to give `ℝ^N \ C` a locally finite regular CW structure
of dimension at most `N`, whose closed cells shrink toward every point of `C`.

At each vertex choose a nearest point of compact `C`. Its distance from that
vertex is at most the distance to any prescribed point of `C`. Inductively include
a cell whose boundary lies in the selected lower skeleton precisely when the
boundary map extends over the closed cell into `C`. Choose a constant extension
when the boundary map is constant. Otherwise its boundary image has positive
diameter `b`; all extension-image diameters are finite and at least `b`. Their
infimum `a` is positive, so choose an extension of diameter less than `2a`.
Thus the selected image diameter is less than twice any candidate diameter.
The selected cells form a subcomplex `Z`. Their maps agree on boundaries and
overlaps. Local finiteness of the closed cells makes the glued map `r : Z → C`
continuous, since the preimage of a closed set is a locally finite union of closed
preimage pieces. Repeat this construction through dimension `N`.

Fix `c ∈ C` and an arbitrary relative ball `O` about `c`. Choose successively
centered relative balls `V_i ⊆ U_i`, for `i=N,...,0`, whose inclusions into
`U_i` are null-homotopic, with `U_N=O`. The given open neighborhood condition
allows these choices by restricting its homotopy to a smaller centered ball.
For `i<N`, first make `U_i` so small inside `V_(i+1)` that
`radius(V_i) + 4 radius(U_i) < radius(V_(i+1))`.
Choose an ambient ball `B(c,t)` with `2t < radius(V_0)` and let `Y` be the
subcomplex of cells whose closures lie inside this ball. Nearest-point control
puts the vertex images in `V_0`.

Inductively, if the boundary image of an `(i+1)`-cell lies in `V_i`, composing
its boundary map with the null-homotopy into `U_i` gives a closed-ball extension:
at radial point `sθ`, use the homotopy at `1-s`, and at the center use its
constant endpoint. The homotopy descends through the cone on the sphere, so this
extension is continuous. Its diameter is at most `2 radius(U_i)`. The selected
extension has diameter less than `4 radius(U_i)`, or zero for a constant boundary.
Comparing with a boundary value in `V_i` puts its entire image in `V_(i+1)`.
Thus `Y ⊆ Z` and `r(Y) ⊆ V_N ⊆ O`.

Cell shrinking gives `δ>0` such that every closed cell meeting `B(c,δ)` lies
inside `B(c,t)`. Hence `B(c,δ) \ C ⊆ Y ⊆ Z`. Reduce `δ` to ensure also
`C ∩ B(c,δ) ⊆ O`, and extend `r` by the identity on `C`. The extended map sends
`(Z ∪ C) ∩ B(c,δ)` into `O`, proving continuity at `c` and showing that `c`
is interior to `Z ∪ C`. Off the closed set `C`, continuity is the existing
continuity on `Z`. Therefore the interior of `Z ∪ C` is an open neighborhood
of `C`, and restriction of the extended map to it gives the required retraction.

This is the source-backed natural-language proof from the node; the dyadic
complement CW supplier and the formal proof remain separate obligations.
-/
theorem compact_locally_contractible_neighborhood_retract
    (N : ℕ) (C : Set (EuclideanSpace ℝ (Fin N))) (hC : IsCompact C)
    (hlocal : ∀ (c : C) (O : Set C), IsOpen O → c ∈ O →
      ∃ V : Set C, IsOpen V ∧ c ∈ V ∧
        ∃ hVO : V ⊆ O, (ContinuousMap.inclusion hVO).Nullhomotopic) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin N))) (hCU : C ⊆ U), IsOpen U ∧
      ∃ r : C(U, C), ∀ c : C, r ⟨c.val, hCU c.property⟩ = c := by
  classical
  by_cases hne : C.Nonempty
  · by_cases hN : N = 0
    · subst N
      obtain ⟨c, hc⟩ := hne
      refine ⟨Set.univ, Set.subset_univ C, isOpen_univ,
        ContinuousMap.const _ ⟨c, hc⟩, ?_⟩
      intro x
      exact Subsingleton.elim _ _
    · obtain ⟨Z, r, hr, hfix, hcontrol⟩ :=
        hatcher_controlled_partial_retraction N (Nat.pos_of_ne_zero hN) C hC hne hlocal
      exact neighborhood_retract_of_control C Z hC.isClosed r hr hfix hcontrol
  · have hempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst C
    refine ⟨∅, Set.Subset.rfl, isOpen_empty, ContinuousMap.id _, ?_⟩
    intro c
    exact c.property.elim

end HolomorphicAnosov
