import HolomorphicAnosov.Topology.HatcherCenteredNullhomotopicBall
import HolomorphicAnosov.Topology.HatcherDyadicComplementShrinkingCW
import HolomorphicAnosov.Topology.ControlledExtensionDiameter
import HolomorphicAnosov.Topology.HatcherControlledPartialRetractionHigherCells
import HolomorphicAnosov.Topology.HatcherNearestPointFactorTwo
import Mathlib.Topology.Homotopy.Contractible

/-!
# Hatcher's controlled partial retraction

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed pp.525–526.
The selected CW subcomplex admits a continuous partial retraction with small
images near the compact set. Its union with the compact set contains a neighborhood.
-/

namespace HolomorphicAnosov

/-- Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed pp.525–526.

For positive ambient dimension and nonempty compact C, apply the dyadic
complement construction to its original Euclidean complement. The closed cells
are locally finite, have dimension at most N, and shrink near C.

At each vertex choose a nearest point of compact `C`. Its distance from that
vertex is at most the distance to any prescribed point of `C`. Inductively include
a cell whose boundary lies in the selected lower skeleton precisely when the
boundary map extends over the closed cell into `C`. Choose a constant extension
when the boundary map is constant. Otherwise its boundary image has positive
diameter `b`; all extension-image diameters are finite and at least `b`. Their
infimum `a` is positive, so choose an extension of diameter less than `2a`.
Thus the selected image diameter is at most twice any candidate diameter.
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
extension has diameter at most `4 radius(U_i)`, or zero for a constant boundary.
Comparing with a boundary value in `V_i` puts its entire image in `V_(i+1)`.
Thus `Y ⊆ Z` and `r(Y) ⊆ V_N ⊆ O`.

Cell shrinking supplies δ>0 such that every closed cell meeting B(c,δ) lies
inside B(c,t). Hence B(c,δ) minus C lies in Y and its image lies in O. Since
O can be any relative ε-ball, this gives exactly the displayed estimate.
Let Z be the image in the ambient Euclidean space of the selected subcomplex.
The complement's subtype inclusion is an open embedding because C is closed;
therefore continuity on that subcomplex is continuity on Z in its induced topology.
Extend the map by the identity on C, and by an arbitrary chosen point of the
nonempty C elsewhere. This defines a total function r without asserting continuity
outside Z or at C; continuity at C follows later from the displayed control.

The extension selection uses the proved controlled-diameter lemma, with constant
boundary data treated by a constant extension. A positive-dimensional attaching
sphere is nonempty, so the diameter comparison and a boundary anchor are available.
Dimension-zero cells use nearest points and do not require a sphere anchor.
-/
theorem hatcher_controlled_partial_retraction
    (N : ℕ) (hN : 0 < N) (C : Set (EuclideanSpace ℝ (Fin N)))
    (hC : IsCompact C) (hne : C.Nonempty)
    (hlocal : ∀ (c : C) (O : Set C), IsOpen O → c ∈ O →
      ∃ V : Set C, IsOpen V ∧ c ∈ V ∧
        ∃ hVO : V ⊆ O, (ContinuousMap.inclusion hVO).Nullhomotopic) :
    ∃ (Z : Set (EuclideanSpace ℝ (Fin N))) (r : EuclideanSpace ℝ (Fin N) → C),
      ContinuousOn r Z ∧ (∀ c : C, r c = c) ∧
      ∀ c : C, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        Metric.ball c.val δ ⊆ Z ∪ C ∧
        ∀ z ∈ Z, dist z c.val < δ → dist (r z).val c.val < ε := by
  classical
  obtain ⟨c₀, hc₀⟩ := hne
  by_cases hsub : C.Subsingleton
  · let r : EuclideanSpace ℝ (Fin N) → C := fun _ ↦ ⟨c₀, hc₀⟩
    refine ⟨Set.univ, r, continuousOn_const, ?_, ?_⟩
    · intro c
      exact Subtype.ext (hsub hc₀ c.property)
    · intro c ε hε
      refine ⟨1, zero_lt_one, (fun _ _ ↦ Or.inl (Set.mem_univ _)), ?_⟩
      intro z hz hdist
      have heq : (r z).val = c.val := hsub hc₀ c.property
      simpa only [heq, dist_self] using hε
  obtain ⟨nearest, hfix, hcontrol⟩ := nearest_point_factor_two N C hC ⟨c₀, hc₀⟩
  have hball (c : C) (R : ℝ) (hR : 0 < R) :=
    hatcher_centered_nullhomotopic_ball C hlocal c R hR
  obtain ⟨cw, hfinite, hdim, hfaces, hregular, hboundary, hshrink⟩ :=
    hatcher_dyadic_complement_shrinking_cw N hN C hC
  -- The nearest-point map supplies the original zero-cell values and the
  -- factor-two estimate needed in the source's small-neighborhood induction.
  -- Centered relative balls with nullhomotopic inclusions are supplied by hball.
  -- The source-backed higher-cell stage owns the dependent CW extension,
  -- locally finite gluing, and shrinking-neighborhood argument.
  exact hatcher_controlled_partial_retraction_higher_cells N hN C hC
    ⟨c₀, hc₀⟩ hsub hlocal

end HolomorphicAnosov
