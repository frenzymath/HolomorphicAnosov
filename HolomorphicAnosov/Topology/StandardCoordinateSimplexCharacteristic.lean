import HolomorphicAnosov.Topology.ConvexBodyCharacteristicMap
import Mathlib.Logic.Equiv.PartialEquiv
import HolomorphicAnosov.Topology.StandardCoordinateSimplexBody

namespace HolomorphicAnosov

open Set Topology _root_.Topology Metric Bornology

/-!
# Characteristic disk for the standard barycentric coordinate simplex

This module isolates the next construction required by the face-indexed
characteristic family.  It is independent of the geometric carrier: the
parameter space is the original finite product `Fin d → ℝ` with its native
maximum norm.
-/

/-- The standard normalized barycentric coordinate simplex has one characteristic
map from the native unit disk.

Source: Hatcher, *Algebraic Topology*, §2.1, pp.103--104, where normalized
barycentric coordinates identify a simplex with nonnegative coefficients whose
sum is one, and Proposition A.2, p.521, where the characteristic map is
required to map the closed disk to the closed cell, the open disk to its
interior, and the sphere to the lower-dimensional boundary.  The ambient
radial construction is the gauge homeomorphism in pinned Mathlib
`Analysis/Convex/GaugeRescale.lean:185--197`, specialized to the coordinate
simplex.

Natural-language proof obligation: for `V = Fin d → ℝ`, define
`Delta = {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}` and
`I = {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}`.  The coordinate inequalities make
`Delta` closed and convex; each coordinate is bounded by one, so `Delta` is
bounded in the finite-product maximum norm.  The point with every coordinate
`1/(d+1)` lies in `I`, including the zero-dimensional singleton case.  A
finite-product perturbation argument proves `interior Delta = I`: positive
coordinates and a strict sum inequality contain a small maximum-norm ball,
while a zero coordinate or a sum equal to one is violated by a one-coordinate
perturbation.  The gauge theorem then supplies one ambient homeomorphism
sending `I`, `Delta`, and `frontier Delta` to the open ball, closed ball, and
sphere.  Compose its inverse with the continuous radial retraction
`u ↦ (max 1 ‖u‖)⁻¹ • u` and restrict to the open-ball source and `I` target.
The resulting partial equivalence is continuous in both directions and has
closed/open/sphere images `Delta`, `I`, and `frontier Delta`.  Since every
normalized coefficient family has at least one positive coefficient, the
frontier is exactly the union of the nonnegative proper barycentric faces,
including the empty sphere when `d = 0`.  No geometric face, ambient interior,
Euclidean L2 norm, or nonempty-complex hypothesis is introduced.
-/
theorem standard_coordinate_simplex_characteristic (d : ℕ) :
    let V := Fin d → ℝ
    let Delta : Set V := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}
    let I : Set V := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
    ∃ χ : PartialEquiv V V,
      χ.source = ball 0 1 ∧
      χ.target = I ∧
      Continuous χ ∧
      Continuous χ.symm ∧
      χ '' closedBall 0 1 = Delta ∧
      χ '' ball 0 1 = I ∧
      χ '' sphere 0 1 = frontier Delta := by
  dsimp
  obtain ⟨hconv, hclosed, hbounded, hne, hinterior, hfrontier⟩ :=
    standard_coordinate_simplex_body d
  obtain ⟨χ, hsource, htarget, hcont, hinv, hmem, hclosedImage, hopen, hsphere⟩ :=
    convex_body_characteristic_map hconv hne hbounded hclosed
  rw [hinterior] at htarget hopen
  exact ⟨χ, hsource, htarget, hcont, hinv, hclosedImage, hopen, hsphere⟩


end HolomorphicAnosov
