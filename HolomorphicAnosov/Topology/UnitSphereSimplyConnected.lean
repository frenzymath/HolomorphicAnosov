import HolomorphicAnosov.Topology.SimplyConnectedOfTwoOpenSets
import HolomorphicAnosov.Topology.SpherePunctureSimplyConnected
import HolomorphicAnosov.Topology.SphereTwoPuncturesPathConnected
import HolomorphicAnosov.Topology.UnitSphereRadialHomeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Subpath
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Simple connectedness of Euclidean and maximum-norm unit spheres

Source: Hatcher, *Algebraic Topology*, Proposition 1.14 and Lemma 1.15, printed p.35
(literature/hatcher-at.pdf, PDF page44). The native `EuclideanSpace` model has its L² norm;
the native finite product of real lines has its maximum norm. Both spheres carry the original
subtype topology. The radial formulas are included in the theorem, rather than an unspecified
choice of equivalence.
-/

namespace HolomorphicAnosov

open Set

/-- The Euclidean and maximum-norm spheres have the precise radial homeomorphism
used in the sphere theorem, without identifying their norms.

Source: the explicit finite-dimensional norm conversion in the proof of
`topo.unit_sphere_simply_connected_g9`, accompanying Hatcher Proposition 1.14 p.35.
Apply radial normalization to the actual `PiLp` continuous linear equivalence;
its forward and inverse maps are `WithLp.ofLp` and `WithLp.toLp 2`. -/
theorem unit_sphere_euclidean_max_radial (n : ℕ) :
    ∃ e : {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} ≃ₜ
        {w : Fin (n + 1) → ℝ // ‖w‖ = 1},
      (∀ v, (e v).val = ‖WithLp.ofLp v.val‖⁻¹ • WithLp.ofLp v.val) ∧
      (∀ w, (e.symm w).val =
        ‖WithLp.toLp 2 w.val‖⁻¹ • WithLp.toLp 2 w.val) := by
  exact unit_sphere_radial_homeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℝ))

/-- Stereographic charts give local path connectedness in the original norm-sphere
subtypes. Source: Step 5 of Hatcher Proposition 1.14, p.35, as expanded in
`topo.unit_sphere_simply_connected_g9`. The Euclidean chart model is locally
path connected, and the explicit radial homeomorphism transports this property
to the maximum-norm sphere. This local assertion also holds in dimension zero. -/
theorem unit_sphere_locally_path_connected (n : ℕ) :
    LocallyPathConnectedSpace {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} ∧
    LocallyPathConnectedSpace {w : Fin (n + 1) → ℝ // ‖w‖ = 1} := by
  have hs : LocallyPathConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hE : LocallyPathConnectedSpace
      {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} := by
    let h : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ₜ
        {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} :=
      Homeomorph.setCongr (by ext v; exact mem_sphere_zero_iff_norm)
    exact h.locallyPathConnectedSpace
  obtain ⟨e, _, _⟩ := unit_sphere_euclidean_max_radial n
  exact ⟨hE, e.locallyPathConnectedSpace⟩

/-- Radial normalization preserves simple connectedness for the exact original
sphere subtypes. Source: Step 6 of `topo.unit_sphere_simply_connected_g9`,
Hatcher Proposition 1.14, p.35. A homeomorphism is a homotopy equivalence,
so its induced equivalence of fundamental groupoids transports the property. -/
theorem unit_sphere_euclidean_max_simply_connected_iff (n : ℕ) :
    SimplyConnectedSpace {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} ↔
    SimplyConnectedSpace {w : Fin (n + 1) → ℝ // ‖w‖ = 1} := by
  obtain ⟨e, _, _⟩ := unit_sphere_euclidean_max_radial n
  exact e.toHomotopyEquiv.simplyConnectedSpace_iff

/-- The n-dimensional Euclidean and maximum-norm unit spheres are simply connected and locally
path-connected for n ≥ 2, and their radial homeomorphism has the stated forward and inverse maps.

Source: Hatcher, *Algebraic Topology*, Proposition 1.14 and Lemma 1.15, printed p.35
(literature/hatcher-at.pdf, PDF page44). Complete natural-language proof of
`topo.unit_sphere_simply_connected_g9`:

1. First use the Euclidean unit sphere Sⁿ⊂ℝⁿ⁺¹. It is path-connected by the sphere
path-connectedness theorem, since n+1>1 and radius1 is positive. Fix any basepoint b∈Sⁿ. Choose a
unit vector p orthogonal to b; a nonzero vector in that orthogonal subspace exists since n+1≥3.
Thus b differs from both p and −p. The two sets A₊=Sⁿ\{p} and A₋=Sⁿ\{−p} are open, cover Sⁿ, and
contain b. Stereographic projection identifies each with ℝⁿ, so each is contractible and simply
connected.

2. After an orthogonal change of Euclidean coordinates sending p to the last coordinate unit
vector, the intersection A₊∩A₋ consists of (v,t) with ||v||²+t²=1 and −1<t<1. The map
(v,t)↦(v/sqrt(1−t²),t) is a homeomorphism to Sⁿ⁻¹×(−1,1), with inverse (u,t)↦(sqrt(1−t²)u,t). The
denominators are strictly positive, and both formulas are continuous. Sⁿ⁻¹ is path-connected
because its ambient dimension is n≥2; the interval is path-connected by straight interpolation.
Thus the intersection is path-connected. No simple-connectedness of this intersection is required,
including n=2 where it is a cylinder over a circle.

3. For a loop γ at b pull this open cover back along γ and use the interval partition theorem to
obtain finitely many times 0=t₀≤⋯≤t_m=1 whose consecutive closed subpaths lie in a chosen
A_i∈{A₊,A₋}. Repeated times cause constant subpaths and are allowed. Each intermediate γ(t_i)
belongs to A_i∩A_{i+1}. Choose a path r_i from b to γ(t_i) inside that intersection by
path-connectedness; if the two chosen members coincide, use that member itself. Set r₀ and r_m to
the constant path at b. Each loop λ_i=r_{i−1}·γ|[t_{i−1},t_i]·r_i⁻¹ lies wholly in A_i and is
based at b.

4. Each λ_i is endpoint-fixed nullhomotopic in its punctured-sphere subtype, by
simple-connectedness there; postcompose with the inclusion to get an ambient endpoint-fixed
nullhomotopy. Concatenate these finitely many homotopies. In the concatenation of λ_i the inserted
consecutive reverse/forward paths r_i⁻¹·r_i cancel by the exact path-homotopy backtrack identity,
associativity aligns the factors, and the outer constant factors can be removed. The remaining
finite subpath concatenation is endpoint-homotopic to γ by the exact subdivision-concatenation
theorem. Consequently every loop at this arbitrary b is endpoint-fixed nullhomotopic.
Path-connectedness and the all-basepoints loop criterion imply SimplyConnectedSpace Sⁿ. This is
Hatcher Lemma1.15 and Proposition1.14 with the finite path manipulations written out.

5. Stereographic charts give an open Euclidean chart through every sphere point; the Euclidean
model is locally path-connected because its open balls are convex. The charted-space local
path-connectedness theorem therefore gives LocallyPathConnectedSpace Sⁿ. This is independent of
the global loop argument.

6. Now let S∞ be the actual maximum-norm unit sphere in Fin(n+1)→ℝ. The Euclidean and maximum-norm
topologies on the vector space are the same: ||v||∞≤||v||₂≤sqrt(n+1)||v||∞. The map R:Sⁿ→S∞,
R(v)=v/||v||∞, has inverse w↦w/||w||₂. Neither denominator vanishes because the source vector has
norm1. The formulas are continuous in the original finite-product/subspace topologies and compose
to the identity; thus R is a homeomorphism. Transport path-connectedness and each endpoint-fixed
loop nullhomotopy by R and its inverse, then use the same loop criterion. Transport local
path-connectedness by the homeomorphism theorem. This proves both asserted properties for the
exact maximum-norm sphere used by the classical CW characteristic disks.

The bound n ≥ 2 is essential: n=1 is the circle and is not simply connected; n=0 is two points.
The conclusion concerns both original sphere topologies and does not identify their two norms.
The homeomorphism witness is existential theorem data with both coordinate formulas specified;
there is no definition whose data is `sorry`.
-/
theorem unit_sphere_simply_connected (n : ℕ) (hn : 2 ≤ n) :
    SimplyConnectedSpace {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} ∧
    LocallyPathConnectedSpace {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} ∧
    SimplyConnectedSpace {w : Fin (n + 1) → ℝ // ‖w‖ = 1} ∧
    LocallyPathConnectedSpace {w : Fin (n + 1) → ℝ // ‖w‖ = 1} ∧
    ∃ e : {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} ≃ₜ
        {w : Fin (n + 1) → ℝ // ‖w‖ = 1},
      (∀ v, (e v).val = ‖WithLp.ofLp v.val‖⁻¹ • WithLp.ofLp v.val) ∧
      (∀ w, (e.symm w).val =
        ‖WithLp.toLp 2 w.val‖⁻¹ • WithLp.toLp 2 w.val) := by
  have hs : SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
    let p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp⟩
    apply sphere_simply_connected_of_two_sets {p}ᶜ {-p}ᶜ
      isOpen_compl_singleton isOpen_compl_singleton
      (sphere_puncture_simply_connected n p) (sphere_puncture_simply_connected n (-p))
      (sphere_two_punctures_path_connected n hn p (-p) (ne_neg_of_mem_unit_sphere ℝ p))
    ext x
    simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
    by_cases hx : x = p
    · exact Or.inr (hx ▸ ne_neg_of_mem_unit_sphere ℝ p)
    · exact Or.inl hx
  have hE : SimplyConnectedSpace
      {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} := by
    let h : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ₜ
        {v : EuclideanSpace ℝ (Fin (n + 1)) // ‖v‖ = 1} :=
      Homeomorph.setCongr (by ext v; exact mem_sphere_zero_iff_norm)
    exact h.symm.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨hElocal, hMlocal⟩ := unit_sphere_locally_path_connected n
  exact ⟨hE, hElocal, (unit_sphere_euclidean_max_simply_connected_iff n).mp hE,
    hMlocal, unit_sphere_euclidean_max_radial n⟩


end HolomorphicAnosov
