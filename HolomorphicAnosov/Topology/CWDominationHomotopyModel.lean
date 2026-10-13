import HolomorphicAnosov.Topology.CWComplex.CellularApproximation
import HolomorphicAnosov.Topology.CellularMappingTelescopeCW
import HolomorphicAnosov.Topology.CWCellularTelescopeModel
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeHomotopyComparisons
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import HolomorphicAnosov.AlternatingTelescopeDomination
import HolomorphicAnosov.Topology.CWComplexULift
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Equiv

/-!
# A CW homotopy model from topological domination

This interface retains the closed connected smooth manifold in the public statement, while
the proof uses only its topological domination by the supplied connected Hausdorff CW complex.
All CW structures, continuous maps and homotopies are Mathlib's actual objects.
-/

open scoped Manifold ContDiff

namespace HolomorphicAnosov

universe u v

/-- A nonempty closed connected smooth real manifold dominated by a nonempty connected
Hausdorff CW complex has a genuine nonempty connected Hausdorff CW homotopy model.

Source: Hatcher, *Algebraic Topology*, Proposition A.11, pp.528–529, and Corollary A.12,
p.529; cellular approximation, Theorem4.8, p.349; homotopic attaching maps, Proposition0.18,
p.16. DAG node: `topo.cw_domination_homotopy_model`.

The fixed Euclidean atlas, smoothness, compactness, Hausdorffness and second countability
express the given closed smooth real n-manifold without boundary. `ConnectedSpace` includes
nonemptiness. The model is the whole Euclidean space, so the canonical model with corners
has empty boundary. The number n is a natural number, including0. No finiteness condition is
imposed on either CW complex. `H` is an actual jointly continuous interval homotopy with the
specified endpoint maps. The output `HomotopyEquiv` contains both continuous maps and both
jointly continuous inverse homotopies; it is not a condition on homotopy groups or homology.
The existentially chosen topology is the topology used by every output CW and map structure.

Natural-language proof: Put a=j∘q:P→P. Form the quotient-cylinder telescope of the alternating
sequence P --q→ M --j→ P --q→ M --j→ ... . Pair successive cylinders to obtain the telescope
of a,a,... . Delete the first cylinder in the alternating telescope, then pair its cylinders;
this gives the telescope of q∘j,q∘j,... . Each operation is a genuine homotopy equivalence.
For deletion, retract the initial mapping cylinder onto its target level. For pairing, slide
the attaching end of the first cylinder down the second mapping cylinder, then retract the
extra second mapping cylinder onto its target. These maps and inverse homotopies agree on
the identified level copies, so descend continuously through the quotient; the same homotopies
on successive strips paste continuously on the telescope. This is Hatcher's A.11 comparison.

Use H on every M-level to replace q∘j by id_M. The homotopic-bond comparison is obtained by
varying the cylinder attaching maps along H, using the homotopic-attachment equivalence of
Proposition0.18. The cylinder endpoint pair has the required deformation retraction for that
argument, without a CW assumption on M. The resulting telescope is the identity telescope,
homeomorphic to M×[0,∞): the quotient maps on adjacent closed strips agree at their common
endpoints, and their inverses paste on the locally finite strips. Contracting the nonnegative
time coordinate gives its homotopy equivalence with M. Thus Tel(a) is homotopy equivalent to M.

Apply cellular approximation to a:P→P with empty relative subcomplex. It gives a continuous
cellular c:P→P and an actual homotopy a≃c. Homotopic-bond comparison gives Tel(a)≃Tel(c).
The cellular telescope K=Tel(c) has its Hausdorff CW structure in the original quotient
topology: retain each level cell and add the open prism over every cell, of dimension one
higher. The cellular attaching maps land in the required lower skeleton. Closure finiteness
comes from that of each level and the finite compact-image cell condition; the weak topology
is exactly the cylinder quotient topology. Every level and joining mapping cylinder is
connected and nonempty, since P is. Their increasing unions therefore make K connected and
nonempty. No finite-cell or finite-dimensional conclusion follows or is asserted.

Compose the equivalences to obtain e:M≃Tel(a) and d:Tel(a)≃K. Take u=d∘e and
v=e⁻¹∘d⁻¹. Whisker the inverse homotopy d⁻¹d≃id by e⁻¹ and e, then concatenate with
e⁻¹e≃id_M; this gives vu≃id_M. Similarly whisker ee⁻¹≃id by d and d⁻¹ and concatenate
with dd⁻¹≃id_K to obtain uv≃id_K. Mathlib's `HomotopyEquiv` packages exactly these data.
Dimension0, constant bonding maps, and infinitely many cells cause no change in the argument.

This is Stage2 statement formalization; the named proof is intentionally admitted.
-/
theorem cw_domination_homotopy_model
    (n : ℕ) (M : Type u)
    [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (P : Type v) [TopologicalSpace P] [T2Space P] [ConnectedSpace P]
    [Topology.CWComplex (Set.univ : Set P)]
    (j : C(M, P)) (q : C(P, M))
    (H : ContinuousMap.Homotopy (q.comp j) (ContinuousMap.id M)) :
    ∃ (K : Type (max u v)) (t : TopologicalSpace K),
      letI := t
      T2Space K ∧ ConnectedSpace K ∧
        Nonempty (Topology.CWComplex (Set.univ : Set K)) ∧
        Nonempty (ContinuousMap.HomotopyEquiv M K) := by
  obtain ⟨c, hc, hhom, hT2, hCW, hconn, d⟩ := cellular_telescope_model P (j.comp q)
  obtain ⟨e⟩ := domination_telescope_homotopy_equiv M P j q H
  let K₀ := MappingTelescope.Sequence.telescope (fun _ : ℕ ↦ c)
  let : T2Space K₀ := hT2
  let : ConnectedSpace K₀ := hconn
  let : Topology.CWComplex (Set.univ : Set K₀) := hCW.some
  let K := ULift.{u} K₀
  refine ⟨K, inferInstance, inferInstance, ?_, cwComplex_ulift K₀, ?_⟩
  · exact Homeomorph.ulift.symm.surjective.connectedSpace
      Homeomorph.ulift.symm.continuous
  · exact ⟨(e.symm.trans d.some).trans Homeomorph.ulift.symm.toHomotopyEquiv⟩


end HolomorphicAnosov
