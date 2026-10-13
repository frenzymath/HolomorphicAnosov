import HolomorphicAnosov.Topology.CWRefinementFiniteFrontier
import HolomorphicAnosov.Topology.CWSkeletonCellComplement
import HolomorphicAnosov.Topology.CWSkeletonMovedDiskQuotient
import HolomorphicAnosov.Topology.CWFiniteDiskCoverClosedCriterion
import HolomorphicAnosov.Topology.CWPointVertexMappingConeReplacement
import HolomorphicAnosov.Topology.CWPointVertexPrismBoundaryFaces
import HolomorphicAnosov.Topology.CWPointVertexBoundarySmallerCell
import HolomorphicAnosov.Topology.CWVertexDiskHomeomorph
import HolomorphicAnosov.Topology.CWPointVertexPositiveCell
import HolomorphicAnosov.Topology.CubicalCharacteristicParameterG8
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Making an arbitrary point a vertex of a CW complex

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), Lemma 2.3.7, p.67.
-/

open _root_.Topology

universe u

namespace HolomorphicAnosov

/--
Any prescribed point becomes a vertex after a finite subdivision of the original Hausdorff
CW structure, on exactly its existing topology.

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), Lemma 2.3.7,
printed p.67; cellular adjunction and mapping cone, Theorem 2.3.1 and Example 3,
pp.62–63. The finite-replacement and unchanged-map clauses are properties of this
written induction. Subdivision of every original subcomplex is Proposition 2.3.6,
p.66: new open cells lie inside their assigned old open cells, so an old closed
union of cells remains a closed union of new cells.

The two CWComplex values use the SAME supplied TopologicalSpace X. Their PartialEquiv
targets are their open cells, by the source_eq field. The carrier function records
which original open cell is subdivided; each fibre is finite and the targets in it
have union that original cell. Outside the finite changed set the original
characteristic map is retained on its entire closed characteristic disk, not only
on its interior. All output data are literal Mathlib CWComplex/Set/PartialEquiv data;
no separate refinement predicate or additional CW hypothesis is assumed.

Complete natural-language proof:

1. Follow Fritsch–Piccinini Lemma 2.3.7, printed p.67, by induction on the finite dimension n of the
unique original open cell e containing x. The strengthened induction records finite replacements,
dimensions not increasing within any replaced original cell, unchanged original characteristic maps
outside those cells, and unchanged topology and skeleton spaces in dimensions at least n. For n=0
retain the given structure. In the inductive step work first in the original n-skeleton Kⁿ with its
inherited topology and characteristic maps; do not remove e from the entire K and call the result a
subcomplex, since higher cells may attach to e.

2. Let cₑ:Sⁿ⁻¹→Kⁿ⁻¹ be the attaching map of e. Give Sⁿ⁻¹ the minimal CW structure used on source
p.67: for n=1, S⁰ has two zero-cells; for n≥2, it has one zero-cell θ and one (n−1)-cell, and all
intervening skeleta are {θ}. This is the sphere structure of source §1.2 Example 1, printed
pp.23–24. Its characteristic disk for the positive-dimensional cell is the disk/boundary quotient
onto the sphere: inverse stereographic projection after u↦u/(1−‖u‖) on the open disk extends to the
constant θ on the boundary. The stereographic formula tends to θ as ‖u‖→1, and its inverse on the
punctured sphere is continuous. Thus this is a finite CW structure with its original sphere
topology, not a regularity assumption on K. The sphere has its usual Euclidean topology; radial norm
conversion transports these finite-dimensional disk charts to the max-norm model of the named CW
class.

3. For n≥2 apply the induction hypothesis to z=cₑ(θ), whose carrier has dimension strictly below n,
refining only lower-dimensional cells and making z a vertex. The given map cₑ is still continuous,
since this refinement preserves the topology. It is now cellular from the minimal sphere: its zero
and intervening skeleta map to z, and its whole (n−1)-skeleton maps into Kⁿ⁻¹. For n=1 both points
of S⁰ already map to original vertices, so no preliminary refinement is needed. The open e and every
other original n-cell and its characteristic map survive the preliminary refinement. Write A=Kⁿ\e
with this refined structure. Within Kⁿ, all selected cells other than e have their closed cells in
A: other n-cell boundaries and all lower-cell boundaries lie below dimension n. The selected-cell
union is therefore a closed subcomplex with the inherited topology and maps. No such assertion is
made about K\e.

4. Use the source mapping cone C(c), where c:Sⁿ⁻¹→A is cₑ followed by inclusion. Explicitly it is
the quotient of A ⨿ (Sⁿ⁻¹×[0,1]), identifying (s,0) with c(s) and identifying the whole top Sⁿ⁻¹×{1}
to a new point v. Expand Theorem 2.3.1 and Example 3, printed pp.62–63, in this special finite-
source case: keep the cells of A, add v as a zero-cell, and for every d-cell b of the minimal sphere
add the open prism b×(0,1) as a (d+1)-cell. The cone quotient identifies no two points in these open
prisms or in A. Each prism interior has the product topology, since the cylinder interior is an open
saturated subset of the raw quotient domain and is homeomorphic to its quotient image. In the next
step the cone is identified with Hausdorff Kⁿ, and its restriction to A is the identity, giving the
unchanged topology and charts of A as well.

5. Here is the homeomorphism asserted in the written Lemma 2.3.7 proof, with its elementary disk
choice made explicit. The ordinary cone on Sⁿ⁻¹ is a closed n-ball; write its points as r s, with
r=1 on the base and r=0 at the peak. If a is the original interior disk representative of x, the map
h(r s)=(1−r)a+r s is a self-homeomorphism of the closed Euclidean n-ball, fixes every boundary point
s, and carries the peak to a. Every ray from the interior point a has a unique boundary
intersection, so the segment parameter and boundary direction give the continuous inverse; at a the
segment parameter tends to zero. On A take the identity and on the cone take φₑ∘h, where φₑ is the
original characteristic map. At the base these maps agree with cₑ, so the quotient universal
property gives a continuous bijection T:C(c)→Kⁿ. Its inverse is continuous, not merely assumed from
bijectivity: the original characteristic quotient onto Kⁿ consists of A and the old disk of e, and
the proposed inverse pulls back continuously to the identity on A and the disk homeomorphism into
the cone quotient. The original closed-cell criterion and compact-to-Hausdorff quotient fact supply
this characteristic quotient. Thus T is the source homeomorphism, is the identity on A, and has
T(v)=x. Arbitrary identifications of the old attaching sphere are exactly the base equivalence
relation of C(c); no boundary injectivity is needed.

6. Verify the characteristic maps in the cellular-adjunction proof, rather than taking a mapping-
cone CW theorem as an elementary assertion. For a sphere d-cell with characteristic disk β:Dᵈ→Sⁿ⁻¹,
its prism characteristic map is (u,t)↦[β(u),t]. The named cubical parameter identifies Dᵈ×[0,1] with
the closed (d+1)-disk, interior with int(Dᵈ)×(0,1), and boundary with bottom, top and sides. The
bottom maps by cβ to Aᵈ because c is cellular, the top maps to v, and the sides map to prisms over
lower sphere cells and their bases. Hence all boundary values lie in cells of dimension strictly
below d+1. Forward continuity follows from the quotient and product maps; the interior inverse is
continuous by the open saturated interior chart. The cells of A and all the prism interiors and v
partition the cone. Under T these become characteristic maps on the original Kⁿ. This is the
attaching-cell part of Theorem 2.3.1 pp.62–63 specialized to the cone; it includes d=0, when the
lateral boundary is empty.

7. The final-topology part of Theorem 2.3.1, printed p.63, also applies on the original quotient
carrier. The coproduct of the characteristic disks of A is quotient onto A by the closed-cell test
and compactness of each disk; the same holds for the finite sphere characteristic family.
Multiplying the sphere characteristic quotient by the locally compact interval is quotient, by the
named product-descent result. Therefore a subset of the raw cylinder has closed preimage under every
prism characteristic disk exactly when it is closed in the cylinder. Testing the A disks and all
prism disks, and then the defining cone quotient, proves that a subset of C(c) is closed precisely
when all its characteristic-disk preimages are closed. This is the written source universal-property
argument for final topology, with the cylinder quotient spelled out. Transport by T gives the
original topology on Kⁿ. This argument allows arbitrarily many cells in A; it asserts no equality of
ordinary and CW product topologies for two arbitrary infinite CW spaces.

8. The finite-source cone also gives exactly the stronger finite-replacement clause. For n=1 the two
sphere vertices give two new one-cells and the peak gives x; the endpoints cₑ(S⁰) may coincide. For
n≥2 the sphere vertex gives one new one-cell, its (n−1)-cell gives one new n-cell, and the peak
gives x. All these new open cells lie inside the old open e, with dimensions at most n. Outside e, T
is the identity and retains the characteristic maps of A; the preliminary induction modified only
finitely many original lower cells, each into a finite family. Consequently the total number of
replaced original cells and of cells replacing any one of them is finite. This is a direct property
of the written induction and cone construction, not an additional published theorem or a new
alternative construction. Every cell boundary still has finite lower support: in the cone the sphere
has finitely many cells and every bottom characteristic image is compact in A, hence has finite cell
support by source Proposition 1.5.2 p.40; equivalently the bottom lies in the finite refined support
of the old attaching frontier. Old frontier finite-open covers remain finite after replacing their
finitely many selected cells by finite families.

9. Retain every original characteristic map for cells of dimension above n and every unreplaced cell
of dimension at most n. This is the extension implicit in source Lemma 2.3.7, whose skeleton spaces
Kᵐ for m≥n stay unchanged, and the source discussion before Proposition 2.3.3, printed p.65. Since
lower replacements never increase dimension, every old higher attaching sphere still lies in the
appropriate lower skeleton, and continuity is unchanged on the same space. Its finite frontier
support remains finite by the finite replacement property just proved. Its open-cell interior and
inverse are literally the original ones. Thus no new characteristic map or changed boundary value is
imposed on an unreplaced higher cell, even when its attaching map meets e.

10. Finally check the weak topology for the full possibly infinite K, using the source closed-cell
criterion (Proposition 1.2.2 pp.23–24) rather than imposing a topology on a new carrier. All new
characteristic maps into K are continuous in its original topology. If a subset B has closed
pullback under every new characteristic disk, its intersection with each new closed-cell image is
compact, hence closed in the original Hausdorff K. Each replaced old closed cell is covered by the
finitely many new closed-cell images within it: the cone prism images include their bases, which
cover the old attaching image, and their interiors and peak cover the old open cell; the preliminary
recursive replacements have the same covering property. Thus B intersects each replaced old closed
cell in a finite union of original-topology closed sets, and intersects each unreplaced old closed
cell in an original-topology closed set. The original CW closed-cell test makes B closed in K.
Conversely an originally closed B has closed pullback under every continuous new characteristic map.
Together with the partition, inverse continuity, finite lower-dimensional boundary covers and
unchanged union, these verify all fields of the named CW class on the original topology. This is the
global weak-topology extension of the source cellular-adjunction proof; it uses no global
finiteness.

11. The recursive carrier dimension decreases strictly, so the strengthened construction terminates
in finitely many stages. The result makes x a zero-cell on precisely the original topological K and
satisfies all finite and unchanged-map clauses of the statement. A chosen x excludes empty K; an
existing vertex requires no change; loop edges, disconnected spaces, arbitrarily large cell families
and unbounded dimensions are allowed. The construction uses arbitrary attaching maps, not regular CW
cells or a triangulation. The source proof has therefore been expanded without connectedness, local
finiteness, finite-dimensionality or regularity assumptions.
-/
theorem cw_point_vertex_refinement
    (X : Type u) [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X)) (x : X) :
    let oldCell := @CWComplex.cell X _ Set.univ old
    let oldMap := @CWComplex.map X _ Set.univ old
    ∃ new : CWComplex (Set.univ : Set X),
      let newCell := @CWComplex.cell X _ Set.univ new
      let newMap := @CWComplex.map X _ Set.univ new
      ∃ (changed : Set (Σ n, oldCell n))
        (carrier : (Σ n, newCell n) → (Σ n, oldCell n)),
        changed.Finite ∧
        (∃ i : newCell 0, (newMap 0 i).target = {x}) ∧
        (∀ e : Σ n, newCell n,
          e.1 ≤ (carrier e).1 ∧
          (newMap e.1 e.2).target ⊆ (oldMap (carrier e).1 (carrier e).2).target) ∧
        (∀ e : Σ n, oldCell n,
          (oldMap e.1 e.2).target =
            ⋃ (f : Σ n, newCell n) (_ : carrier f = e), (newMap f.1 f.2).target) ∧
        (∀ e : Σ n, oldCell n, Set.Finite {f : Σ n, newCell n | carrier f = e}) ∧
        (∀ (n : ℕ) (i : oldCell n), (⟨n, i⟩ : Σ n, oldCell n) ∉ changed →
          ∃ j : newCell n, carrier ⟨n, j⟩ = ⟨n, i⟩ ∧
            Set.EqOn (newMap n j) (oldMap n i)
              (Metric.closedBall (0 : Fin n → ℝ) 1)) := by
  classical
  by_cases hx : ∃ i : @CWComplex.cell X _ Set.univ old 0,
      (@CWComplex.map X _ Set.univ old 0 i).target = {x}
  · dsimp only
    refine ⟨old, ∅, id, Set.finite_empty, hx, ?_, ?_, ?_, ?_⟩
    · intro e
      exact ⟨le_rfl, Set.Subset.rfl⟩
    · intro e
      ext y
      simp only [Set.mem_iUnion, id_eq]
      constructor
      · intro hy
        exact ⟨e, rfl, hy⟩
      · rintro ⟨f, hfe, hy⟩
        subst f
        exact hy
    · intro e
      simpa only [id_eq, Set.ofPred_eq_eq_singleton] using Set.finite_singleton e
    · intro n i hi
      exact ⟨i, rfl, Set.eqOn_refl _ _⟩
  · obtain ⟨n, hn, i, a, ha, hax⟩ :=
      cw_point_vertex_refinement_positive_cell X old x hx
    have haInterior : ‖a‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using ha
    obtain ⟨diskMove, hmove, hpeak, hboundary⟩ :=
      cw_vertex_disk_homeomorph a haInterior
    let : CWComplex (Set.univ : Set X) := old
    let movedCharacteristic : C(Metric.closedBall (0 : Fin n → ℝ) 1, X) :=
      ⟨fun z ↦ (@CWComplex.map X _ Set.univ old n i) (diskMove z).val,
        (@CWComplex.continuousOn X _ Set.univ old n i).domRestrict.comp
          diskMove.continuous⟩
    have hmovedPeak : movedCharacteristic ⟨0, by simp⟩ = x := by
      change (@CWComplex.map X _ Set.univ old n i) (diskMove ⟨0, by simp⟩).val = x
      rw [hpeak]
      exact hax
    have hmovedBoundary (z : Metric.closedBall (0 : Fin n → ℝ) 1)
        (hz : z.val ∈ Metric.sphere (0 : Fin n → ℝ) 1) :
        movedCharacteristic z = (@CWComplex.map X _ Set.univ old n i) z.val := by
      have hzNorm : ‖z.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      change (@CWComplex.map X _ Set.univ old n i) (diskMove z).val = _
      rw [hboundary z hzNorm]
    have hmoveInterior (z : Metric.closedBall (0 : Fin n → ℝ) 1) :
        (diskMove z).val ∈ Metric.ball (0 : Fin n → ℝ) 1 ↔
          z.val ∈ Metric.ball (0 : Fin n → ℝ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right]
      have hzle : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      have hHzle : ‖(diskMove z).val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (diskMove z).property
      constructor
      · intro hHz
        by_contra hz
        have hzEq : ‖z.val‖ = 1 := le_antisymm hzle (le_of_not_gt hz)
        rw [hboundary z hzEq] at hHz
        exact (ne_of_lt hHz) hzEq
      · intro hz
        by_contra hHz
        have hHzEq : ‖(diskMove z).val‖ = 1 := le_antisymm hHzle (le_of_not_gt hHz)
        have hfix := diskMove.injective (hboundary (diskMove z) hHzEq)
        rw [hfix] at hHzEq
        exact (ne_of_lt hz) hHzEq
    have hmovedOpen : movedCharacteristic ''
        {z : Metric.closedBall (0 : Fin n → ℝ) 1 |
          z.val ∈ Metric.ball (0 : Fin n → ℝ) 1} =
        (@CWComplex.map X _ Set.univ old n i).target := by
      rw [← PartialEquiv.image_source_eq_target, @CWComplex.source_eq X _ Set.univ old]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(diskMove z).val, (hmoveInterior z).mpr hz, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        let w : Metric.closedBall (0 : Fin n → ℝ) 1 :=
          ⟨v, Metric.ball_subset_closedBall hv⟩
        refine ⟨diskMove.symm w, ?_, ?_⟩
        · apply (hmoveInterior _).mp
          simpa only [Homeomorph.apply_symm_apply] using hv
        · change (@CWComplex.map X _ Set.univ old n i)
            (diskMove (diskMove.symm w)).val = _
          rw [Homeomorph.apply_symm_apply]
    obtain ⟨A, hA⟩ := cw_skeleton_cell_complement (C := (Set.univ : Set X)) n i
    have hattach : Set.MapsTo (@CWComplex.map X _ Set.univ old n i)
        (Metric.sphere (0 : Fin n → ℝ) 1) (A : Set X) := by
      intro v hv
      rw [hA]
      have hf : (@CWComplex.map X _ Set.univ old n i) v ∈
          CWComplex.cellFrontier (C := (Set.univ : Set X)) n i := ⟨v, hv, rfl⟩
      have hlow := CWComplex.cellFrontier_subset_skeletonLT (C := (Set.univ : Set X)) n i hf
      exact ⟨(CWComplex.skeletonLT_mono (show (n : ℕ∞) ≤ n + 1 from le_self_add)) hlow,
        (CWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
          (j := i) le_rfl).notMem_of_mem_left hlow⟩
    let theta : Fin n → ℝ := Pi.single ⟨0, hn⟩ 1
    have htheta : theta ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      simp [theta, Pi.norm_single]
    obtain ⟨m, hm, j, b, hb, hbj⟩ :=
      cw_point_vertex_refinement_boundary_smaller_cell X old i theta htheta
    obtain ⟨movedQuotient, hmovedQuotient, hquotient⟩ :=
      cw_skeleton_moved_disk_quotient n i A hA diskMove
    -- The chosen attaching value has carrier dimension m<n, enabling the
    -- preliminary induction that makes this attaching value a vertex.
    -- The peak can now be moved to a without changing any boundary value.
    -- Construct the finite mapping-cone CW replacement and extend the
    -- unchanged higher-dimensional characteristic maps.
    have hA' : let _ : CWComplex (Set.univ : Set X) := old
        (A : Set X) = (CWComplex.skeleton (Set.univ : Set X) n : Set X) \
          (@CWComplex.map X _ Set.univ old n i).target := by
      rw [← (@CWComplex.map X _ Set.univ old n i).image_source_eq_target]
      rw [@CWComplex.source_eq X _ Set.univ old n i]
      exact hA
    have hcone := cw_point_vertex_mapping_cone_replacement X old i x a ha hax A hA' diskMove hattach
    -- The helper's package has the exact target shape; applying it exposes
    -- the remaining source construction without changing the parent statement.
    exact hcone

end HolomorphicAnosov

