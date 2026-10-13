import HolomorphicAnosov.Topology.DyadicCubesShrinkAt
import HolomorphicAnosov.Topology.HatcherDyadicComplementShrinkingCWConstruction
import HolomorphicAnosov.Topology.ClosedFamilyShrinksAt
import Mathlib.Data.Fintype.Pi
import HolomorphicAnosov.Topology.ClosedComplementDyadicCubeCover
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.LocallyFinite

/-!
# Shrinking dyadic CW cells on a Euclidean compact-set complement

Source: Hatcher, Algebraic Topology, proof of Theorem A.7, printed pp. 525–526.
The native CW structure lives on the original Euclidean complement subtype.
DAG node: `topo.hatcher_dyadic_complement_shrinking_cw_g7`.
-/

namespace HolomorphicAnosov

open Set Topology _root_.Topology

/-- A compact-set complement has a locally finite regular coordinate-box CW structure
whose cells shrink towards every point of the removed compact set.

The ambient Euclidean metric and original complement topology remain fixed. Local finiteness
ranges over the full dependent family of closed cells in all dimensions. Each cell has dimension
at most `N`, and its coordinate box lies in a closed level-`k` dyadic cube disjoint from `C`.
The free-coordinate embedding identifies its dimension; all other coordinate intervals degenerate
to a point. The displayed affine equations describe the SAME native characteristic map on its
closed maximum-norm disk. Its closed-disk restriction is a homeomorphism onto the closed cell,
which expresses regularity without assuming a separate regular-CW predicate. The open-cell
formula is the box's relative interior, including its fixed coordinates. The characteristic sphere
image is exactly a finite union of lower-dimensional closed cells. Shrinking uses ambient
Euclidean balls at the removed points. Empty `C` and zero-dimensional cells are included;
only the ambient dimension is assumed positive, as in the node.

Source: Hatcher, Algebraic Topology, proof of Theorem A.7, printed pp. 525–526,
literature/hatcher-at.pdf (PDF pp. 534–535) and literature/hatcher-at.txt.
The coordinate verification of the source's minimal-face assertion is expanded in the DAG proof.

Complete natural-language proof of `topo.hatcher_dyadic_complement_shrinking_cw_g7`:
1. Compactness makes C closed. For k≥0 and m∈ℤ^N write Q(k,m)=∏j[2^(−k)mj,2^(−k)(mj+1)]. Select the
level-zero cubes disjoint from C, then at level k select precisely those disjoint from C not
contained in an earlier selected cube. Each dyadic cube has one containing ancestor at every
earlier level. A cube disjoint from C is therefore selected or lies in an earlier selected
ancestor. For x∉C choose a ball B(x,r) disjoint from C and k with √N·2^(−k)<r; a level-k cube
through x lies in the ball. The selected cubes consequently cover X. Two selected cubes have
disjoint interiors, since dyadic cubes with intersecting interiors are nested; a strictly smaller
selected cube cannot lie in a larger selected cube. These facts also handle C=∅, in which case
only unit cubes are selected.

2. To prove local finiteness at x∈X, choose an ambient ball B(x,a) disjoint from C and then K such
that every level-K cube meeting B(x,a/4) is contained in B(x,a). If a selected cube of level k>K
meets B(x,a/4), its level-K ancestor also meets this ball, is disjoint from C, and therefore is
selected or lies in an earlier selected ancestor. That would exclude the level-k cube. Only
levels 0,…,K can meet B(x,a/4), and only finitely many grid cubes at these levels do so. Each
selected cube is a compact coordinate box, so it meets only finitely many other selected cubes by
local finiteness on X.

3. For a fixed c∈C, finitely many selected cubes of side at least η>0 meet B(c,1): there are
finitely many relevant levels and finitely many grid positions at each. These are closed and do
not contain c; some neighborhood of c avoids all of them. The diameters of the remaining cubes
are less than √N·η. Given ε>0 choose η with √N·η<ε/2, and δ<ε/2 small enough to avoid the
finitely many larger cubes. Then every selected cube meeting B(c,δ) lies in B(c,ε). Any closed
cell contained in such a cube inherits this property.

4. For a dyadic closed cube, an open face means the product of either an endpoint singleton or the
strict interval in each coordinate; include the full interior and vertices. Identify repeated
open faces as the same subset. Two such open faces that intersect are nested as subsets. To check
this, take the smaller side length, divide each coordinate by it, and note that all coarse
endpoints are integer multiples of the coarse/fine scale ratio. Two strict grid intervals with an
intersection are either equal or the fine interval lies inside the coarse strict interval. A fine
strict interval cannot contain a coarse grid endpoint; an intersecting coarse endpoint coordinate
must therefore be a fine endpoint singleton. The remaining singleton/interval cases give
containment coordinate by coordinate. Equal scales force equal open faces whenever they
intersect. These elementary integer-coordinate checks apply to all dimensions including zero.

5. Fix x∈X. Only finitely many selected closed cubes contain x, by local finiteness. Choose one Q
with the smallest side length among them, and let F be its unique relative open face containing
x. Claim F is minimal under inclusion among all selected-cube open faces. Suppose a proper
selected-cube open face G⊊F exists, belonging to R. The preceding grid calculation makes R
strictly smaller than Q: at Q scale no proper intersecting open-face containment is possible, and
coarser grid coordinates cannot form a proper open face inside F. Let P be the ancestor of R at Q
scale. Since G⊂F, P has the same coordinate intervals as Q on every free coordinate of F, and on
fixed coordinates its intervals end at the fixed value of F. Hence the entire closed face F̄⊂P,
in particular x∈P. Since R is selected, neither P nor any earlier ancestor of P is selected.
Every selected cube covering a point in int(P) must therefore be strictly smaller than Q and
contained in P: a same-scale cube is P, and an intersecting coarser cube is an ancestor, both
impossible. Approach x through int(P). Local finiteness near x supplies finitely many selected
cubes covering this sequence. One occurs infinitely often and, being closed, contains its limit
x. It is strictly smaller than Q, contradicting the choice of Q. Thus F is a global minimal open
face. The sequence argument is elementary: distance from x to each of finitely many closed cubes
not containing x is positive; a sufficiently close sequence point avoids their finite union.

6. Every x therefore lies in a minimal open face. Minimal open faces are pairwise disjoint, because
an intersection forces inclusion and minimality forces equality. They partition X. A minimal face
e is the relative open face of a selected cube, so its closure is its corresponding closed
coordinate face and is contained in X. For x in the boundary of ē, let H be the proper open face
of the same cube containing x; dim H<dim e. The minimal face through x intersects H, so by
nesting it is contained in H: the opposite proper containment would violate its minimality. Thus
the boundary of each cell closure is a union of lower-dimensional minimal open faces. A minimal
face meets a selected cube Q only if its own selected cube meets Q. Compactness of Q and local
finiteness of selected cubes imply that only finitely many cubes, hence finitely many original
faces, meet Q. Therefore the boundary is covered by finitely many lower-dimensional minimal faces
and by their closures; these closures remain inside ē. The latter containment follows from the
same coordinate inclusions. Every selected cube consequently contains finitely many minimal faces
and is their union, with no assumption that every original face itself is a cell.

7. Once that finite face partition is established, for an m-dimensional chosen closed face enumerate
its free coordinates, write their intervals as [a_j,b_j] with b_j>a_j, and map u∈[-1,1]^m to
fixed coordinates on the other axes and to (a_j+b_j)/2+(b_j-a_j)u_j/2 on the free axes. Its
inverse is coordinatewise affine. This gives the characteristic map and the inverse on the open
face; the max-norm sphere is exactly the union of coordinate boundary faces. These formulas
include m=0, where the closed ball is a point and the attaching sphere is empty.

8. The minimal closed-face family is locally finite. Near any x only finitely many selected cubes
meet a suitable neighborhood, and each has finitely many original faces; every chosen closed cell
is one of these faces. Each closed cell is compact and therefore closed in Hausdorff X. If A⊂X
intersects every closed cell in a relatively closed set, these intersections are closed in X;
local finiteness and the locally finite closed-union theorem imply that their union A is closed
in X. Conversely a closed A has closed intersections with every closed cell. The cell partition,
affine characteristic maps, finite attaching-boundary cover, and this weak-topology criterion
give the CW structure through the fields of mathlib.cw_complex_structure_g8 with X carrying its
unchanged Euclidean subspace topology. Characteristic maps are homeomorphisms on closed cells, so
the structure is regular. Cell dimensions are ≤N. Finally each closed cell is contained in a
selected cube; the cube-shrinking estimate already proved in step 3 implies exactly the asserted
cell-shrinking property. There are countably many cells: every original face is specified by a
level k∈ℕ, an integer N-tuple m, and one of the 3^N choices of singleton endpoint or strict
interval in each coordinate. Identifying equal face subsets and restricting to minimal faces
preserves countability. This includes all positive-dimensional cells, without treating only
vertices.
-/
theorem hatcher_dyadic_complement_shrinking_cw :
    ∀ (N : ℕ) (_hN : 0 < N) (C : Set (EuclideanSpace ℝ (Fin N))) (_hC : IsCompact C),
    let X := {x : EuclideanSpace ℝ (Fin N) // x ∉ C}
    ∃ cw : CWComplex (univ : Set X),
      letI : CWComplex (univ : Set X) := cw
      LocallyFinite (fun j : Σ d : ℕ, RelCWComplex.cell (univ : Set X) d ↦
        RelCWComplex.closedCell (C := (univ : Set X)) j.1 j.2) ∧
      (∀ (d : ℕ) (_i : RelCWComplex.cell (univ : Set X) d), d ≤ N) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        ∃ (k : ℕ) (m : Fin N → ℤ) (e : Fin d ↪ Fin N) (a b : Fin N → ℝ),
          Disjoint {x : EuclideanSpace ℝ (Fin N) | ∀ j,
            (m j : ℝ) / (2 : ℝ) ^ k ≤ x j ∧
              x j ≤ ((m j : ℝ) + 1) / (2 : ℝ) ^ k} C ∧
          (∀ j, (m j : ℝ) / (2 : ℝ) ^ k ≤ a j ∧ a j ≤ b j ∧
            b j ≤ ((m j : ℝ) + 1) / (2 : ℝ) ^ k ∧
            (a j < b j ↔ j ∈ Set.range e)) ∧
          RelCWComplex.closedCell (C := (univ : Set X)) d i =
            {x : X | ∀ j, a j ≤ x.val j ∧ x.val j ≤ b j} ∧
          RelCWComplex.openCell (C := (univ : Set X)) d i =
            {x : X | (∀ j : Fin d, a (e j) < x.val (e j) ∧ x.val (e j) < b (e j)) ∧
              ∀ j : Fin N, j ∉ Set.range e → x.val j = a j} ∧
          (∀ u : Fin d → ℝ, u ∈ Metric.closedBall 0 1 →
            (∀ j : Fin d,
              (RelCWComplex.map (C := (univ : Set X)) d i u).val (e j) =
                (a (e j) + b (e j)) / 2 + (b (e j) - a (e j)) * u j / 2) ∧
            (∀ j : Fin N, j ∉ Set.range e →
              (RelCWComplex.map (C := (univ : Set X)) d i u).val j = a j))) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        ∃ h : ↥(Metric.closedBall (0 : Fin d → ℝ) 1) ≃ₜ
            ↥(RelCWComplex.closedCell (C := (univ : Set X)) d i),
          ∀ u : ↥(Metric.closedBall (0 : Fin d → ℝ) 1),
            (h u).val = RelCWComplex.map (C := (univ : Set X)) d i u.val) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        ∃ F : Finset (Σ n : ℕ, RelCWComplex.cell (univ : Set X) n),
          (∀ j : Σ n : ℕ, RelCWComplex.cell (univ : Set X) n, j ∈ F → j.1 < d) ∧
          RelCWComplex.cellFrontier (C := (univ : Set X)) d i =
            ⋃ j ∈ F, RelCWComplex.closedCell (C := (univ : Set X)) j.1 j.2) ∧
      (∀ c ∈ C, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
          (∃ x : X, x ∈ RelCWComplex.closedCell (C := (univ : Set X)) d i ∧
            dist x.val c < δ) →
          ∀ x : X, x ∈ RelCWComplex.closedCell (C := (univ : Set X)) d i →
            dist x.val c < ε)  := by
  intro N hN C hC
  simpa using hatcher_dyadic_complement_shrinking_cw_construction N hN C hC Set.Subset.rfl

end HolomorphicAnosov
