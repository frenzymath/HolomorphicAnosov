import HolomorphicAnosov.Topology.CWComplex.NeighborhoodDyadicSchedule
import HolomorphicAnosov.Topology.CWComplex.SkeletalNeighborhoodSuccessor
import HolomorphicAnosov.Topology.CWComplex.OpenSubcomplexPrismContinuity
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.PartialHomeomorph.Basic
import HolomorphicAnosov.Topology.ContractibleNeighborhoodBasis
import HolomorphicAnosov.Topology.ContractibleLoop

/-!
# Contractible open neighborhoods in arbitrary Hausdorff CW complexes

DAG node: `topo.cw_contractible_open_neighborhoods`.
Source: Hatcher, *Algebraic Topology*, Appendix Proposition A.4 p.522,
local path-connectivity and homotopy-continuity discussion p.523,
and characteristic quotient/weak topology pp.519–521.

The whole-space CW structure uses the existing topology. Contractibility below
is in the neighborhood's own subtype topology. Semilocal simple connectivity is
written as its based-loop condition; it does not assert that the entire CW
complex is simply connected. No finiteness, dimension or local-finiteness
hypothesis is imposed.
-/



namespace HolomorphicAnosov

universe u

/-- Arbitrarily small open contractible neighborhoods in a Hausdorff CW complex,
with the local path-connectivity, semilocal simple-connectivity, and
connected-nonempty-to-path-connected consequences.

Source: Hatcher Appendix Proposition A.4 p.522 and the discussion p.523;
CW characteristic maps and weak topology pp.519–521. Complete natural-language
proof from the DAG:

1. Write X^n for the actual subcomplex carrier skeletonLT(univ X,n+1), and X^(−1)=∅. The
selected-index and subcomplex-structure leaves make every X^n closed in the given Hausdorff X;
the subcomplex cell-map reindexing leaf supplies its inherited CW structure on that SAME ambient
X, with precisely the original maps of cells of dimensions at most n. Closedness of X^n
identifies closed sets in its subtype with ambient closed subsets contained in X^n. Thus the
closed-cell CW criterion restricts to the original skeletal topology; we do not posit a new
CWComplex univ instance on a silently changed carrier.  Fix the native characteristic interface
used throughout. For every original d-cell e, let D_d be the subtype of closedBall(0:Fin
d→Real,1) in the native MAXIMUM norm, and let C_e be its actual closed-cell image, with the
induced Hausdorff topology. Finite-dimensionality of this actual finite-coordinate real module
and the proper-space leaf give compactness of its closed ball; isCompact_iff_compactSpace gives
CompactSpace D_d, including d=0. The characteristic partial-equivalence map is only ContinuousOn
that closed ball. continuousOn_iff_continuous_domRestrict gives continuity on D_d, and the
closed-cell-image identity gives both membership in C_e and surjectivity onto it.
continuous_subtype_mk binds the codomain restriction. The compact-Hausdorff surjection leaf
therefore makes q_e:D_d→C_e a quotient map. Closed cells themselves are compact and hence closed
in Hausdorff X. No map continuity outside D_d, boundary injectivity, regular-cell identification
C_e=D_d, or finiteness of the cell family is assumed. These statements apply unchanged to the
original selected cells of each skeleton.  Let x lie in its unique open m-cell, using the open-
cell cover and disjointness. Below dimension m set V_n=C_n=∅. In native coordinates of this open
m-cell, choose a small open norm ball V_m centered at the coordinate of x, with a compact closed
norm ball C_m contained in the characteristic-map interior and mapped into O; put nothing in
other open m-cells. The closed-ball neighborhood basis applies to the open coordinate preimage
of O intersected with the native open unit ball, and a smaller radius keeps the entire closed
buffer there. Properness supplies compactness; its continuous characteristic image is compact,
hence closed in X and in X^m. The cell interior is embedded, and its frontier lies in X^(m−1),
disjoint from this open m-cell. Its chosen ball pulls back openly in the native disk, while all
other m-cell and lower-cell preimages are empty. The same characteristic closed-set/complement
criterion therefore makes V_m open in X^m, not necessarily in X. When m=0, the native Fin0 disk
and its open cell are singletons. The zero-cell singleton and closed-cell criterion make the
zero skeleton discrete, so use V_0=C_0={x}. We maintain V_n open and C_n closed in X^n,
V_n⊆C_n⊆O, and their restrictions to preceding skeleta equal the earlier sets. All initial balls
refer to the usual native coordinate topology; no equality of Euclidean and maximum norms is
claimed.

2. Given V_(n−1)⊆C_(n−1)⊆O for n>m, treat each original n-cell separately. Thus n≥1. Use its
native characteristic map Φ:D_n→X^n and the native maximum-norm sphere S_n={θ:||θ||∞=1}. On that
sphere let T=Φ⁻¹(V_(n−1)) and K=Φ⁻¹(C_(n−1)). The actual frontier lies in X^(n−1), so these are
preimages under the continuous boundary restriction into the preceding skeleton. T is open in
S_n; K is closed there. The proper-space compact-sphere and closed-subset compactness leaves
make K compact, even though C_(n−1) need not be compact. T⊆K, and Φ(K)⊆O.  Bind the uniform
closed-collar choice to the exact compact_eventually_forall API without extending Φ beyond its
disk. Take the radial parameter r in the ordinary interval I=[0,1], the point r=1 in its
inherited topology, and θ in compact K. The map (r,θ)↦rθ is jointly continuous by scalar
multiplication and always lies in D_n, since ||rθ||∞=r≤1. Therefore its composite with the
already restricted continuous Φ is continuous on I×K. The relation Φ(rθ)∈O holds on a full
product neighborhood of (1,θ) in these subtypes for every θ∈K. compact_eventually_forall gives a
relative neighborhood of1 in I where it holds for ALL θ∈K. The metric closed-ball neighborhood
basis on I, followed by shrinking, supplies 0<δ_α<1/2 with [1−δ_α,1] contained in that
neighborhood. Consequently the entire CLOSED radial collar {rθ:θ∈K,1−δ_α≤r≤1} lies in Φ⁻¹(O). If
K=∅ choose any such δ_α and the condition is vacuous. There is no use of Φ at r>1, no
compactness of an infinite skeleton, and no radius uniform across cells.  Include in V_n the
interior collar {rθ:θ∈T,1−δ_α<r<1}, in addition to V_(n−1). Include in C_n the closed collar
over K with radius interval [1−δ_α,1], in addition to C_(n−1). Native radial coordinates are
r=||z||∞ and θ=z/r; r≥1−δ_α>1/2 on the closed collar, so the normalization never approaches0.
This is the original radial-collar algorithm, run on the native maximum-norm disk rather than an
unidentified Euclidean disk. Distinct open-cell interiors are disjoint, so prescriptions are
unambiguous; at every characteristic boundary point they use exactly the earlier skeletal
membership, including noninjective attaching maps.

3. For each native characteristic disk, the preimage of V_n is its open collar together with T
on the boundary, an open set in D_n. Indeed on r>1−δ_α the native radial coordinates are
continuous and it is exactly the inverse image of open T under θ=z/||z||∞. The preimage of C_n
is its closed collar over K, including K at r=1. This collar is compact: it is the continuous
scalar-multiplication image of compact K×[1−δ_α,1], using compactness of closed real intervals
and products. It is therefore closed in the Hausdorff native disk. Nonregular frontier
identifications introduce precisely K and T, and lower-dimensional restrictions have already
been checked.  Apply the per-cell quotient q_e:D_n→C_e from step1: a closed characteristic
preimage gives a closed restriction on the actual closed-cell image. Since each C_e is closed in
the ambient Hausdorff X, this restriction is also ambient closed. The inherited skeletal CW
closed-cell criterion then makes C_n closed in X^n. Apply the same criterion to X^n minus V_n,
whose characteristic preimages are closed, to obtain openness of V_n in X^n. This preserves
V_n⊆C_n⊆O and the skeletal restrictions. In particular closure_(X^n)(V_n)⊆C_n⊆O, the buffer
needed in Hatcher’s printed construction.  Let V=⋃_(n≥m)V_n and C=⋃_(n≥m)C_n. Their
intersections with each actual finite skeleton X^n are V_n,C_n. Every original closed d-cell
lies in X^d by the closed-cell skeleton bound, so its restrictions have already been checked at
this finite stage. The ambient CW closed-cell criterion makes C closed in X, and applied to X
minus V makes V open in X. Thus x∈V⊆C⊆O. This is the original weak-topology argument with its
actual native disk-to-cell interfaces, not an assumption that the CW structure record alone
exports a skeletal quotient. No positive lower bound on δ_α and no local finiteness or bound on
dimensions is used.

4. For n>m define R_n:V_n×I→V_n by fixing V_(n−1) and moving an n-cell collar point rθ to
((1−s)r+s)θ at time s. The radius remains in its chosen open collar for s<1; at s=1 its image is
the attaching point Φ(θ)∈V_(n−1). On the characteristic-disk boundary the formula is the
identity, agreeing with the fixed earlier skeleton even when multiple boundary points are
identified. Hence it is well-defined on the cell quotient, is continuous, fixes V_(n−1), and is
a deformation retraction onto V_(n−1). For continuity use the actual skeletal characteristic-
coproduct quotient whose closed-set certificate is detailed in step6, using the inherited
subcomplex maps. Restrict it to the OPEN subset V_n with
topo.mathlib_quotient_open_restriction_g8. Its characteristic pullbacks are jointly continuous:
on positive-radius collar coordinates the radial formula above is continuous, and on the earlier
skeleton it is the identity; boundary formulas agree exactly at every attaching identification.
Apply topo.quotient_map_locally_compact_product_descent_g8 to the FUNCTION I×V_n→V_n and that
restricted quotient, swapping factors from V_n×I as necessary. This supplier exports continuity
descent, not an assumed bundled quotient-map theorem for q×id. The native radial normalization
is used only for r>1−δ_α>0. The same characteristic-summand product redistribution and inherited
open-subspace argument detailed in step6 establishes upstairs joint continuity in the ordinary
product.

5. Set a_n=2^(−n). Starting at time0 with the identity, apply R_n during [a_n,a_(n−1)] in
descending dimension, with progress parameter (t−a_n)/(a_(n−1)−a_n). For an input in V_d, only
the stages d,d−1,…,m+1 act: it stays fixed until a_d, is moved by R_d to V_(d−1), is then moved
by R_(d−1), and so on, arriving in V_m at a_m. This definition is independent of the chosen d
because a higher R_j fixes the earlier skeleton. Finite pasting on V_d×I gives continuity there
and agrees on boundaries; near t=0 the restriction is the identity for t≤a_d. After a_m leave
the point fixed. Each point lies in a finite-dimensional open cell, although X may be infinite-
dimensional. The finite closed-time-interval pasting is an application of the existing finite-
family locally-finite and locally-finite closed-pasting leaves on the subspace V_d×I; exact
endpoint agreements hold because each R_n ends in its fixed earlier skeleton. Exhaustion by
actual finite skeleta is the named CW exhaustion, not a bound on the dimension of X. For later
characteristic pullbacks, the whole closed d-cell lies in X^d, including all identified frontier
points, by the closed-cell skeleton bound.

6. Joint continuity on the full V×I follows from the original characteristic quotient, rather
than pointwise finite-stage stabilization. First bind that quotient independently of any
homotopy. Let D=Sigma_(d,e) D_d be the topological coproduct of ALL original native closed
characteristic disks and q:D→X their characteristic map. Each summand map is continuous by the
actual ContinuousOn-to-domRestrict binding in step1, so continuous_sigma makes q continuous. The
closed-cell-image and closed-cell-union identities give surjectivity; the family is not asserted
finite and the coproduct is not asserted compact. If q⁻¹(A) is closed, its restriction to each
summand is closed. The per-cell compact-Hausdorff quotient q_e from step1 then makes A∩C_e
closed in the induced closed-cell topology. Since C_e is closed in X, it is ambient closed. The
CW closed-cell criterion yields A closed in X. The converse follows from continuity of q.
mathlib.is_quotient_map_iff_is_closed_g8 therefore certifies q as a quotient map. Exactly this
argument applies to each actual skeleton via its selected-index subcomplex structure and
unchanged characteristic maps.  Since V is now proved OPEN,
topo.mathlib_quotient_open_restriction_g8 gives the quotient map q_V:q⁻¹(V)→V in the actual
subtype topologies. Its source is literally the subtype q⁻¹(V) of D, not definitionally a sigma
type of disk subtypes. For each (d,e), put W_e={z∈D_d:Φ_e(z)∈V}. These W_e are open in their
native disks. The bijection Sigma_e W_e→q⁻¹(V), (e,z)↦the same disk representative, has the
inherited coproduct topology: a subset of q⁻¹(V) is open precisely when its inverse image in
each W_e is open, by the sigma open-set criterion and open-subspace restriction. Thus using this
coordinate identification requires exactly that topology check, not a silent definitional cast.
Apply sigma_product_distrib_homeomorph_g8 to (Sigma_e W_e)×I, obtaining Sigma_e(W_e×I), and
continuous_sigma to the lifted scheduled homotopy. On each W_e×I it is the finite-dimensional
construction on V_d, because the ENTIRE closed d-cell lies in X^d and V∩X^d=V_d. The closed-cell
bound and step5 finite pasting therefore prove its joint continuity on every summand, including
time0 and every boundary representative. The coordinate redistribution and inherited-subspace
identification prove continuity upstairs on q⁻¹(V)×I; swap factors to I×q⁻¹(V).  Finally apply
the existing locally-compact-product FUNCTION descent to g:I×V→V and q_V: its pullback
(t,z)↦g(t,q_V(z)) is just the continuous map established above. The ordinary interval I is
locally compact, so g is continuous on the ordinary product; swapping factors gives the asserted
V×I homotopy. This verifies the accumulating time0 as Hatcher’s p523 discussion requires. No
bundled product-quotient theorem beyond the named function-descent contract, compactness of the
disk coproduct, equality of disk with a nonregular closed cell, or equality of CW and ordinary
product topologies for arbitrary infinite CW factors is assumed.

7. The scheduled homotopy fixes V_m and at time1 is a retraction to that initial cell-coordinate
ball. Contract this ball to x by its straight-line contraction, or use the constant contraction
when m=0. Concatenate the two continuous homotopies and view their values in V. This gives id_V
homotopic to the constant map at x in the subspace V itself, not merely in O or X. The
contractibility criterion therefore yields ContractibleSpace V.

8. Every open neighborhood of every point contains the open contractible V just constructed. A
contractible nonempty space is path connected and simply connected; hence these V form path-
connected open neighborhood bases. Every loop based at x and lying in V is nullhomotopic already
in V, and consequently in X, proving semilocal simple connectivity. Path components in a locally
path-connected space are open: for any point in a component, one of its path-connected open
neighborhoods lies in that component. If X is connected and nonempty, multiple path components
would give a separation into a component and the union of the others; there is therefore a
single component and X is path connected.

`ContractibleSpace V` uses the topology induced from X, and each loop homotopy
fixes its base point. `ConnectedSpace X` includes nonemptiness, so the last
implication is precisely the stated connected-and-nonempty consequence.
For empty X the neighborhood and based-loop assertions are vacuous; no
contractibility or path-connectedness of the empty space is claimed.
-/
theorem cw_contractible_open_neighborhoods
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    (∀ (x : X) (O : Set X), IsOpen O → x ∈ O →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ ContractibleSpace V) ∧
    LocallyPathConnectedSpace X ∧
    (∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ γ : Path x x, Set.range γ ⊆ V → γ.Homotopic (Path.refl x)) ∧
    (ConnectedSpace X → PathConnectedSpace X) := by
  suffices hneighborhoods :
      ∀ (x : X) (O : Set X), IsOpen O → x ∈ O →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ ContractibleSpace V by
    have hlocal : LocallyPathConnectedSpace X :=
      locallyPathConnected_of_contractible_neighborhoods hneighborhoods
    refine ⟨hneighborhoods, hlocal, ?_, ?_⟩
    · intro x
      obtain ⟨V, hV, hxV, _, hcontract⟩ :=
        hneighborhoods x Set.univ isOpen_univ (Set.mem_univ x)
      have : ContractibleSpace V := hcontract
      exact ⟨V, hV, hxV, fun γ hγ ↦ loop_nullhomotopic_of_contractible_subset hxV γ hγ⟩
    · intro hconnected
      exact PathConnectedSpace.of_locallyPathConnectedSpace
  classical
  intro x O hO hxO
  -- Step 1: choose the unique open cell containing x, in native maximum-norm coordinates.
  have hxcell : x ∈ ⋃ (n : ℕ) (e : Topology.RelCWComplex.cell (Set.univ : Set X) n),
      Topology.RelCWComplex.openCell n e := by
    rw [Topology.CWComplex.iUnion_openCell_eq_complex]
    exact Set.mem_univ x
  obtain ⟨m, hxcell⟩ := Set.mem_iUnion.mp hxcell
  obtain ⟨e, a, ha, hax⟩ := Set.mem_iUnion.mp hxcell
  let φ := Topology.RelCWComplex.map (C := (Set.univ : Set X)) m e
  have hφ : ContinuousOn φ (Metric.closedBall 0 1) :=
    Topology.RelCWComplex.continuousOn m e
  have hsmall : IsOpen (Metric.ball (0 : Fin m → ℝ) 1 ∩ φ ⁻¹' O) :=
    (hφ.mono Metric.ball_subset_closedBall).isOpen_inter_preimage Metric.isOpen_ball hO
  have haO : a ∈ Metric.ball (0 : Fin m → ℝ) 1 ∩ φ ⁻¹' O :=
    ⟨ha, by change Topology.RelCWComplex.map m e a ∈ O; rwa [hax]⟩
  obtain ⟨r, hr, hbuffer⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hsmall.mem_nhds haO)
  let V₀ : Set X := φ '' Metric.ball a r
  let C₀ : Set X := φ '' Metric.closedBall a r
  have hC₀O : C₀ ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hbuffer hz).2
  have hV₀C₀ : V₀ ⊆ C₀ := Set.image_mono Metric.ball_subset_closedBall
  have hxV₀ : x ∈ V₀ := ⟨a, Metric.mem_ball_self hr, hax⟩
  have hC₀compact : IsCompact C₀ :=
    (isCompact_closedBall a r).image_of_continuousOn
      (hφ.mono fun z hz ↦ Metric.ball_subset_closedBall (hbuffer hz).1)
  have hC₀closed : IsClosed C₀ := hC₀compact.isClosed
  have hC₀cell : C₀ ⊆ Topology.RelCWComplex.openCell m e := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, (hbuffer hz).1, rfl⟩
  have hball_source : Metric.ball a r ⊆ φ.source := by
    rw [Topology.RelCWComplex.source_eq]
    exact fun z hz ↦ (hbuffer (Metric.ball_subset_closedBall hz)).1
  let cellChart : PartialHomeomorph (Fin m → ℝ) X :=
    { toPartialEquiv := φ
      continuousOn_toFun := by
        rw [Topology.RelCWComplex.source_eq]
        exact hφ.mono Metric.ball_subset_closedBall
      continuousOn_invFun := Topology.RelCWComplex.continuousOn_symm m e }
  let ballChart : Metric.ball a r ≃ₜ V₀ :=
    cellChart.homeomorphOfImageSubsetSource hball_source rfl
  have hV₀contractible : ContractibleSpace V₀ := by
    let : ContractibleSpace (Metric.ball a r) :=
      (convex_ball a r).contractibleSpace ⟨a, Metric.mem_ball_self hr⟩
    exact ballChart.symm.contractibleSpace
  have hC₀skeleton : C₀ ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) :=
    hC₀cell.trans (Topology.RelCWComplex.openCell_subset_skeletonLT m e)
  have hV₀skeleton : V₀ ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) :=
    hV₀C₀.trans hC₀skeleton
  have hV₀lower : Disjoint
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) m : Set X) V₀ :=
    (Topology.RelCWComplex.disjoint_skeletonLT_openCell (le_refl (m : ℕ∞))).mono_right
      (hV₀C₀.trans hC₀cell)
  have hV₀frontier : Disjoint (Topology.RelCWComplex.cellFrontier m e) V₀ :=
    hV₀lower.mono_left (Topology.RelCWComplex.cellFrontier_subset_skeletonLT m e)
  have hpreimage : Metric.closedBall (0 : Fin m → ℝ) 1 ∩ φ ⁻¹' V₀ =
      Metric.ball a r := by
    ext z
    constructor
    · rintro ⟨hz, w, hw, hzw⟩
      by_cases hzint : z ∈ Metric.ball (0 : Fin m → ℝ) 1
      · have hzsource : z ∈ φ.source := by rwa [Topology.RelCWComplex.source_eq]
        have : w = z := φ.injOn (hball_source hw) hzsource hzw
        rwa [← this]
      · have hzboundary : z ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
          rw [Metric.mem_sphere]
          exact le_antisymm hz (le_of_not_gt hzint)
        exact False.elim <| Set.disjoint_left.mp hV₀frontier
          ⟨z, hzboundary, rfl⟩ ⟨w, hw, hzw⟩
    · intro hz
      exact ⟨Metric.ball_subset_closedBall (hbuffer (Metric.ball_subset_closedBall hz)).1,
        z, hz, rfl⟩
  have hclosedCell_diff : IsClosed (Topology.RelCWComplex.closedCell m e \ V₀) := by
    have heq : Topology.RelCWComplex.closedCell m e \ V₀ =
        φ '' (Metric.closedBall (0 : Fin m → ℝ) 1 \ Metric.ball a r) := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hy⟩
        refine ⟨z, ⟨hz, ?_⟩, rfl⟩
        exact fun hzball ↦ hy ⟨z, hzball, rfl⟩
      · rintro ⟨z, ⟨hz, hzball⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, ?_⟩
        intro hy
        exact hzball (hpreimage.subset ⟨hz, hy⟩)
    rw [heq]
    exact ((isCompact_closedBall (0 : Fin m → ℝ) 1).diff Metric.isOpen_ball
      |>.image_of_continuousOn (hφ.mono Set.sdiff_subset)).isClosed
  have hV₀subsetO : V₀ ⊆ O := hV₀C₀.trans hC₀O
  let S : Topology.CWComplex.Subcomplex (Set.univ : Set X) :=
    Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1)
  have hother (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n)
      (hn : n ≤ m)
      (hne : (⟨m, e⟩ : Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) ≠ ⟨n, j⟩) :
      Disjoint V₀ (Topology.RelCWComplex.closedCell n j) := by
    rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
    apply Disjoint.union_right
    · apply hV₀lower.symm.mono_right
      exact (Topology.RelCWComplex.cellFrontier_subset_skeletonLT n j).trans
        (Topology.RelCWComplex.skeletonLT_mono (by exact_mod_cast hn))
    · exact (Topology.RelCWComplex.disjoint_openCell_of_ne hne).mono_left
        (hV₀C₀.trans hC₀cell)
  have hSclosed : IsClosed ((S : Set X) \ V₀) := by
    apply Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (C := (Set.univ : Set X)) (Set.subset_univ _)
    intro n hn j
    by_cases hnm : n ≤ m
    · right
      have hjS : Topology.RelCWComplex.closedCell n j ⊆ (S : Set X) :=
        (Topology.RelCWComplex.closedCell_subset_skeletonLT n j).trans
          (Topology.RelCWComplex.skeletonLT_mono (by exact_mod_cast Nat.add_le_add_right hnm 1))
      have hinter : ((S : Set X) \ V₀) ∩ Topology.RelCWComplex.closedCell n j =
          Topology.RelCWComplex.closedCell n j \ V₀ := by
        ext y
        exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨hjS h.1, h.2⟩, h.1⟩⟩
      rw [hinter]
      by_cases heq : (⟨m, e⟩ : Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) = ⟨n, j⟩
      · cases heq
        exact hclosedCell_diff
      · have hd := hother n j hnm heq
        have heqdiff : Topology.RelCWComplex.closedCell n j \ V₀ =
            Topology.RelCWComplex.closedCell n j := by
          ext y
          exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, Set.disjoint_left.mp hd.symm h⟩⟩
        rw [heqdiff]
        exact Topology.RelCWComplex.isClosed_closedCell
    · left
      apply Disjoint.mono_left Set.sdiff_subset
      exact Topology.RelCWComplex.disjoint_skeletonLT_openCell
        (C := (Set.univ : Set X)) (j := j) (by exact_mod_cast Nat.lt_of_not_ge hnm)
  have hV₀openInSkeleton : IsOpen {y : S | y.val ∈ V₀} := by
    have hc := hSclosed.preimage
      (continuous_subtype_val : Continuous (Subtype.val : S → X))
    have heq : (Subtype.val : S → X) ⁻¹' ((S : Set X) \ V₀) =
        {y : S | y.val ∈ V₀}ᶜ := by
      ext y
      change (y.val ∈ (S : Set X) ∧ y.val ∉ V₀) ↔ y.val ∉ V₀
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨y.property, h⟩⟩
    rw [heq] at hc
    simpa only [compl_compl] using hc.isOpen_compl
  -- This predicate retains precisely the set-theoretic induction hypotheses.
  -- The recursive successor must take n, A and B as inputs, not as chosen outputs.
  let Stage : ℕ → Set X → Set X → Prop := fun n A B ↦
    A ⊆ B ∧ B ⊆ O ∧ B ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n + 1) : Set X) ∧
    IsOpen {y : Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n + 1) |
      y.val ∈ A} ∧ IsClosed B ∧ x ∈ A
  have successor (m : ℕ) (V₀ C₀ : Set X) (hstage : Stage m V₀ C₀) :
      ∃ (A B : Set X) (hVA : V₀ ⊆ A),
        Stage (m + 1) A B ∧ C₀ ⊆ B ∧
        A ∩ (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) = V₀ ∧ B ∩ (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) = C₀ ∧
        ∃ (R : A → V₀) (H : unitInterval × A → A),
          (∀ y : V₀, R ⟨y.val, hVA y.property⟩ = y) ∧
          (∀ y, H (0, y) = y) ∧ (∀ y, (H (1, y)).val = (R y).val) ∧
          (∀ t (y : A), y.val ∈ V₀ → H (t, y) = y) ∧
          (∀ n (i : Topology.RelCWComplex.cell (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 2) : Set X) n),
            Continuous (fun p : unitInterval ×
                {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
                  Topology.RelCWComplex.map n i z.val ∈ A} ↦
              H (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩))) ∧
          (Continuous H → ∃ r : C(A, V₀),
            (∀ y, r y = R y) ∧
            r.comp (ContinuousMap.inclusion hVA) = ContinuousMap.id V₀ ∧
            Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id A)
              ((ContinuousMap.inclusion hVA).comp r) {y : A | y.val ∈ V₀})) := by
    exact cw_skeletal_neighborhood_successor x O hO m V₀ C₀ hstage
  have hinitial_stage_data : Stage m V₀ C₀ :=
    ⟨hV₀C₀, hC₀O, hC₀skeleton, hV₀openInSkeleton, hC₀closed, hxV₀⟩
  let StageState (n : ℕ) := {p : Set X × Set X // Stage n p.1 p.2}
  let nextState (n : ℕ) (s : StageState n) : StageState (n + 1) :=
    let hs := successor n s.val.1 s.val.2 s.property
    ⟨(hs.choose, hs.choose_spec.choose), hs.choose_spec.choose_spec.choose_spec.1⟩
  have hnextState (n : ℕ) (s : StageState n) :
      s.val.1 ⊆ (nextState n s).val.1 ∧ s.val.2 ⊆ (nextState n s).val.2 ∧
      (nextState n s).val.1 ∩
        (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n + 1) : Set X) = s.val.1 ∧
      (nextState n s).val.2 ∩
        (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n + 1) : Set X) = s.val.2 := by
    let hs := successor n s.val.1 s.val.2 s.property
    exact ⟨hs.choose_spec.choose_spec.choose,
      hs.choose_spec.choose_spec.choose_spec.2.1,
      hs.choose_spec.choose_spec.choose_spec.2.2.1,
      hs.choose_spec.choose_spec.choose_spec.2.2.2.1⟩
  let stages : (k : ℕ) → StageState (m + k) :=
    fun k ↦ Nat.rec (motive := fun k ↦ StageState (m + k))
      ⟨(V₀, C₀), hinitial_stage_data⟩ (fun k s ↦ nextState (m + k) s) k
  let Vseq (k : ℕ) : Set X := (stages k).val.1
  let Cseq (k : ℕ) : Set X := (stages k).val.2
  have hseq_stage (k : ℕ) : Stage (m + k) (Vseq k) (Cseq k) := (stages k).property
  have hseq_zero : Vseq 0 = V₀ ∧ Cseq 0 = C₀ := ⟨rfl, rfl⟩
  have hseq_step (k : ℕ) : Vseq k ⊆ Vseq (k + 1) ∧ Cseq k ⊆ Cseq (k + 1) ∧
      Vseq (k + 1) ∩
        (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + k + 1) : Set X) =
          Vseq k ∧
      Cseq (k + 1) ∩
        (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + k + 1) : Set X) =
          Cseq k := hnextState (m + k) (stages k)
  have hVseq_mono : Monotone Vseq := monotone_nat_of_le_succ (fun k ↦ (hseq_step k).1)
  have hCseq_mono : Monotone Cseq := monotone_nat_of_le_succ (fun k ↦ (hseq_step k).2.1)
  have hseq_deformation (k : ℕ) :
      ∃ (R : Vseq (k + 1) → Vseq k)
        (H : unitInterval × Vseq (k + 1) → Vseq (k + 1)),
        (∀ y : Vseq k, R ⟨y.val, (hseq_step k).1 y.property⟩ = y) ∧
        (∀ y, H (0, y) = y) ∧ (∀ y, (H (1, y)).val = (R y).val) ∧
        (∀ t (y : Vseq (k + 1)), y.val ∈ Vseq k → H (t, y) = y) ∧
        (∀ n (i : Topology.RelCWComplex.cell
            (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + k + 2) : Set X) n),
          Continuous (fun p : unitInterval ×
              {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
                Topology.RelCWComplex.map n i z.val ∈ Vseq (k + 1)} ↦
            H (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩))) ∧
        (Continuous H → ∃ r : C(Vseq (k + 1), Vseq k),
          (∀ y, r y = R y) ∧
          r.comp (ContinuousMap.inclusion (hseq_step k).1) = ContinuousMap.id (Vseq k) ∧
          Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id (Vseq (k + 1)))
            ((ContinuousMap.inclusion (hseq_step k).1).comp r)
            {y : Vseq (k + 1) | y.val ∈ Vseq k})) := by
    let hs := successor (m + k) (Vseq k) (Cseq k) (hseq_stage k)
    exact hs.choose_spec.choose_spec.choose_spec.2.2.2.2
  have hseq_continuous (k : ℕ) :
      Continuous ((hseq_deformation k).choose_spec.choose) := by
    let T := Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + k + 2)
    let V := Vseq (k + 1)
    let H := (hseq_deformation k).choose_spec.choose
    have hc := (hseq_deformation k).choose_spec.choose_spec.2.2.2.2.1
    have hdim : ((m + (k + 1) : ℕ) : ℕ∞) + 1 = (m + k + 2 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      norm_num
    have hcar : V ⊆ (T : Set X) := by
      have hs := (hseq_stage (k + 1)).1.trans (hseq_stage (k + 1)).2.2.1
      change V ⊆ (Topology.RelCWComplex.skeletonLT (Set.univ : Set X)
        (((m + (k + 1) : ℕ) : ℕ∞) + 1) : Set X) at hs
      rw [hdim] at hs
      exact hs
    have hopen : IsOpen {y : T | y.val ∈ V} := by
      have hs := (hseq_stage (k + 1)).2.2.2.1
      change IsOpen {y : Topology.RelCWComplex.skeletonLT (Set.univ : Set X)
        (((m + (k + 1) : ℕ) : ℕ∞) + 1) | y.val ∈ V} at hs
      rw [hdim] at hs
      exact hs
    let J := Σ n : ℕ, Topology.RelCWComplex.cell (T : Set X) n
    let D (j : J) : Type := Metric.closedBall (0 : Fin j.1 → ℝ) 1
    let q : (Σ j : J, D j) → T := fun p ↦
      ⟨Topology.RelCWComplex.map p.1.1 p.1.2 p.2.val,
        Topology.RelCWComplex.closedCell_subset_complex _ _ ⟨p.2.val, p.2.property, rfl⟩⟩
    have hqcont : Continuous q := by
      apply continuous_sigma
      rintro ⟨n, i⟩
      exact (Topology.RelCWComplex.continuousOn n i).domRestrict.subtype_mk _
    have hq : Topology.IsQuotientMap q := by
      apply Topology.isQuotientMap_iff_isClosed.mpr
      constructor
      · intro y
        have hy : y.val ∈ ⋃ n : ℕ, ⋃ i : Topology.RelCWComplex.cell (T : Set X) n,
            Topology.CWComplex.closedCell n i := by
          rw [Topology.CWComplex.union]
          exact y.property
        obtain ⟨n, hy⟩ := Set.mem_iUnion.mp hy
        obtain ⟨i, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
        exact ⟨⟨⟨n, i⟩, ⟨z, hz⟩⟩, Subtype.ext hzy⟩
      · intro A
        constructor
        · exact fun hA ↦ hA.preimage hqcont
        · intro hA
          have himage : IsClosed (Subtype.val '' A : Set X) := by
            apply (Topology.CWComplex.closed (T : Set X) _
              (by rintro _ ⟨y, _, rfl⟩; exact y.property)).mpr
            intro n i
            let : CompactSpace (D ⟨n, i⟩) :=
              isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
            let χ : D ⟨n, i⟩ → X := fun z ↦ Topology.RelCWComplex.map n i z.val
            have hχ : Continuous χ := (Topology.RelCWComplex.continuousOn n i).domRestrict
            have hpre : IsClosed ((fun z : D ⟨n, i⟩ ↦ q ⟨⟨n, i⟩, z⟩) ⁻¹' A) :=
              hA.preimage (@continuous_sigmaMk J D _ ⟨n, i⟩)
            have heq : (Subtype.val '' A : Set X) ∩ Topology.CWComplex.closedCell n i =
                χ '' ((fun z : D ⟨n, i⟩ ↦ q ⟨⟨n, i⟩, z⟩) ⁻¹' A) := by
              ext y
              constructor
              · rintro ⟨⟨y, hy, rfl⟩, z, hz, hzy⟩
                refine ⟨⟨z, hz⟩, ?_, hzy⟩
                have he : q ⟨⟨n, i⟩, ⟨z, hz⟩⟩ = y := Subtype.ext hzy
                change q ⟨⟨n, i⟩, ⟨z, hz⟩⟩ ∈ A
                rwa [he]
              · rintro ⟨z, hz, rfl⟩
                exact ⟨⟨q ⟨⟨n, i⟩, z⟩, hz, rfl⟩, ⟨z.val, z.property, rfl⟩⟩
            rw [heq]
            exact (hpre.isCompact.image hχ).isClosed
          convert himage.preimage continuous_subtype_val using 1
          exact (Set.preimage_image_eq _ Subtype.val_injective).symm
    let W : Set T := {y | y.val ∈ V}
    let P := q ⁻¹' W
    have hP : IsOpen P := hopen.preimage hqcont
    let E (j : J) := {z : D j // q ⟨j, z⟩ ∈ W}
    let e : (Σ j : J, E j) ≃ₜ P := by
      let ee : (Σ j : J, E j) ≃ P :=
        { toFun := fun p ↦ ⟨⟨p.1, p.2.val⟩, p.2.property⟩
          invFun := fun p ↦ ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
          left_inv := fun p ↦ by cases p; rfl
          right_inv := fun p ↦ by cases p; rfl }
      apply ee.toHomeomorphOfContinuousOpen
      · apply continuous_sigma
        intro j
        exact ((@continuous_sigmaMk J D _ j).comp
          (continuous_subtype_val : Continuous (Subtype.val : E j → D j))).subtype_mk _
      · apply isOpenMap_sigma.mpr
        intro j
        have hj : IsOpen {z : D j | q ⟨j, z⟩ ∈ W} := hP.preimage continuous_sigmaMk
        exact ((@isOpenMap_sigmaMk J D _ j).comp hj.isOpenMap_subtype_val).subtype_mk _
    let qW : P → W := W.restrictPreimage q
    have hqW : Topology.IsQuotientMap qW := hq.restrictPreimage_isOpen hopen
    let H' : unitInterval × W → V := fun p ↦ H (p.1, ⟨p.2.val.val, p.2.property⟩)
    have hH' : Continuous H' := by
      apply (hqW.comp e.isQuotientMap).continuous_lift_prod_right
      let F : unitInterval × (Σ j : J, E j) → V :=
        fun p ↦ H' (p.1, qW (e p.2))
      let G : (Σ j : J, E j × unitInterval) → V :=
        fun p ↦ F (p.2.2, ⟨p.1, p.2.1⟩)
      have hG : Continuous G := by
        apply continuous_sigma
        rintro ⟨n, i⟩
        exact (hc n i).comp (continuous_snd.prodMk continuous_fst)
      let rearrange : ((Σ j : J, E j) × unitInterval) ≃ₜ
          (Σ j : J, E j × unitInterval) := Homeomorph.sigmaProdDistrib
      have hp : Continuous (fun p : (Σ j : J, E j) × unitInterval ↦ F (p.2, p.1)) := by
        convert hG.comp rearrange.continuous using 1
        funext p
        rfl
      exact hp.comp continuous_swap
    let lift : V → W := fun y ↦ ⟨⟨y.val, hcar y.property⟩, y.property⟩
    have hlift : Continuous lift := (continuous_subtype_val.subtype_mk _).subtype_mk _
    exact hH'.comp (continuous_fst.prodMk (hlift.comp continuous_snd))
  have hseq_bundle (k : ℕ) :
      ∃ r : C(Vseq (k + 1), Vseq k),
        (∀ y, r y = (hseq_deformation k).choose y) ∧
        r.comp (ContinuousMap.inclusion (hseq_step k).1) = ContinuousMap.id (Vseq k) ∧
        Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id (Vseq (k + 1)))
          ((ContinuousMap.inclusion (hseq_step k).1).comp r)
          {y : Vseq (k + 1) | y.val ∈ Vseq k}) :=
    (hseq_deformation k).choose_spec.choose_spec.2.2.2.2.2 (hseq_continuous k)
  let sk (k : ℕ) :=
    Topology.RelCWComplex.skeletonLT (Set.univ : Set X) ((m + k : ℕ) + 1)
  have hsk_mono : Monotone (fun k ↦ (sk k : Set X)) := by
    intro a b hab
    apply Topology.RelCWComplex.skeletonLT_mono
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hab m) 1
  have hVseq_carrier (k : ℕ) : Vseq k ⊆ (sk k : Set X) :=
    (hseq_stage k).1.trans (hseq_stage k).2.2.1
  have hVseq_later (n k : ℕ) (hnk : n ≤ k) :
      Vseq k ∩ (sk n : Set X) = Vseq n := by
    induction k, hnk using Nat.le_induction with
    | base => exact Set.inter_eq_self_of_subset_left (hVseq_carrier n)
    | succ k hnk ih =>
      calc
        Vseq (k + 1) ∩ (sk n : Set X) =
            (Vseq (k + 1) ∩ (sk k : Set X)) ∩ (sk n : Set X) := by
          ext y
          exact ⟨fun h ↦ ⟨⟨h.1, hsk_mono hnk h.2⟩, h.2⟩,
            fun h ↦ ⟨h.1.1, h.2⟩⟩
        _ = Vseq k ∩ (sk n : Set X) := by
          have hstep : Vseq (k + 1) ∩ (sk k : Set X) = Vseq k := by
            simpa only [sk, Nat.cast_add] using (hseq_step k).2.2.1
          rw [hstep]
        _ = Vseq n := ih
  let U : Set X := ⋃ k, Vseq k
  have hU_inter (n : ℕ) : U ∩ (sk n : Set X) = Vseq n := by
    ext y
    constructor
    · rintro ⟨hy, hyS⟩
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
      rcases le_total k n with hkn | hnk
      · exact hVseq_mono hkn hk
      · exact (Set.ext_iff.mp (hVseq_later n k hnk) y).mp ⟨hk, hyS⟩
    · intro hy
      exact ⟨Set.mem_iUnion.mpr ⟨n, hy⟩, hVseq_carrier n hy⟩
  have hcell_sk (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set X) n)
      (z : Metric.closedBall (0 : Fin n → ℝ) 1) :
      Topology.RelCWComplex.map n i z.val ∈ (sk n : Set X) := by
    apply Topology.RelCWComplex.skeletonLT_mono
      (show (n : ℕ∞) + 1 ≤ (m + n : ℕ) + 1 by
        exact_mod_cast (show n + 1 ≤ m + n + 1 by omega))
    exact Topology.RelCWComplex.closedCell_subset_skeletonLT n i ⟨z.val, z.property, rfl⟩
  have hU_pullback (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set X) n)
      (z : Metric.closedBall (0 : Fin n → ℝ) 1) :
      Topology.RelCWComplex.map n i z.val ∈ U ↔
        Topology.RelCWComplex.map n i z.val ∈ Vseq n := by
    exact ⟨fun hz ↦ (Set.ext_iff.mp (hU_inter n) _).mp ⟨hz, hcell_sk n i z⟩,
      fun hz ↦ Set.mem_iUnion.mpr ⟨n, hz⟩⟩
  have hU_diskOpen (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set X) n) :
      IsOpen {z : Metric.closedBall (0 : Fin n → ℝ) 1 |
        Topology.RelCWComplex.map n i z.val ∈ U} := by
    let χ : Metric.closedBall (0 : Fin n → ℝ) 1 → sk n :=
      fun z ↦ ⟨Topology.RelCWComplex.map n i z.val, hcell_sk n i z⟩
    have hχ : Continuous χ := (Topology.RelCWComplex.continuousOn n i).domRestrict.subtype_mk _
    convert (hseq_stage n).2.2.2.1.preimage hχ using 1
    ext z
    exact hU_pullback n i z
  have hUopen : IsOpen U := by
    apply isClosed_compl_iff.mp
    apply (Topology.CWComplex.closed (Set.univ : Set X) _ (Set.subset_univ _)).mpr
    intro n i
    let D := Metric.closedBall (0 : Fin n → ℝ) 1
    let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    let χ : D → X := fun z ↦ Topology.RelCWComplex.map n i z.val
    have hχ : Continuous χ := (Topology.RelCWComplex.continuousOn n i).domRestrict
    have heq : Uᶜ ∩ Topology.RelCWComplex.closedCell n i = χ '' {z : D | χ z ∉ U} := by
      ext y
      constructor
      · rintro ⟨hy, z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, hy, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, z.val, z.property, rfl⟩
    rw [heq]
    exact ((hU_diskOpen n i).isClosed_compl.isCompact.image hχ).isClosed
  have hxU : x ∈ U := Set.mem_iUnion.mpr ⟨0, (hseq_stage 0).2.2.2.2.2⟩
  have hUO : U ⊆ O := by
    intro y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    exact (hseq_stage k).2.1 ((hseq_stage k).1 hk)
  let inc (k : ℕ) : Vseq k ⊆ U := Set.subset_iUnion Vseq k
  let qStages : (Σ k, Vseq k) → U := fun p ↦ ⟨p.2.val, inc p.1 p.2.property⟩
  have hqStages : Topology.IsQuotientMap qStages := by
    have hqcont : Continuous qStages := by
      apply continuous_sigma
      intro k
      exact continuous_subtype_val.subtype_mk _
    have hsurj : Function.Surjective qStages := by
      intro y
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp y.property
      exact ⟨⟨k, ⟨y.val, hk⟩⟩, rfl⟩
    rw [Topology.isQuotientMap_iff]
    refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen (fun W ↦ ?_), hsurj⟩
    constructor
    · intro hpre
      have himage : IsOpen (Subtype.val '' W : Set X) := by
        apply isClosed_compl_iff.mp
        apply (Topology.CWComplex.closed (Set.univ : Set X) _ (Set.subset_univ _)).mpr
        intro n i
        let D := Metric.closedBall (0 : Fin n → ℝ) 1
        let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
        let χ : D → X := fun z ↦ Topology.RelCWComplex.map n i z.val
        have hχ : Continuous χ := (Topology.RelCWComplex.continuousOn n i).domRestrict
        have hwstage : IsOpen ((fun y : Vseq n ↦ qStages ⟨n, y⟩) ⁻¹' W) :=
          hpre.preimage (@continuous_sigmaMk ℕ (fun k ↦ Vseq k) _ n)
        obtain ⟨G, hG, hGeq⟩ := isOpen_induced_iff.mp hwstage
        have hopen : IsOpen {z : D | χ z ∈ Subtype.val '' W} := by
          have heq : {z : D | χ z ∈ Subtype.val '' W} =
              {z : D | χ z ∈ U} ∩ χ ⁻¹' G := by
            ext z
            constructor
            · rintro ⟨y, hy, hyy⟩
              have hzU : χ z ∈ U := hyy ▸ y.property
              have hzV : χ z ∈ Vseq n := (hU_pullback n i z).mp hzU
              refine ⟨hzU, ?_⟩
              have hmem : (⟨χ z, hzV⟩ : Vseq n) ∈
                  (fun y : Vseq n ↦ qStages ⟨n, y⟩) ⁻¹' W := by
                have he : qStages ⟨n, ⟨χ z, hzV⟩⟩ = y := Subtype.ext hyy.symm
                change qStages ⟨n, ⟨χ z, hzV⟩⟩ ∈ W
                rwa [he]
              rw [← hGeq] at hmem
              exact hmem
            · rintro ⟨hzU, hzG⟩
              have hzV : χ z ∈ Vseq n := (hU_pullback n i z).mp hzU
              have hmem : (⟨χ z, hzV⟩ : Vseq n) ∈
                  (Subtype.val : Vseq n → X) ⁻¹' G := hzG
              rw [hGeq] at hmem
              exact ⟨qStages ⟨n, ⟨χ z, hzV⟩⟩, hmem, rfl⟩
          rw [heq]
          exact (hU_diskOpen n i).inter (hG.preimage hχ)
        have heq : (Subtype.val '' W)ᶜ ∩ Topology.RelCWComplex.closedCell n i =
            χ '' {z : D | χ z ∉ Subtype.val '' W} := by
          ext y
          constructor
          · rintro ⟨hy, z, hz, rfl⟩
            exact ⟨⟨z, hz⟩, hy, rfl⟩
          · rintro ⟨z, hz, rfl⟩
            exact ⟨hz, z.val, z.property, rfl⟩
        rw [heq]
        exact (hopen.isClosed_compl.isCompact.image hχ).isClosed
      convert himage.preimage continuous_subtype_val using 1
      exact (Set.preimage_image_eq _ Subtype.val_injective).symm
    · exact fun hW ↦ hW.preimage hqcont
  let retractions (k : ℕ) : C(Vseq (k + 1), Vseq k) := (hseq_bundle k).choose
  let deformations (k : ℕ) : (ContinuousMap.id (Vseq (k + 1))).HomotopyRel
      ((ContinuousMap.inclusion (hseq_step k).1).comp (retractions k))
      {y : Vseq (k + 1) | y.val ∈ Vseq k} :=
    (hseq_bundle k).choose_spec.2.2.some
  let : ContractibleSpace (Vseq 0) := hseq_zero.1.symm ▸ hV₀contractible
  have hUcontractible : ContractibleSpace U :=
    CWNeighborhoodSchedule.union_contractible Vseq hVseq_mono hqStages retractions deformations
  exact ⟨U, hUopen, hxU, hUO, hUcontractible⟩


end HolomorphicAnosov
