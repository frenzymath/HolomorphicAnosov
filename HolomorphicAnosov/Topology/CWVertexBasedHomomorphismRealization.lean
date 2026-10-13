import HolomorphicAnosov.Topology.ConstantMapFundamentalGroup
import HolomorphicAnosov.Topology.CWVertexBasedHomomorphismRealizationNontrivial
import HolomorphicAnosov.Topology.CWVertexRealizationFromOneSkeleton
import HolomorphicAnosov.Topology.CWComplex.OneCellLoopDiskRealization
import HolomorphicAnosov.Topology.CWComplex.HigherCellExtension
import HolomorphicAnosov.Topology.CWComplex.RealizationSpanningTree
import HolomorphicAnosov.Topology.CWOneSkeletonPiOneSurjective
import HolomorphicAnosov.Topology.ConnectedCWOneSkeletonFiniteWalk
import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopGeneration
import HolomorphicAnosov.Topology.NullhomotopicSphereDiskExtension
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Realizing based homomorphisms from a CW complex

Source: Hatcher, *Algebraic Topology*, Proposition 1B.9, pp.90–91,
existence proof and maximal-tree paragraph. The target assumption is a
path-connected space with a surjective covering by a contractible space,
exactly the covering data used in that written existence proof.
-/

namespace HolomorphicAnosov

universe u v w

/- The constant-map case of the based realization statement. This isolates the
trivial homomorphism branch before the nontrivial CW extension construction. -/
theorem cw_vertex_based_homomorphism_realization_constant
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    (k₀ : K) (y₀ : Y) (φ : FundamentalGroup K k₀ →* FundamentalGroup Y y₀)
    (hφ : φ = 1) :
    ∃ f : C(K, Y), ∃ hf : f k₀ = y₀, FundamentalGroup.mapOfEq f hf = φ := by
  subst φ
  exact ⟨⟨fun _ ↦ y₀, continuous_const⟩, rfl, constant_continuousMap_mapOfEq k₀ y₀⟩

/-- Every homomorphism from the fundamental group of a connected Hausdorff CW
complex, based at a zero-cell, is induced by an actual based continuous map
into a path-connected space with a contractible covering space.

The CW structure is on `Set.univ` in the original topology. The vertex
hypothesis uses the actual zero skeleton of this structure. `IsCoveringMap`
is supplemented by surjectivity because Mathlib permits empty covering
fibres. `FundamentalGroup.mapOfEq f hf` is the genuine induced monoid
homomorphism with the endpoint equality `hf : f k₀ = y₀`; no connecting
path, opposite-group convention, or abstract homomorphism proxy is chosen.

Sources: Hatcher, Proposition 1B.9 pp.90–91; graph generators Proposition
1A.2 pp.84–85; one-skeleton surjectivity Proposition 1.26 pp.50–51;
canonical once-around circle Theorem 1.7 pp.29–30; disk filling Chapter 0
pp.14–15; original CW topology Appendix A.2 p.521 and closed-cell map
criterion p.523; quotient-product argument Proposition A.17 pp.532–533.
The native maximum-norm disk boundary adapter uses Bredon, *Topology and
Geometry*, I.16.2–16.4 pp.56–57. The target need not carry a CW structure
or satisfy a separation axiom. This asserts existence only.

Complete natural-language proof of DAG node
`topo.cw_vertex_based_homomorphism_realization`:

1. Conventions and source domain. Use pi1=FundamentalGroup with its existing group operation
p*q=q.trans p on endpoint-fixed path classes. All path descriptions below are chronological, and
all homomorphisms use this same reverse-chronological group convention on both domain and
codomain. In particular no opposite-group equivalence or sign correction is silently applied to
phi. The chosen point k0 lies in the zero skeleton, so it is the point of a unique original
zero-cell. The finite-walk bridge shows every original vertex connects to this vertex by a
finite original-edge walk; characteristic edge paths then make K1 path-connected.

2. Choose the rooted spanning tree T of K1 and its finite root paths q_v using the spanning-tree
theorem. Orient every original edge e outside T by choosing its characteristic-interval
endpoints u,v. Let gamma_e be q_u, then that oriented edge, then q_v reversed, a loop in K1 at
k0. By the graph-generation child these classes generate pi1(K1,k0), with no global finiteness
hypothesis. Let i:K1→K be inclusion and define theta=phi composed with i_*. Choose for each e a
based representative ell_e in Y of theta([gamma_e]) using quotient-constructor surjectivity.
This is a choice of paths representing the prescribed classes, not a choice of a map inducing
phi.

3. For each oriented complementary edge apply cw_one_cell_loop_disk_realization to ell_e
and its Boolean orientation. This agent-written affine adapter gives a continuous map on the
original maximum-norm one-disk, equal to y0 on its boundary, whose pullback under t↦2t−1
(or t↦1−2t in the reverse orientation) is exactly ell_e(t). Use the constant map y0 on every
tree-edge disk. Define f1:K1→Y by sending vertices to y0 and using these disk maps on edge
interiors. Their boundary values agree with the vertex assignment even for a loop edge.
Interiors are disjoint and each characteristic interior is homeomorphic onto its open cell;
therefore this defines one function on K1 with the prescribed original disk restrictions.
The closed-cell continuity argument in the later gluing step proves f1 continuous in the
inherited topology. The affine adapter supplies only the disk maps and their exact equations;
this global descent and the subsequent fundamental-group computation remain separate steps.

4. The map f1 sends each root path q_v to a constant path. Thus the image of gamma_e is
constant, then ell_e, then constant, which has the same endpoint-fixed class as ell_e. The exact
mapOfEq formula computes these images with f1(k0)=y0. Consequently
(f1)_*([gamma_e])=theta([gamma_e]) for every generator. Since both maps are homomorphisms,
equality extends to every finite word in the generators and their inverses, giving (f1)_*=phi
i_*. Group products in such words retain the reverse chronological convention established above;
no commutativity is used.

5. Two-cell relation, following Hatcher Proposition1B.9 pp90–91 with the canonical circle of
Theorem1.7 pp29–30. For a two-cell characteristic map chi:D2→K, let a:S2→K1 be its
attaching-circle restriction, where D2 is the native closed maximum-norm unit ball in Fin2→Real
and S2 its boundary sphere. Use complex coordinates c(z)(0)=Re z and c(z)(1)=Im z.
Complex.orthonormalBasisOneI.repr identifies these coordinates with the real Euclidean space by
a real linear isometry, so their Euclidean norm is |z|; this is not an isometry to the
maximum-norm Pi space. Continuity of c into the actual finite-coordinate topology follows from
Complex.reCLM, Complex.imCLM and continuous_pi_iff. Its inverse
x↦(x(0):Complex)+(x(1):Complex)*I is continuous by ofRealCLM, coordinate projections, continuous
multiplication and addition; re_add_im and the coordinate identities give the inverse laws.
Restrict these maps to obtain the complex unit circle homeomorphic to the Euclidean unit circle
in that coordinate topology. Now use the written boundary-normalization homeomorphism and its
inverse in Bredon I.16.2–16.4 pp56–57, already expanded in
topo.euclidean_closed_disk_unit_cube_homeomorphism BC3–BC5: the intermediate centered-cube
adapter, before its final affine rescaling A, sends a Euclidean unit vector u to u/N_infty(u).
Its boundary restriction gives beta:Circle≃ₜS2; take s0=beta(1)=(1,0), since both norms of this
coordinate vector are 1. No arbitrary square-perimeter rotation or new disk homeomorphism is
chosen. Define omega(t)=exp(2*pi*i*t), Hatcher’s printed once-around loop
(cos(2*pi*t),sin(2*pi*t)), and v=beta composed with omega on I=[0,1]. Bind this precise omega to
the quotient coercion R→AddCircle1 and AddCircle.homeomorphCircle at period1 using
toCircle_apply_mk and Circle.coe_exp. Quotient coercion and the circle homeomorphism make omega
continuous. For surjectivity, AddCircle.openPartialHomeomorphCoe with period1 and a=0 maps (0,1)
onto the complement of the zero coset; its required DiscreteTopology(zmultiples1) comes from the
existing ordered-group discreteness instance. Thus omega maps (0,1) onto Circle minus {1}, and
omega(0)=omega(1)=1 supplies the remaining point. Since the circle homeomorphism and beta are
injective, v(t)=v(tprime) iff the coset of t-tprime in AddCircle1 is zero.
AddCircle.coe_eq_zero_iff makes this difference an integer. For t,tprime in I, the bounds
-1≤t-tprime≤1 leave only 0,1,-1; these give respectively t=tprime or the endpoint pair {0,1}.
Hence v is surjective with exactly the endpoints as its only nontrivial fibre and with
v(0)=v(1)=s0. Choose a path c in K1 from k0 to a(s0). The loop c followed by a composed with v
followed by c reversed is nullhomotopic in K: v, viewed in D2, is a loop in the contractible
disk, hence endpoint-homotopic to its constant loop, and chi maps this homotopy to K.
Conjugating by c preserves the identity class. Applying phi and the preceding equality
(f1)_*=phi i_* therefore shows the image of this conjugated loop under f1 has class1.

6. Let b=f1 composed with a and yb=b(s0). Conjugation along the image path f1 composed with c is
a multiplicative equivalence between pi1(Y,y0) and pi1(Y,yb), so the preceding identity implies
[b composed with v]=1 at yb. The path-class equality theorem supplies a jointly continuous
endpoint-fixed homotopy J:I×I→Y from b composed with v to the constant loop yb: J(0,t)=b(v(t)),
J(1,t)=yb, and J(u,0)=J(u,1)=yb for every u. The real closed interval I is compact; convert its
compact subset to CompactSpace on its original induced subtype topology. S2 is Hausdorff as a
subtype of the native real coordinate space, so the continuous surjection v from the preceding
step is a quotient map by the compact-to-Hausdorff theorem. Its endpoint-only fibre calculation
and the endpoint laws for J show J(u,t)=J(u,tprime) whenever v(t)=v(tprime). Descend in the
second coordinate to the uniquely defined function H:I×S2→Y satisfying H(u,v(t))=J(u,t). Hatcher
PropositionA.17 pp532–533 proves the needed quotient-times-locally-compact-interval assertion;
the existing quotient-product continuity theorem, with the standard locally compact structure on
I, makes this H jointly continuous, without a separation hypothesis on Y. Surjectivity of v and
the exact defining triangle give H(0,s)=b(s) and H(1,s)=yb for every s in S2. Apply
topo.nullhomotopic_sphere_disk_extension at d=2 to obtain F_chi:D2→Y with F_chi(s)=b(s) on every
native boundary point. This is the zero attaching-class to nullhomotopic attaching-circle step
written in Hatcher1B.9 p91, with its quotient-continuity details expanded from the printed
canonical circle and A.17, not from an arbitrary rotated perimeter or an unbased homotopy with
an assumed fixed trace.

7. Attach all two-cell interiors using their chosen fillings F_chi, keeping f1 on K1. On each
disk boundary the filling is exactly f1 composed with its attaching map; all boundary
identifications therefore agree. At an interior point use the unique inverse characteristic
coordinate. Original open-cell disjointness and the boundary equality make this a function f2 on
K2. Its pullback to each original disk of dimension≤2 is the chosen continuous filling or its
already defined lower-dimensional map. The gluing continuity argument below proves f2
continuous. Choices over arbitrarily many two-cells are pointwise classical choices, and require
no finite collection or local finiteness.

8. For d≥3, suppose fdminus1 is continuous on K^(d−1). Apply the existing higher-cell extension
theorem to every d-cell with lower-skeleton map fdminus1, the surjective covering p:E→Y, and
contractibility of E. Its source proof lifts each simply connected attaching sphere, contracts
its lift, projects the nullhomotopy, and gives a continuous filling on the native maximum-norm
disk with its exact boundary equation. Choose the fillings and define fd on interiors with the
original characteristic inverses; boundary agreement makes it extend fdminus1. The next gluing
step proves continuity. This is Hatcher p91: contractibility is a hypothesis on E and no CW or
Hausdorff hypothesis is imposed on Y. The higher-cell extension proof follows Hatcher Proposition1B.9 p91: the simply connected
attaching-sphere lift, contraction upstairs and projection supply the actual jointly continuous
nullhomotopy, after which topo.nullhomotopic_sphere_disk_extension uses Hatcher Chapter0 p14
closed-bottom/side pasting and Proposition0.16 p15 local disk-prism retraction, with its Bredon
I16.2–16.4 pp56–57 boundary-preserving native maximum-norm adapter, to give the exact disk
boundary equation. This records the current natural-language source proof only; it asserts no
closure of deeper prerequisites or completed Lean proof.

9. Cellwise continuity in the original topology, using Hatcher Appendix p523’s ordinary-map
closed-cell criterion and the original CW closed-set topology (AppendixA.2 p521). At any finite
skeleton B, and finally at K, each original characteristic disk has continuous pullback under
the defined function. For dimension d, the literal disk D_d is the induced subtype of
closedBall(0,1) in Fin d→Real with its maximum norm. FiniteDimensional.finiteDimensional_pi,
then FiniteDimensional.proper_real and isCompact_closedBall give compactness of this exact ball,
including d=0; isCompact_iff_compactSpace supplies CompactSpace D_d. The original characteristic
map is only ContinuousOn this closed ball, as required by the CW structure. Apply
continuousOn_iff_continuous_domRestrict to obtain its continuous restriction chi:D_d→K; restrict
its codomain to its original closed-cell image C_chi using Continuous.subtype_mk, since every
chi(z) lies in that image. This restriction is surjective by the definition of the image and its
target has the inherited Hausdorff subtype topology. The compact-to-Hausdorff theorem therefore
makes chi:D_d→C_chi a quotient map. For a closed subset C of Y, let A be its inverse image under
the defined function on B (regarded as a subset of K). Each characteristic pullback of A is
closed in D_d because that pullback is the inverse image of C under its continuous chosen
filling. The quotient closed-set criterion consequently makes A intersect C_chi closed in C_chi.
The original closed cell is compact in K and hence closed there by Hausdorffness, so the same
intersection is closed in K. The CW closed-cell criterion for the inherited CWComplex B then
makes A closed in K and therefore in B. Here the inherited structure reindexes the selected
original characteristic maps and retains their ambient K topology; no replacement topology is
put on B. The closed-preimage criterion proves continuity on B. At K the same argument uses all
original closed cells. This handles infinitely many cells and nonregular attaching maps:
whole-disk injectivity, arbitrary unions of closed sets and local finiteness are never used.

10. Define f(x)=fd(x) for any finite skeleton Kd containing x; the finite-skeleton exhaustion
gives such d, and the extension property makes this independent of d. Every characteristic disk
has dimension finite and thus has exactly its chosen continuous filling as the pullback of f. The
preceding continuity argument gives continuous f:K→Y, with f(k0)=y0 and restriction f1 on K1. By
the one-skeleton surjectivity child, each class z in pi1(K,k0) is i_*(w) for some w in
pi1(K1,k0). Compute f_*(z)=(f composed with i)_*(w)=(f1)_*(w)=phi(i_*(w))=phi(z). These
equalities are checked on representative paths by the actual fundamental-group map/mapOfEq APIs.
Thus f induces phi on every class, not merely the chosen edge loops.

11. Edge cases. A connected zero-dimensional K with a chosen vertex is a single point and the
constant map realizes its trivial group homomorphism. There may be no complementary edges, no
two-cells, or no cells in any higher dimension; the corresponding choices are empty families and
the restrictions stay compatible. Infinite dimension is handled by each point and each disk
belonging to a finite-dimensional skeleton. No torus, equivalence of groups, inverse map, or
rigidity premise is part of this theorem.
-/
theorem cw_vertex_based_homomorphism_realization
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [ConnectedSpace K] [Topology.CWComplex (Set.univ : Set K)]
    [PathConnectedSpace Y] [ContractibleSpace E]
    (k₀ : K) (hk₀ : k₀ ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) 0 : Set K))
    (y₀ : Y) (p : E → Y)
    (hp : IsCoveringMap p) (hp_surjective : Function.Surjective p)
    (φ : FundamentalGroup K k₀ →* FundamentalGroup Y y₀) :
    ∃ f : C(K, Y), ∃ hf : f k₀ = y₀, FundamentalGroup.mapOfEq f hf = φ := by
  by_cases hφ : φ = 1
  · exact cw_vertex_based_homomorphism_realization_constant k₀ y₀ φ hφ
  · exact cw_vertex_based_homomorphism_realization_nontrivial k₀ hk₀ y₀ p hp hp_surjective φ hφ

end HolomorphicAnosov
