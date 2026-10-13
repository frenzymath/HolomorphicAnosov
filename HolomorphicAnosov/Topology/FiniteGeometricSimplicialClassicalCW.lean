import HolomorphicAnosov.Topology.FiniteGeometricCellIndexProperties
import HolomorphicAnosov.Topology.AffineSimplexCombinationEquiv
import HolomorphicAnosov.Topology.ConvexBodyCharacteristicMap
import HolomorphicAnosov.Topology.GeometricFaceCharacteristicAttachment
import HolomorphicAnosov.Topology.FiniteCWULiftCharacteristicMaps
import HolomorphicAnosov.Topology.SimplicialFaceCharacteristicMaps
import HolomorphicAnosov.Topology.StandardCoordinateSimplexCharacteristic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Classical CW structures on finite geometric simplicial complexes

Source: Hatcher, Algebraic Topology, section 2.1, pp. 104, 107, and Proposition A.2,
pp. 520--521; literature/hatcher-at.pdf and literature/hatcher-at.txt.
The existing Euclidean carrier retains its subtype topology. Its native characteristic
sphere image is specified by proper subfaces, without identifying it with an ambient frontier.
-/

namespace HolomorphicAnosov

open Set Topology _root_.Topology

universe u

/-- The original face-indexed classical CW structure of a finite geometric simplicial complex,
together with its canonical transport to any universe by the up/down homeomorphism.

Source: Hatcher, section 2.1, pp. 104, 107, Proposition A.2, pp. 520--521,
and Corollary A.8, p. 527. The following is the complete natural-language proof of
DAG node `topo.finite_geometric_simplicial_classical_cw_g8`, including its explicit
source-to-Mathlib characteristic-map and universe-transport expansions.

Fix the given finite P in E=EuclideanSpace Real(Fin N), let hP:P.faces.Finite, and define
cell(d)={s:Finset E // s in P.faces and s.card=d+1}; retain exactly these face subtypes throughout
the construction. For every face s, Geometry.SimplicialComplex.nonempty_of_mem_faces supplies
s.Nonempty. Thus the empty finite set is not a face; this checks the nonempty-face convention
without requiring that P.faces itself be nonempty. Nonemptiness is direct field projection: for
hs:s∈P.faces, (P.isRelLowerSet_faces hs).1 is s.Nonempty, using the inherited
PreAbstractSimplicialComplex field (pinned AlgebraicTopology/SimplicialComplex/Basic.lean:51–56 and
Analysis/Convex/SimplicialComplex/Basic.lean:71–72); the same supplied membership proof is used, and
no nonempty-complex hypothesis is added. For the GIVEN finite geometric Q with hQ:Q.faces.Finite,
cell_Q(d)={s:Finset E // s in Q.faces and s.card=d+1} is a subset of the SAME finite face set and
hence a finite subtype; the finite image B=Finset.card image Q.faces has a Nat upper bound M, so any
cell_Q(d) with d>=M would give d+1<=M<=d, contradiction, and eventually_atTop supplies the EXACT
eventual-empty field with threshold M, while card_eq_one identifies degree0 cells precisely with
singleton faces and empty Q admits threshold0, with no bound on ambient vertices, replacement index
family or nonempty-complex assumption (Hatcher Section2.1 pp.103-104,107; pinned
Basic/Finite/Defs.lean185-200, Set/Finite/Basic.lean505-507,574-576, Lattice.lean409-414,
AtTopBot/Basic.lean79 and Finset/Card.lean694-696).

For fixed d, the set A_d of finite subsets s with s in P.faces and s.card=d+1 is a subset of P.faces
by conjunction elimination. Apply Set.Finite.subset to obtain A_d.Finite. Set.Finite is
definitionally finiteness of its subtype, so this gives exactly Finite (cell d). The definitional
conversion is Basic/Finite/Defs.lean:185,200.

Let B=Finset.card '' P.faces. Set.Finite.image makes B finite, and Set.Finite.bddAbove in Nat
supplies M with every member of B at most M. For any s in P.faces, the image witness s gives s.card
in B and hence s.card<=M. The upper-bound theorem permits B empty.

For d>=M a purported c:cell d gives c.val.card=d+1 and c.val.card<=M. Thus d+1<=M<=d, contradicting
d<d+1. This function cell d -> False constructs IsEmpty (cell d). In particular equality d=M is
included.

Apply the reverse direction of Filter.eventually_atTop to threshold M and the preceding IsEmpty
witnesses. The predicate is exactly fun d:Nat => IsEmpty (cell d), supplying the constructor's
eventual-emptiness input.

At d=0 the cardinality condition is s.card=1. Finset.card_eq_one is equivalent to existence of x
with s={x}. Forward substitution transports s in P.faces to {x} in P.faces; reverse substitution and
the same equivalence construct the zero-cell. If {x}={y}, singleton membership gives x=y. Thus zero-
cells are precisely singleton faces, or equivalently vertices by unfolding P.vertices. Here
P.vertices={x | {x} in P.faces} by its literal definition at geometric Basic.lean139-143, so the
zero-cell/vertex identification requires no extra vertex-set hypothesis.

If P.faces is empty, the face-membership component of any c:cell d is false. Therefore every cell
type is empty and threshold zero works. The bottom geometric complex has definitionally empty faces,
so this proves the empty-complex specialization without any ambient nonemptiness or dimension
restriction.

For each original index (d,s) with s in P.faces and s.card=d+1, the finite face subtype has
cardinality d+1 by Fintype.card_coe. Use the inverse of Fintype.equivFinOfCardEq to choose
o_s:Fin(d+1) equiv s once; if a vertex order is already specified, use exactly its face ordering
instead. The following construction uses this fixed o_s and its original vertices throughout. Fix
the GIVEN ordering o:Fin(d+1) equiv s, put v_j=(o j).val and A=affineSpan Real (s:Set E). Define
lambda(u)_0=1-sum_i u i and lambda(u)_(i.succ)=u i on U=Fin d->Real. Splitting the finite sum into
index0 and successors gives sum_j lambda(u)_j=1. Conversely, dropping coordinate0 from any
normalized family recovers it uniquely by that equation. Applying
affineCombination_eq_linear_combination with this exact normalization gives the literal E-valued
formula F(u)=v_0+sum_i u i smul (v_(i.succ)-v_0), equivalently sum_j lambda(u)_j smul v_j. The
ordering identifies the vertex range with s; no ordering on ambient E is needed. For a given face s
of cardinality k+1 with its fixed ordering v_j, normalized lambda0=1-sum_i u_i and
lambda(i.succ)=u_i give the literal affine map F(u)=v0+sum_i u_i•(v_(i.succ)-v0); finite affine-span
representations extended by0 give surjectivity and independence on THIS s gives injectivity, so the
full intrinsic affine-span map and its affine inverse are continuous using the explicit vertex
inhabitant and finite-dimensional normed-torsor instances, and restricting that same F gives beta_s,
strict barycentric intrinsic interior and zero-outside-t subface membership for EVERY t subset s,
including t=empty, with no ambient-interior or union-independence premise (Hatcher Section2.1
pp.103-104,107; pinned Combination.lean423-426,916-922, Independent.lean830-834,
AddTorsor.lean58-62, FiniteDimension.lean116-128 and Intrinsic.lean61-76).

Use mem_affineSpan_iff_eq_affineCombination on the ordered family v:Fin(d+1)->E. The normalization
above puts F(u) in A. Conversely x in A has finite index subset J and weights w with sum over J
equal1 and x equal its affine combination. Extend w by0 to all Fin(d+1): wbar(j)=w(j) if j in J,
otherwise0. Its full sum and weighted vector sum are the original ones. Dropping coordinate0 gives
u_i=wbar(i.succ); normalization determines wbar0=1-sum u, so the SAME displayed F(u)=x. This proves
surjectivity onto the whole affine-span subtype, without convexity, positivity or an unstated span-
rank hypothesis.

For normalized families representing the SAME x, transfer their weights through o to functions
a,b:E->Real by zero outside s. Their scalar sums over the SAME s are both1 and their weighted vector
sums coincide. P.indep hs is exactly AffineIndependent Real (Subtype.val:s->E);
eq_of_sum_eq_sum_subtype at Independent.lean830-834 therefore gives a(v)=b(v) for EVERY v in s.
Reindexing back through o gives equality at every Fin(d+1) index, and dropping coordinate0 yields
u=u'. This proves injectivity of F and uniqueness of its barycentric coordinates even on the full
affine span, with no nonnegative-weight premise and no independence assumption on a union of faces.

Package F as an affine map U->A: its linear part L(u)=sum_i u i smul (v_(i.succ)-v_0) lies in
A.direction because every vertex lies in A and the direction is closed under real linear
combinations; direct finite-sum distribution gives F(u+w)=L(w)+v F(u). The chosen point v_0 belongs
to A by affine-span membership, so (v_0,membership) explicitly gives Nonempty A. Thus A inherits its
Euclidean subtype metric and NormedAddTorsor A.direction A by AddTorsor.lean58-62; the empty affine-
subspace instance is never used. FiniteDimensional Real U is the finite-Pi instance and
FiniteDimensional Real A.direction is the submodule instance from finite-dimensional E
(Defs.lean95-101,131-134). AffineEquiv.ofBijective at AffineEquiv.lean205-212 packages the proved
bijective affine map without changing its forward formula. Apply
AffineMap.continuous_of_finiteDimensional at FiniteDimension.lean116-128 separately to it and its
AFFINE inverse: Real is a complete nontrivially normed field, both actual carriers have the required
inherited normed-torsor metrics, and each source direction is finite-dimensional. This yields the
full homeomorphism U->A and its continuous inverse while preserving U's maximum norm and A's
Euclidean subtype topology.

Finset.mem_convexHull' on the SAME vertex finset gives K=convexHull Real s exactly by nonnegative
weights on s summing1 with the specified weighted vector sum. Reindexing through o identifies these
with lambda0=1-sum u>=0 and lambda(i.succ)=u i>=0, hence with Delta={u | forall i,0<=u i and sum
u<=1}. Therefore the whole F homeomorphism has F image Delta={x:A | x.val in K}. Restrict that SAME
homeomorphism to the two subtypes and reassociate {x:A | x.val in K} with {x:E | x in K}, using that
K is contained in A. Both reassociation maps are identity on underlying E points, their inverse
equations are subtype extensionality, and Continuous.subtype_mk with continuous subtype projection
gives both continuities. This produces beta_s on the literal convex-hull subtype, not a new choice
of map or topology.

On the native maximum-norm U, interior Delta={u | forall i,0<u i and sum u<1}. At d0 U is singleton,
Delta=univ and the strict formula is vacuous coordinate positivity with0<1. At d>0, for strict u
take the positive minimum a of finitely many positive coordinates and delta=1-sum u>0. Choose r>0
with r<a and d*r<delta. The exact positive-radius pi_norm_lt_iff gives abs(v i-u i)<r throughout an
r-ball, so every v i>0 and sum v<sum u+d*r<1. Conversely an interior r-ball at u in Delta excludes u
i=0 by subtracting r/2 in that coordinate, and excludes sum u=1 by adding r/2 in any coordinate when
d>0; both single-coordinate perturbations have norm<r by the SAME finite-Pi strict theorem. Thus all
inequalities are strict. The nonnegative-radius finite-Pi theorem includes d0 without a Nonempty(Fin
d) assumption.

Use affineSpan_convexHull to identify affineSpan Real K with the SAME A. Apply
Homeomorph.image_interior at Defs.lean309-310 to the WHOLE F:U equiv_t A and the subset Delta; it
gives F image (interior Delta)=interior {x:A | x.val in K}. Including A into E gives
intrinsicInterior Real K by its exact definition at Intrinsic.lean61-76. The strict-coordinate
calculation and lambda0=1-sum u make this precisely strict positivity of all unique barycentric
weights. Restricting F to Delta before taking interior would use the wrong topology; this proof uses
interior in the entire affine-span subtype, including d0 and d<N.

Let t subset s and x in K, with its unique normalized nonnegative s-weights. If x in convexHull t,
Finset.mem_convexHull' supplies nonnegative normalized t-weights; extend them by0 to s. Weighted
sums and scalar sums are unchanged, so independence on the SAME s identifies those extended weights
with x's s-weights, proving zero outside t. Conversely if the s-weights vanish outside t, deleting
exactly zero terms preserves sum1 and x; the restricted weights satisfy Finset.mem_convexHull' on t.
For t=empty this would force sum1=0, so both hull membership and all-weights-zero are false: no
nonempty-subface hypothesis has been silently added. For a zero weight at v_j take t=s.erase v_j;
the sum1 and nonnegativity force some positive weight on a different vertex, so t is nonempty, and
v_j in s makes it proper. Downward closure of the geometric complex gives t in P.faces. No positive-
support partition of all points or sphere-image theorem is used.

At d0 the sole normalized coordinate is1, F is the map from the singleton Fin0->Real to the
singleton affine span of the given vertex, K and intrinsicInterior K are that SAME singleton, and no
zero-weight point exists. In ambient dimension N0 the only possible nonempty affinely independent
face is similarly a singleton; the chosen face premise already supplies its actual point. For d<N
every interior assertion remains in A, never in ambient E. If P has no faces the face-quantified
statement has no instance, and no point or map into an empty affine span is chosen. This constructs
the family F_s and its exact restriction beta_s once for the chosen face orderings; use precisely
them in the subsequent disk, characteristic-map and cell-image arguments.

Before defining the geometric characteristic family, carry out the following standard parameter-
space construction for every natural d, independently of P or its faces. Work on V=Fin d -> Real
with its ORIGINAL finite-Pi maximum norm and define Delta={u | (forall i,0<=u i) and sum_i u i<=1},
I={u | (forall i,0<u i) and sum_i u i<1}, D=closedBall 0 1, U=ball 0 1 and S=sphere 0 1. Coordinate
evaluation is continuous and induction using Continuous.add gives continuity of the finite
coordinate sum, including the empty sum. isClosed_le makes each defining inequality closed; their
finite intersection makes Delta closed. Weighted interpolation with coefficient in[0,1] preserves
nonnegativity and the sum bound, so Delta is convex. For u in Delta, each0<=u i<=sum_j u j<=1, so
each abs(u i)<=1 and pi_norm_le_iff_of_nonneg gives norm(u)<=1, also at d0. Thus Delta is contained
in D and is metrically bounded: for any u,v in Delta, dist(u,v)<=norm(u)+norm(v)<=2, equivalently
boundedness of the closed unit ball and subset monotonicity (pinned MetricSpace/Bounded.lean73-75).
No affine face, embedding or geometric simplicial complex is assumed. On the original V_d=Fin
d→Real, the coordinate simplex Delta_d is closed, convex and norm-bounded by1, has directly proved
interior I_d given by positive coordinates and sum<1 and a positive barycenter (singleton/univ at
d0), so the exact gauge theorem gives one ambient h_d:V_d≃ₜV_d with h_d(I_d)=ball0 1,
h_d(Delta_d)=closedBall0 1 and h_d(frontier Delta_d)=sphere0 1; restricting h_d.symm gives the
required q_d on the CLOSED disk, while rho_d(u)=u/max(1,norm u) is globally continuous, fixes that
disk and has rho_d inverse-image ball0 1=ball0 1, with nonempty proper barycentric zero-face images
and d0 included (Hatcher Section2.1 pp.103-104, PropositionA.2 p.521; pinned
GaugeRescale.lean191-197 and finite-Pi norm/continuous primitives).

Prove interior Delta=I directly on this STANDARD V. When d>0 and u in I, let a be the positive
minimum of its finitely many positive coordinates and delta=1-sum u>0; choose0<r<a and d*r<delta. If
norm(v-u)<r, the finite-Pi strict norm theorem gives abs(v i-u i)<r for each i, so every v i>0 and
sum v<=sum u+d*r<1. Thus the r-ball lies in Delta. Conversely a point of interior Delta has all
defining weak inequalities. If a coordinate is zero, subtract r/2 in that single coordinate inside
an interior r-ball, producing a negative coordinate; if sum=1, add r/2 in any coordinate (d>0),
producing sum>1. Both norm bounds follow coordinatewise from pi_norm_lt_iff with positive radius.
This excludes equality and proves strictness. The point b_i=1/(d+1) has positive coordinates and
sum=d/(d+1)<1, so I is nonempty. At d0 V is the singleton zero function, Delta=I=univ and b is its
sole point. Since Delta is closed, frontier Delta=Delta minus I=Z, where at least one of
lambda0=1-sum u or lambda(i.succ)=u i is zero. The remaining nonnegative normalized weights have
nonempty positive support (sum1) and that support is proper; conversely vanishing at a missing
vertex gives exactly a proper barycentric face. This standard-coordinate proof needs no geometric-
face coordinate theorem.

Apply exists_homeomorph_image_interior_closure_frontier_eq_unitBall to E=V and s=Delta with the
preceding convexity, metric boundedness and nonempty interior. Closedness rewrites closure
Delta=Delta, and the direct interior/frontier formulas give ONE ambient homeomorphism h:V equiv_t V
with h image I=U, h image Delta=D and h image Z=S. GaugeRescale.lean160-181 translates an interior
point before applying the origin-centered gauge construction, so there is no missing0-neighborhood
hypothesis; the exact theorem at191-197 assumes neither Nontrivial V nor finite dimensionality.

The image equality h image Delta=D and injectivity/surjectivity of h give h.symm(D)=Delta and the
corresponding pointwise membership equivalences for I/U and Z/S. Restrict h.symm to the subtypes D
and Delta to obtain q:D equiv_t Delta; restrict h for its inverse. Continuity of both restrictions
follows from the ambient continuous maps and subtype topology, and both inverse identities are the
original h inverse identities. Thus q maps the open-ball locus of D onto I and its sphere locus onto
Z, with the SAME ambient h. For d0 all these restrictions are the unique maps between singleton
types and S=Z=empty.

Define M(u)=max(1,norm(u)) and rho(u)=(1/M(u)) smul u. Norm continuity follows from
ContinuousOn.norm on the continuous identity over univ and continuousOn_univ. To reuse the existing
exact min primitive, use the REAL identity max(1,norm(u))=-min(-1,-norm(u)); continuous scalar
multiplication by -1, continuous min and multiplication by -1 again prove M continuous. M>=1 gives
M>0 and nowhere-zero denominator. Continuous.div makes1/M continuous and Continuous.smul makes rho
continuous. Norm_smul and positivity give norm(rho(u))=norm(u)/M(u)<=1. If norm(u)<=1 then M=1 and
rho(u)=u; if norm(u)>=1 then M=norm(u)>0 and norm(rho(u))=1. Consequently rho inverse-image U=U:
inside U it is fixed, and outside U its norm is1, hence never strictly below1. Boundary points are
fixed. This is a global continuous retraction onto the SAME maximum-norm disk, including u0 and d0;
no inverse of rho on all of V is claimed.

Continuous.subtype_mk and the proved norm bound give R:V->D, u maps to (rho(u),membership). Define
Q=q composed with R:V->Delta, with underlying V-valued map Qbar=h.symm composed with rho. Continuity
is inherited by composition. On D the clamp is identity, so Q agrees with the SAME q. Its
closed/open/sphere images are respectively Delta/I/Z: forward membership follows the ambient h
equivalences, and for every v in the corresponding target choose u=h(v) in D/U/S, where rho(u)=u,
then Qbar(u)=v. Finally Qbar inverse-image I=rho inverse-image U=U. No geometric beta, face
ordering, ambient Euclidean embedding or extra carrier choice enters this standard-simplex
assertion.

For d0 check the entire result independently: V is singleton of norm0, D=U=Delta=I=univ, S=Z=empty,
the sole barycentric weight is1, M=1 and rho=id. Choose the ambient h0=id, whose subtype restriction
is q0; Q0 is its unique total extension. All image/preimage/continuity/inverse assertions hold, and
the union of proper nonempty barycentric faces is empty. For all d the construction uses the native
finite-Pi maximum norm, without replacing it by the Euclidean L2 norm. For each d choose the one
ambient h from this exact existence theorem, and form its stated inverse restriction q_d and the
explicit rho_d above once; use this same q_d and rho_d for every face of dimension d in the
characteristic-map proof. These are constructed outputs, not additional geometric hypotheses.

For each index (d,s) with s in P.faces and s.card=d+1, let V_d=Fin d -> Real, D_d={u:V_d // u in
Metric.closedBall 0 1}, Delta_d={u:V_d // every coordinate is nonnegative and their sum is at
most1}, X={x:E // x in P.space}, C_s={x:X | x.val in convexHull Real(s:Set E)}, and O_s={x:X | x.val
in intrinsicInterior Real(convexHull Real(s:Set E))}. Here a homeomorphism onto C_s means onto its
subtype {x:X // x in C_s}. Use exactly the previously chosen face ordering o_s and the explicitly
constructed beta_s:Delta_d homeomorph {x:E // x in convexHull Real(s:Set E)}, together with the same
q_d:D_d homeomorph Delta_d and continuous rho_d from the preceding standard-disk construction. No
ordering, affine map or parameterization is chosen again, and no new premise is introduced. The hull
of s lies in P.space because P.space is the union of the hulls of its faces and hs supplies the
union index. Define T_s from the ambient hull subtype to C_s by y |->
((y.val,hull_subset_space(y.property)),y.property), with inverse x |-> (x.val.val,x.property). Both
inverse laws are subtype extensionality. Both maps are continuous by continuous subtype projection,
iterated inverse images under composition, and Continuous.subtype_mk. Compose T_s with the supplied
beta_s and q_d to obtain q_s : closedBall 0 1 homeomorph C_s. Its inverse first applies T_s.symm,
then beta_s.symm, then q_d.symm: q_s.symm = q_d.symm o beta_s.symm o T_s.symm. For each face s with
s.card=d+1, choose its specified vertex ordering (or a cardinality enumeration if none is
prescribed), the corresponding beta_s : Delta_d homeomorph the hull subtype, and the EXISTING q_d :
closed maximum-norm disk homeomorph Delta_d; the explicit carrier inclusion T_s and total clamp give
chi_s(u)=(T_s(beta_s(q_d(rho_d(u))))).val with its inverse q_d.symm composed beta_s.symm composed
T_s.symm on C_s and zero outside, so restricted inverse laws, closed/open images, induced-target
inverse continuity and the SAME proper-face sphere equation follow without a whole-space
homeomorphism onto the simplex (Hatcher Section2.1 pp.103-104, PropositionA.2 p.521; pinned
PartialEquiv.lean116-133, CWComplex/Classical/Basic.lean135-162 and ContinuousOn.lean105-113).

First every x in O_s has a strict barycentric preimage by the preceding affine-coordinate
construction's full intrinsic-interior image equality, and the image lies in the hull; thus O_s
subset C_s. Let J_d={z:closedBall 0 1 | z.val in ball 0 1}. The disk witness maps J_d to the strict
coordinate simplex. The coordinate witness maps that strict simplex to the actual intrinsic interior
of the geometric hull, and the carrier inclusion preserves vectors. Consequently q_s '' J_d={x:C_s |
x.val in O_s}. For x in O_s, choose a J_d preimage of (x,hxC) from this equality and apply q_s.symm
to its image identity. The underlying point of q_s.symm(x,hxC) therefore lies in the open ball.

Use the supplied rho_d(u)=(max 1 ||u||)^(-1) smul u and its closed-ball membership to define
R_d(u)=(rho_d(u),membership). Continuous.subtype_mk makes R_d continuous. Put
chi_s(u)=(q_s(R_d(u))).val. Composition of continuous maps makes chi_s globally continuous and hence
continuous on the closed ball. On that ball rho_d(u)=u, so subtype extensionality gives
chi_s(u)=(q_s(u,hu)).val=(T_s(beta_s(q_d(u,hu)))).val. This equality includes all boundary points
and is the exact datum for the boundary proof.

Define g_s(x) by a dependent membership test: if hx:x in C_s then (q_s.symm(x,hx)).val, otherwise
zero in Fin d -> Real. Classical decidability supplies the test. The zero fallback exists without
any inhabitant of X. On C_s the formula is exactly Subtype.val composed q_d.symm composed
beta_s.symm composed T_s.symm; every domain is the corresponding subtype, and no unbound h_s or
ambient whole-space homeomorphism is used. Proof irrelevance makes the true-branch formula
independent of the chosen membership proof.

Set toFun=chi_s, invFun=g_s, source=ball 0 1 and target=O_s. For u in the source, u is in the closed
ball and q_s(u) is in O_s by the open-cell image identity, proving map_source'. For x in O_s, g_s(x)
is the underlying point of q_s.symm(x), which lies in the open ball, proving map_target'. For u in
the source, the true branch of g_s(chi_s(u)) equals the underlying point of q_s.symm(q_s(u,hu)),
hence u. For x in O_s, clamp fixes the point g_s(x) in the open ball, so chi_s(g_s(x)) is the
underlying point of q_s(q_s.symm(x,hxC)), hence x. These are all fields of PartialEquiv at
Logic/Equiv/PartialEquiv.lean:116-133. The source is open: radius 1-dist(u,0)>0 around any source
point remains in the unit ball by the triangle inequality, also supplied by Metric.isOpen_ball.

On the subtype C_s, the membership branch is always true, so C_s.domRestrict g_s equals Subtype.val
o q_s.symm. This composite is continuous. Apply continuousOn_iff_continuous_domRestrict to conclude
ContinuousOn g_s C_s. The inclusion O_s -> C_s is continuous by subtype projection and
Continuous.subtype_mk. Composing the previous restricted inverse with this inclusion is exactly
O_s.domRestrict g_s; applying the same iff proves ContinuousOn g_s O_s. This is the literal CW
inverse-continuity field because e_s.symm=g_s and e_s.target=O_s. No openness of O_s in X and no
continuity of g_s off C_s is assumed.

The closed-ball image lies in C_s because on that ball chi_s is q_s followed by projection. Every x
in C_s has the preimage (q_s.symm(x,hx)).val in the closed ball, and the homeomorphism right-inverse
law proves its image equals x. This proves the closed image equality. The source image lies in O_s
by map_source'; every x in O_s has the source preimage g_s(x) by map_target' and right_inv'. This
proves the open image equality. For the same chi_s agreeing on the closed maximum-norm disk with
Subtype.val∘T_s∘beta_s∘q_d, a sphere point maps to barycentric coefficients lambda≥0 summing to1
with at least one zero coefficient, so t={v in s |0<lambda(v)} is nonempty (otherwise the sum is0),
proper (the zero vertex is omitted), and the exact subface criterion puts its image in convexHull
Real t; conversely a point in any nonempty proper subface hull has, by the same beta_s inverse and
subface criterion, a zero coefficient at a vertex of s outside t, and the same q_d sphere-image
equality supplies its sphere preimage, so the characteristic sphere image equals precisely this
proper-subface union, with t a face by the supplied complex lower-set field and t.card−1<d
from1≤t.card<s.card=d+1; filtering s.ssubsets by Nonempty gives the finite indexing family, and for
d0 the source sphere in Fin0→Real is empty and1≤t.card<1 rules out any nonempty proper subface,
without an ambient-frontier assertion (Hatcher§2.1 pp.103–104 and PropositionA.2(ii) p.521; pinned
Hull.lean70, Finset/Card.lean315, Powerset.lean160 and Pseudo/Defs.lean448).

An empty P.space admits no face: a face is nonempty, one of its vertices is in its convex hull, and
that hull is in P.space. Therefore the map family over actual face indices is vacuous; no total
function from the always-inhabited Fin d -> Real into an empty carrier is constructed. For d=0, the
coordinate space has exactly the zero function with norm zero, so the open and closed unit balls are
univ and the unit sphere is empty. The face has one vertex, Delta_d and its strict-coordinate subset
both consist of the unique point, and C_s=O_s is that vertex. The forward map is constant at it and
the inverse is the unique function into Fin 0 -> Real, so all laws and continuity claims hold
without a Nontrivial assumption. Choose this family once over all face indices and use precisely it
in every subsequent CW field and ULift transport; the selected total forward maps need no point of
an empty X because there are then no indices.

For each x:X={x:E // x in P.space}, carry out the following pointwise positive-support calculation;
it also applies to ANY supplied geometric Q without requiring Q.faces finite. Apply mem_space_iff to
x.property to choose s in P.faces and z = (x : E) in convexHull Real s. Finset.mem_convexHull'
yields w : E -> Real, nonnegative on s, with sum w = 1 and weighted sum z. The preceding affine-
coordinate construction's uniqueness identifies the restriction to s with its barycentric
coordinates; no coordinate theorem is repeated. For any supplied geometric complex K, its inherited
isRelLowerSet_faces field gives (K.isRelLowerSet_faces hs).2 hts ht, hence t∈K.faces from
hs:s∈K.faces, hts:t⊆s and ht:t.Nonempty; unfolding K.space=⋃s∈K.faces,convexHull (s:Set E) turns
membership into exactly a face-and-hull witness, and conversely inserts such a witness into that
union (pinned AlgebraicTopology/SimplicialComplex/Basic.lean:51–56 and
Analysis/Convex/SimplicialComplex/Basic.lean:77–82,97–98). For ANY supplied geometric complex Q on
the same Euclidean E and x in Q.space, mem_space_iff supplies s in Q.faces and nonnegative
normalized vertex weights w with weighted sum x; t=s.filter(fun v=>0<w(v)) is nonempty because the
sum is1, omitted weights vanish, and nonempty downward closure gives t in Q.faces, while the scalar
and E-valued sum_subset identities preserve sum1 and the SAME x, so positive normalized weights on t
and its exact coordinate theorem give x in intrinsicInterior Real(convexHull Real t), including
singleton t and ambient dimension0, with no renormalization, changed carrier or global-finiteness
assumption (Hatcher Section2.1 pp.103-104,107 and PropositionA.2(i) p.521; pinned
Convex/Combination.lean415-420, Finset/Basic.lean202-206 and Intrinsic.lean89-90).

Define t = s.filter (fun v => 0 < w(v)), using classical decidability. Finset.mem_filter gives t
subset s and positivity on t. If v in s is omitted, not (0 < w(v)) and 0 <= w(v) imply w(v) = 0. If
t were empty all weights on s would be zero and their sum would be zero, contradicting sum w = 1.
Thus t.Nonempty. These are explicit finite-membership, linear-order and finite-sum-zero arguments,
including the empty-set guard.

Apply P.down_closed to s in P.faces, t subset s, and t.Nonempty. Its exact conclusion is t in
P.faces, on the original ambient vertices.

Use Finset.sum_subset with codomain Real to discard omitted zero weights: sum over t of w is 1. Use
it again with codomain E and summand w(v) smul v; omitted terms vanish by zero_smul, so the
restricted weighted sum is still z. Therefore the restricted weights are positive and normalized,
with no renormalization or change of point. Finset.mem_convexHull' in the reverse direction also
supplies z in convexHull Real t.

Set d = t.card - 1. Nonemptiness implies t.card > 0, hence t.card = d + 1; choose a finite ordering
if requested by the coordinate theorem interface. Apply the preceding affine-coordinate
construction's strict-positive genuine intrinsicInterior criterion to t and the normalized
representation just constructed. It gives z in intrinsicInterior Real (convexHull Real t). If its
presentation uses affineCombination, Finset.affineCombination_eq_linear_combination at sum one is
the exact representation bridge. In the singleton case the only coefficient is 1 and
intrinsicInterior_singleton confirms membership, so no NeZero cell-dimension guard is inserted.

Define C(t) = {y : X | (y : E) in intrinsicInterior Real (convexHull Real t)}. The preceding
membership is exactly x in C(t), retaining the same x : X. Equivalently the same-value inclusion of
the intrinsic-interior subtype has this image: intrinsicInterior_subset and mem_space_iff with
witness t justify its values in X, and equality of underlying E values gives subtype equality. The
union of C(t) over faces covers X by the constructed witness. Empty X is vacuous; N = 0 and
singleton supports are covered without a positive-dimensional premise.

For each pair of the supplied geometric P faces s,t and common intrinsic-interior point x, use the
following argument, which also works for ANY geometric Q without Q.faces finite. For x in both
intrinsic interiors, intrinsicInterior_subset places x in both convex hulls. The exact geometric
complex intersection theorem places x in convexHull Real (u : Set E), where u=s intersect t is the
finset intersection. This uses each face's own intrinsic interior; the affine spans need not agree.
For ANY supplied geometric Q and a point x in both intrinsic interiors of face hulls s,t,
intrinsicInterior_subset and the exact hull-intersection equality give x in convexHull Real(s
intersect t), whose nonnegative normalized weights extend by0 to each original face with the same
scalar sum1 and vector sum x; uniqueness using Q.indep hs on s identifies these with its strictly
positive interior weights, so s has no vertex outside t, and the SAME comparison using Q.indep ht on
t gives t subset s, hence s=t, while face equality and cardinal successor cancellation identify
dependent Sigma cell indices across dimensions, including singleton faces, without independence of s
union t, equal affine spans, ambient interiors or a global-finiteness assumption (Hatcher Section2.1
pp.103-104,107 and PropositionA.2(i) p.521; pinned geometric Basic.lean91-95 and
Independent.lean830-834).

Finset.mem_convexHull' yields c:E->Real nonnegative on u, with sum_u c=1 and sum_u c(v)*v=x. The
values off u are irrelevant. This API applies to any finite u; if u were empty the scalar equality
would already contradict 0!=1.

Define b(v)=c(v) for v in u and b(v)=0 otherwise. Partition each finite sum over s, respectively t,
into vertices in u and outside u. Terms outside u are zero and terms inside u equal the original c
terms. Thus sum_s b=sum_t b=1 and sum_s b(v)*v=sum_t b(v)*v=x. This is only finite-sum arithmetic;
it assumes no affine independence of s union t. Equivalently apply the existing exact sum_subset
primitive on u subset s and u subset t, first with Real codomain and then with E codomain; every
omitted scalar and zero_smul term is0, so the normalization and vector identities hold on each face
separately.

The existing intrinsic-coordinate theorem gives strictly positive weights a on s, scalar sum 1 and
vector weighted sum x. If written in Fin(s.card) coordinates, define a:E->Real by reindexing on s
and zero outside s; each vertex appears exactly once. Apply P.indep hs and
AffineIndependent.eq_of_sum_eq_sum_subtype to a and b on s. They agree at each v in s. Any v in s
outside t has b(v)=0, contradicting a(v)>0. Therefore s subset t.

Use the same coordinate theorem for t and compare its positive weights with the same b using P.indep
ht and weighted-sum uniqueness on t. A vertex of t outside s would have a positive coefficient equal
to zero. Hence t subset s. Finset inclusion antisymmetry gives s=t.

Define O_s on X=P.space by underlying-point membership in intrinsicInterior Real (convexHull Real
s). A common subtype point of O_s and O_t gives exactly the two ambient membership hypotheses, so
distinct faces have disjoint O_s and O_t. For dependent indices (d,s),(e,t) with face cardinalities
d+1,e+1, equality s=t gives d=e by successor cancellation and then equality of the subtype and sigma
indices. Consequently disjointness holds across all dimensions. Singleton weights equal 1>0, so
dimension zero is included; no strict upper bound below 1 is used.

Use mem_space_iff and positive barycentric support for coverage, affine uniqueness for pairwise
disjointness, and zero-coordinate support plus down_closed for finite lower-dimensional
characteristic frontiers. For the supplied finite geometric P and the SAME chosen characteristic
family chi_s, the positive-support calculation supplies every x in P.space in the intrinsic open
cell O_t of a nonempty face t, while O_t is contained in P.space by the same geometric carrier; the
disjointness calculation says a point in O_s intersect O_t forces s=t, and the characteristic
PartialEquiv sphere-image field gives exactly the finite nonempty proper-subface hull union, with
1<=t.card and t.card-1<d, including the empty d=0 sphere. These existing source conclusions directly
supply the original coverage, pairwise-disjointness and lower-boundary fields with the same maps,
topology, maximum norm and intrinsic interiors (Hatcher Section2.1 printed pp.104,107;
PropositionA.2(i)-(ii) p.521).

For the fixed finite geometric P, set X={x:E // x in P.space}, K_s=convexHull Real (s:Set E),
C_s={x:X | x.val in K_s}, and F={s:Finset E // s in P.faces}. Here C_s is a SET in X; its subtype is
a different topological space. Keep the induced Euclidean topology on X. The map v: X->E is
Subtype.val, inducing by Topology.IsInducing.subtypeVal and continuous by continuous_subtype_val. X
inherits T2Space from E (Hausdorff.lean363). For s in P.faces, convexHull_subset_space gives K_s
subset P.space. The equality range v=P.space follows in both directions by projecting or
constructing the pair (y, membership proof). Thus the range guard K_s subset range v is explicit for
every face (Constructions.lean365-380; SimplicialComplex/Basic.lean78-86). The next steps prove
compactness, both ambient/subtype closed-set tests, and the same characteristic-disk test for this
single P; no second complex or replacement topology is introduced.

The vertex set of the Finset s is finite. Apply Set.Finite.isCompact_convexHull over Real to make
K_s compact. Apply the inducing-preimage theorem to Subtype.val, using the proved range containment,
to make C_s compact in X. Apply IsCompact.isClosed in the inherited Hausdorff X to obtain IsClosed
C_s. This is a compactness argument for the original subtype and never assumes that arbitrary
continuous preimages preserve compactness.

Also apply Set.Finite.isClosed_convexHull to K_s in E. Its inverse image C_s is closed because its
complement is the continuous inverse image of the open complement of K_s. This provides the direct
finite-convex-hull closedness specialization requested in the brief; exact continuous-preimage API
is IsClosed.preimage at Topology/Continuous.lean:188-190.

Interpret hP as finiteness of the subtype F. If x : X, Geometry.SimplicialComplex.mem_space_iff
applied to x.property supplies s in P.faces with x.val in K_s, hence x in C_s. Thus union_s C_s =
univ. Elementwise, x in A implies x in A intersect C_s for one such s, and x in any A intersect C_s
implies x in A. Therefore A = union_(s : F) (A intersect C_s). No relative-interior or frontier
theorem is used.

If A is closed, every A intersect C_s is closed: its complement is the union of the two open
complements (IsClosed.inter). Conversely, if each intersection is closed, apply
isClosed_iUnion_of_finite to the finite type F and rewrite the union by the previous identity. This
proves the closed-set test on X without changing its topology.

Let i_s:C_s->X be the subtype inclusion and B_s={z:C_s | z.val in A}. The prior IsClosed C_s gives
IsClosed.isClosedEmbedding_subtypeVal i_s (Constructions.lean402). Elementwise, i_s image B_s=A
intersect C_s: a subtype witness proves one direction and x in C_s supplies the pair for the other.
Apply IsClosedEmbedding.isClosed_iff_image_isClosed (Maps/Basic.lean835-839) to obtain IsClosed B_s
iff IsClosed (A intersect C_s) in X. In particular the relative closedness input is on the subtype
B_s, while the finite-union argument uses the ambient sets A intersect C_s; this exact equivalence
connects them. The forward ambient-to-subtype implication is also continuous inverse image, and
neither direction presupposes that A itself is closed.

Take the SAME characteristic family already constructed for this P. For j : cell d, restrict its
forward map to the maximum-norm closed-ball subtype D_d. The resulting q_(d,j) is continuous by
ContinuousOn.domRestrict and has range exactly C_j by the preceding explicit characteristic
construction's closed-ball image equality. No extension property outside the disk is required and no
closed-set test is assumed.

Let V_d=Fin d->Real with its original product maximum norm, D_d={z:V_d // z in Metric.closedBall 0
1}, and q_(d,j):D_d->X the SAME disk restriction from the preceding step. Real is proper and
pi_properSpace gives ProperSpace V_d for the finite index Fin d, so isCompact_closedBall and
isCompact_iff_compactSpace give CompactSpace D_d (ProperSpace.lean38-55,117-136; Compact.lean1052).
This uses the native maximum norm directly, including d=0, without replacing V_d by a EuclideanSpace
with another norm; the existing finite-dimensional properness input remains a valid alternative. For
arbitrary A:Set X, put B=q_(d,j) inverse-image A as a SET in D_d. Continuity of q_(d,j) and T2Space
X yield Continuous.isClosedMap (Hausdorff.lean682-684), hence IsClosed B implies IsClosed (q_(d,j)
image B) in X. The set identity q_(d,j) image B=A intersect range q_(d,j)=A intersect C_s holds
without injectivity: one direction projects the witness; the other uses membership in the range to
choose a disk witness z and then z in B from q_(d,j) z in A. Conversely IsClosed A implies IsClosed
B by IsClosed.preimage and the same disk continuity. Combined with the preceding exact
relative/ambient equivalence, this proves the disk closed-set test for each fixed face.

Every face is nonempty and hence occurs at d = s.card - 1 in the dimension-indexed cell family; the
card equation is (s.card - 1) + 1 = s.card because 0 < s.card. Consequently closedness of all disk
preimages gives closedness of A intersect C_s for every face. The already proved finite-union
argument yields IsClosed A. This proves the full characteristic-disk closed-set equivalence for the
actual family.

If there are no faces then mem_space_iff makes X empty, every A empty and closed, and both tests
vacuous. A singleton face has d = 0; Fin 0 -> Real and its closed unit ball are singletons and the
compact-disk proof still applies. Nothing here requires positive ambient dimension, connectedness,
ambient interior, or a nonempty sphere. Replacing each map image by C_s in the established
implication gives the exact CWComplex.closed' field at Basic:159-160 for C = univ; mkFinite
independently derives that field and is not a dependency.

Fix E = EuclideanSpace Real (Fin N), X = {x : E // x in P.space} with inherited topology, C =
Set.univ : Set X, and cell d = {s : Finset E // s in P.faces and s.card = d+1}. All these carriers
live in Type 0, satisfying mkFinite's same-universe requirement. Reuse the preceding face-index
calculation's finite_cell and eventually_isEmpty_cell conclusions with this exact family. For X={x:E
// x in P.space} in Type0 and the same face-indexed characteristic PartialEquivs chi, finite face
cardinalities give finite(cell d) and an eventual empty bound, equality of underlying faces
identifies dependent Sigma indices, the intrinsic-open-cell disjointness gives pairwise disjointness
across all degrees, every nonempty proper subface t supplies cell(t.card-1) with t.card-1<d and the
same closed-image witness, and mem_space_iff gives the exact closed-image union; these are precisely
the arguments of CWComplex.mkFinite, which internally produces finite lower-frontier witnesses and
the closed-set field by bounded finite unions, and its identical selected cell family gives
CWComplex.Finite by its two inherited fields, including empty P and d0 (Hatcher PropositionA.2
p.521; pinned Classical/Finite.lean188-232,263-308).

Select the preceding explicit characteristic construction's family chi d i once on the exact subtype
X. If initially indexed at s.card-1, transport the map and all fields along s.card=d+1 to dimension
d. Pass its PartialEquiv, open-ball source, closed maximum-norm-ball continuity and inverse
continuity on target. Keep its exact open, closed and sphere image equations for this same family.

For distinct sigma indices (d,i) and (e,j), their underlying faces cannot agree: face equality plus
cardinality gives d+1=e+1, hence d=e, and Sigma.subtype_ext gives equality of the sigma indices.
Rewrite the open map images as the preceding explicit characteristic construction's relative-
interior sets. Distinct-face disjointness then proves Set.PairwiseDisjoint over univ of the full
dependent sigma type, including different dimensions. For the supplied finite geometric P and the
SAME chosen characteristic family chi_s, the positive-support calculation supplies every x in
P.space in the intrinsic open cell O_t of a nonempty face t, while O_t is contained in P.space by
the same geometric carrier; the disjointness calculation says a point in O_s intersect O_t forces
s=t, and the characteristic PartialEquiv sphere-image field gives exactly the finite nonempty
proper-subface hull union, with 1<=t.card and t.card-1<d, including the empty d=0 sphere. These
existing source conclusions directly supply the original coverage, pairwise-disjointness and lower-
boundary fields with the same maps, topology, maximum norm and intrinsic interiors (Hatcher
Section2.1 printed pp.104,107; PropositionA.2(i)-(ii) p.521).

For u on the d-sphere, the fixed characteristic boundary equality supplies a nonempty proper subface
t of i.val with chi d i u in C_t. Put m=t.card-1. Positivity gives t.card=m+1, so t determines j_t :
cell m. Finset.card_lt_card and i.val.card=d+1 give m<d. The exact closed-image identity places chi
d i u in chi m j_t '' closedBall 0 1; insert m, m<d and j_t in the nested lower-dimensional union.
This proves the MapsTo argument named mapsTo_iff_image_subset. For d=0 the sphere is empty by
Metric.sphere_eq_empty_of_subsingleton, agreeing with absence of nonempty proper subfaces.

The finite frontier witness generated by RelCWComplex.mkFinite is I m = Set.finite_univ.toFinset on
cell m. Each finite_cell m makes this legal, and Set.Finite.mem_toFinset says every j : cell m
belongs to I m. Thus the union over j in I m equals the union over all j used above. The additional
restriction m<d makes the dimensions finite as well. This exactly realizes the existential Pi m,
Finset (cell m) field; it assumes neither a finite ambient E nor a finite Nat.

For the closed-cell union, one inclusion into univ : Set X is immediate. For x : X,
Geometry.SimplicialComplex.mem_space_iff chooses s in P.faces with x.val in convexHull Real s.
Geometry.SimplicialComplex.nonempty_of_mem_faces gives positive cardinality. Put d=s.card-1 and form
j_s : cell d using s.card=d+1. The characteristic closed-image equality puts x in chi d j_s ''
closedBall 0 1, proving the reverse inclusion and the exact union' equation. The open-cover sibling
is not needed for this field.

Check the internally generated closed' field directly: an eventual-emptiness bound B reduces the
closed-cover union to dimensions d<B. For any A subset X, distribution of intersection over the
cover writes A as the union over d<B and j : cell d of A intersect chi d j '' closedBall 0 1. If
each term is closed, two finite-union closedness applications give IsClosed A. This is exactly the
proof in RelCWComplex.mkFinite:215-232. The empty relative base is closed, is disjoint from every
open cell, and drops out of both union equations. Thus weak_topology_and_closed_cells is not a
direct input to this constructor.

Apply Topology.CWComplex.mkFinite with the preceding exact arguments, obtaining a particular
CWComplex on Set.univ of X. For the identical CWComplex instance installed by mkFinite with the
supplied cell and characteristic-map family, its cell types are the original cell n, so construct
CWComplex.Finite directly as {eventually_isEmpty_cell := the supplied eventual-emptiness proof,
finite_cell := the supplied degreewise finiteness proofs}; these are exactly the two inherited
fields of RelCWComplex.Finite, with no choice of a replacement instance, topology or maps (pinned
Classical/Finite.lean:41–69,263–308). The output cell/map family and image equations are preserved
by the constructor and its relative-to-absolute conversion. At Classical/Finite.lean263-287 the
definition applies RelCWComplex.mkFinite with D=empty, disjointBase and isClosedBase given by the
empty-set identities, then uses RelCWComplex.toCWComplex. That conversion literally copies cell and
map, and its relative roundtrip is rfl at Classical/Basic.lean181-194; hence the selected cell types
and every total forward/inverse characteristic function are preserved. The exact
CWComplex.finite_mkFinite at Classical/Finite.lean289-308 installs this identical instance and has
precisely the two displayed fields, agreeing with the direct structure proof above. Only the
original TopologicalSpace X is an implicit constructor hypothesis; the finite-union closed' proof
already supplied by its relative body requires no additional Hausdorff, closed-carrier or weak-
topology premise.

If P.faces is empty then mem_space_iff makes P.space and X empty, and every cell d is empty. Define
the family by eliminating its impossible cell index; no element of the empty X is selected. All
indexed fields are vacuous, eventual emptiness holds with bound zero, and union' equates the empty
union with univ of the empty type. Zero-dimensional nonempty faces separately have singleton
open/closed balls and empty sphere, so no negative-dimensional cell is introduced.

Let X be the original subtype |P| and let C=Set.univ : Set X. Use the particular CWComplex C and its
Finite instance assembled in the preceding steps; write I n and p n i for exactly its cell types and
total characteristic PartialEquivs. These are the explicitly constructed closed-disk maps above,
with their typed witnesses and every original image equation, so no additional geometric premise is
supplied. For the actual X:Type0 put Y=ULift.{u,0} X, J n=ULift.{u,0}(I n), and C_up=ULift.down
preimage C=Set.univ : Set Y. Thus Y and J n are in Type u, matching the exact cell-universe
requirement of CWComplex, while each characteristic source Fin n -> Real remains in Type0. More
generally a carrier X:Type v and indices I n:Type v use Y=ULift.{u,v} X and J n=ULift.{u,v}(I n),
both in Type(max u v). The degree-preserving equivalence (n,j) |-> (n,j.down) between the dependent
Sigma index types has inverse (n,i) |-> (n,ULift.up i); these are inverse by up/down cancellation
and preserve distinct total indices across dimensions. Project source_eq, continuousOn,
continuousOn_symm, pairwiseDisjoint', mapsTo', closed', union' and the two finiteness fields from
this identical instance (pinned Classical/Basic.lean135-162, Classical/Finite.lean41-69). For
Y=ULift.{u} X, replace each cell index I n by J n=ULift.{u}(I n) and each total map p n i by (p n
j.down).transEquiv Equiv.ulift.symm; canonical up/down cancellation preserves all original source,
closed/open/sphere images, inverse-continuity, pairwise-disjointness, finite lower-cell witnesses,
weak topology, union and finiteness fields on the inherited topology (Hatcher PropositionA.2 p.521;
pinned Classical/Basic.lean135-162, Classical/Finite.lean41-69, Homeomorph.ulift and
PartialEquiv.transEquiv).

Use the canonical Homeomorph.ulift : Y equiv_t X, whose maps are down and up and whose topology is
the inherited topology induced by down. Define p_up n j = (p n j.down).transEquiv Equiv.ulift.symm.
The transEquiv definition gives source equal to the old source, target equal to down preimage old
target, forward up composed with p, and inverse p.symm composed with down on the whole respective
types. Its inverse laws are the old laws followed by up/down cancellation, so no new inverse or off-
source values are chosen.

For every source set S, membership with witness z proves p_up n j image S = up image (p n j.down
image S) = down preimage (p n j.down image S). Apply this to the unchanged maximum-norm ball,
closedBall and sphere. The old closed/open image equations become the up-images of the original
closed simplex and intrinsic relative interior. Apply up to the original sphere/proper-face union
equality, retaining precisely each original proper-subface witness. The same pointwise operation
preserves agreement with the chosen disk map on the whole closed disk. These are characteristic-
boundary equations, not ambient-frontier assertions.

Use global continuity of up and ContinuousOn.comp with outer domain univ to transfer forward
continuity on the closed ball. For inverse continuity, restrict the continuous down map to down
preimage old target; its MapsTo into the old target is exactly membership in that preimage. Compose
with the original inverse-continuity field using ContinuousOn.comp. This proves continuity only on
the required target and does not assert global continuity of the original partial inverse.

Two distinct total lifted cell indices have distinct projections by the explicit Sigma equivalence
defined above. Any common point of their lifted open cells projects into both original open cells by
the preceding exact image identity, contradicting the original pairwise-disjointness field. This
verifies pairwise disjointness across all degrees, not merely within one degree.

Project the original mapsTo' field at (n,i); it supplies a family F(m) of finite lower-cell witness
sets, equivalently the cellFrontier_subset_finite_closedCell conclusion with characteristic sphere
image. For an original finite lower-frontier witness F(m), define F_up(m)=F(m).map
((Equiv.ulift.symm : I m equiv J m).toEmbedding). Finset.mem_map_equiv identifies membership of k in
F_up(m) with membership of k.down in F(m). An old sphere-image witness m<n, t in F(m), and w in the
closed m-ball gives the new witness m<n, up t in F_up(m), and the same w after applying up to the
characteristic-map equality. Thus mapsTo' retains the exact finite witness family and all lower-
degree inequalities.

For A subset C_up with closed intersections with all new closed cells, set B=up preimage A, which is
a subset of C. For each old cell i, B intersect oldClosedCell(n,i) equals up preimage (A intersect
newClosedCell(n,up i)) by the image identity. ULift.isClosed_iff makes these old intersections
closed. The original protected closed' field gives IsClosed B; the reverse ULift.isClosed_iff
implication gives IsClosed A. This fills weak topology on the inherited lifted topology without an
additional Hausdorff premise. The same equivalence preserves the already-closed geometric cells.

If y belongs to C_up, the original union' applied to y.down supplies n,i and z in the closed ball
with p n i z=y.down. The lifted index up i and same z witness y in the new cell union, using
up(y.down)=y. Conversely every new closed-cell witness projects into C. Thus the new union is
exactly C_up, which is univ when C is univ. The identical witness calculation transports any
supplied open-cell union. Assemble the explicit fields into CWComplex C_up with cell=J and map=p_up.

Finite.of_equiv applied to the original finite type I n and Equiv.ulift.symm gives Finite(J n),
matching the existing ULift finite instance. If I n is empty then any j:J n contradicts emptiness
via j.down; apply this implication on the original eventual set to retain its same dimension bound.
These two fields instantiate CWComplex.Finite for this selected new structure. An empty carrier
requires no chosen point; dimension-zero spheres remain the original empty spheres; u=0 uses the
same canonical up/down construction. No nonemptiness, connectedness, or new dimension assumption is
introduced. Every transported image equation remains conditional on its original equation for the
chosen p; this transport proves no omitted construction of characteristic maps.
-/
theorem finite_geometric_simplicial_classical_cw (N : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (hP : P.faces.Finite) :
    let X := {x : EuclideanSpace ℝ (Fin N) // x ∈ P.space}
    ∃ cw : CWComplex (univ : Set X),
      letI : CWComplex (univ : Set X) := cw
      CWComplex.Finite (univ : Set X) ∧
      ∃ index : ∀ d : ℕ,
        {s : Finset (EuclideanSpace ℝ (Fin N)) // s ∈ P.faces ∧ s.card = d + 1} ≃
          RelCWComplex.cell (univ : Set X) d,
        (∀ (d : ℕ)
          (s : {s : Finset (EuclideanSpace ℝ (Fin N)) // s ∈ P.faces ∧ s.card = d + 1}),
          RelCWComplex.closedCell (C := (univ : Set X)) d (index d s) =
            {x : X | x.val ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin N)))} ∧
          RelCWComplex.openCell (C := (univ : Set X)) d (index d s) =
            {x : X | x.val ∈ intrinsicInterior ℝ
              (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin N))))} ∧
          RelCWComplex.cellFrontier (C := (univ : Set X)) d (index d s) =
            {x : X | ∃ t : Finset (EuclideanSpace ℝ (Fin N)),
              t.Nonempty ∧ t ⊂ s.val ∧
                x.val ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin N)))}) ∧
        ∃ cwUp : CWComplex (univ : Set (ULift.{u} X)),
          letI : CWComplex (univ : Set (ULift.{u} X)) := cwUp
          CWComplex.Finite (univ : Set (ULift.{u} X)) ∧
          ∃ liftIndex : ∀ d : ℕ, ULift.{u} (RelCWComplex.cell (univ : Set X) d) ≃
              RelCWComplex.cell (univ : Set (ULift.{u} X)) d,
            ∀ (d : ℕ) (i : ULift.{u} (RelCWComplex.cell (univ : Set X) d)),
              RelCWComplex.map (C := (univ : Set (ULift.{u} X))) d (liftIndex d i) =
                (RelCWComplex.map (C := (univ : Set X)) d i.down).transEquiv
                  (Homeomorph.ulift : ULift.{u} X ≃ₜ X).symm.toEquiv := by
  classical
  let X := {x : EuclideanSpace ℝ (Fin N) // x ∈ P.space}
  suffices hnative :
    ∃ cw : CWComplex (univ : Set X),
      let : CWComplex (univ : Set X) := cw
      CWComplex.Finite (univ : Set X) ∧
      ∃ index : ∀ d : ℕ,
        {s : Finset (EuclideanSpace ℝ (Fin N)) // s ∈ P.faces ∧ s.card = d + 1} ≃
          RelCWComplex.cell (univ : Set X) d,
        (∀ (d : ℕ)
          (s : {s : Finset (EuclideanSpace ℝ (Fin N)) // s ∈ P.faces ∧ s.card = d + 1}),
          RelCWComplex.closedCell (C := (univ : Set X)) d (index d s) =
            {x : X | x.val ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin N)))} ∧
          RelCWComplex.openCell (C := (univ : Set X)) d (index d s) =
            {x : X | x.val ∈ intrinsicInterior ℝ
              (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin N))))} ∧
          RelCWComplex.cellFrontier (C := (univ : Set X)) d (index d s) =
            {x : X | ∃ t : Finset (EuclideanSpace ℝ (Fin N)),
              t.Nonempty ∧ t ⊂ s.val ∧
                x.val ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin N)))}) by
    obtain ⟨cw, hfinite, index, himages⟩ := hnative
    let : CWComplex (univ : Set X) := cw
    let : CWComplex.Finite (univ : Set X) := hfinite
    exact ⟨cw, hfinite, index, himages, finite_cw_ulift_characteristic_maps.{u, 0} X⟩
  let cell (d : ℕ) :=
    {s : Finset (EuclideanSpace ℝ (Fin N)) // s ∈ P.faces ∧ s.card = d + 1}
  obtain ⟨hfinite, hempty⟩ := finite_geometric_cell_index_properties N P hP
  have hcell_nonempty : ∀ d (s : cell d), s.1.Nonempty := by
    intro d s
    exact P.nonempty_of_mem_faces s.2.1
  have hface_cell (s : Finset (EuclideanSpace ℝ (Fin N))) (hs : s ∈ P.faces) :
      cell (s.card - 1) := by
    have hpos : 0 < s.card := Finset.card_pos.mpr (P.nonempty_of_mem_faces hs)
    exact ⟨s, hs, by omega⟩
  suffices hcharts :
      ∃ χ : ∀ d, cell d → PartialEquiv (Fin d → ℝ) X,
        (∀ d s, (χ d s).source = Metric.ball 0 1) ∧
        (∀ d s, ContinuousOn (χ d s) (Metric.closedBall 0 1)) ∧
        (∀ d s, ContinuousOn (χ d s).symm (χ d s).target) ∧
        (univ : Set (Σ d, cell d)).PairwiseDisjoint
          (fun ds ↦ χ ds.1 ds.2 '' Metric.ball 0 1) ∧
        (∀ d s,
          χ d s '' Metric.closedBall 0 1 =
            {x : X | x.1 ∈ convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin N)))} ∧
          χ d s '' Metric.ball 0 1 =
            {x : X | x.1 ∈ intrinsicInterior ℝ
              (convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin N))))} ∧
          χ d s '' Metric.sphere 0 1 =
            {x : X | ∃ t : Finset (EuclideanSpace ℝ (Fin N)),
              t.Nonempty ∧ t ⊂ s.1 ∧
                x.1 ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin N)))}) by
    obtain ⟨χ, hsource, hcont, hinv, hdisjoint, himages⟩ := hcharts
    obtain ⟨hattach, hcover⟩ := geometric_face_characteristic_attachment N P
      (fun d s ↦ χ d s) (fun d s ↦ (himages d s).1) (fun d s ↦ (himages d s).2.2)
    let cw := CWComplex.mkFinite (univ : Set X) cell χ hempty hfinite
      hsource hcont hinv hdisjoint hattach hcover
    refine ⟨cw, ?_, (fun d ↦ Equiv.refl (cell d)), ?_⟩
    · exact CWComplex.finite_mkFinite (univ : Set X) cell χ hempty hfinite
        hsource hcont hinv hdisjoint hattach hcover
    · intro d s
      exact himages d s
  obtain ⟨χ, hsource, hcont, hinv, hdisjoint, himages⟩ :=
    simplicial_face_characteristic_maps N P
  exact ⟨χ, hsource, hcont, hinv, hdisjoint, himages⟩

end HolomorphicAnosov
