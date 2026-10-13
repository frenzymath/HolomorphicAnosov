import HolomorphicAnosov.Topology.CWComplex.ZeroSkeletonDiscrete
import HolomorphicAnosov.Topology.CWComplex.CompactGenerationSubspaces
import HolomorphicAnosov.Topology.CWComplex.NormalityFromSkeleta
import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.SuccessorSkeletonNormality
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Separation.Regular

/-!
# Normality and compact generation of Hausdorff CW complexes

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), Proposition 1.2.1,
pp. 22–23, with Appendix A.4.8(iv), pp. 260–261, and A.5.1(iv), p. 274;
Hatcher, Algebraic Topology, Appendix, pp. 521 and 523.
The topology is the supplied topology in Mathlib's classical CW structure.
-/

namespace HolomorphicAnosov.Topology.CWComplex

universe u

/--
Successor normality for the native CW filtration.

Source: Fritsch--Piccinini, *Cellular Structures in Topology* (1990),
Proposition 1.2.1, pp. 22--23, with the closed-cofibration interface in
Appendix A.4.8(iv), pp. 260--261.  The predecessor skeleton is attached to
the coproduct of the closed characteristic disks of the next dimension along
the coproduct of their boundary spheres.  The disk-prism retraction of FP
§1.0, pp. 7--8, gives the homotopy-extension property on each summand; the
coproduct criterion assembles these maps for an arbitrary cell family.  The
ordinary adjunction topology is the native successor-skeleton topology by the
CW final-topology axiom.  Applying A.4.8(iv) to the normal predecessor and
normal disk coproduct proves normality of the successor.

The Lean proof is intentionally isolated here because the current native
`RelCWComplex` interface exposes the skeletal final topology and characteristic
maps separately, but does not export the single adjunction quotient object.
The missing proof must construct that quotient comparison and the coproduct
prism retraction before applying the direct FP A.4.8(iv) normality argument;
it must not use a transitive normality theorem for an unrelated quotient.
-/
theorem normality_of_successor_skeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    [NormalSpace
      ↥(_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)] :
    NormalSpace
      ↥(_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  obtain ⟨h⟩ := successor_skeleton_adjunction_data (X := X) n
  exact normality_of_successor_skeleton_of_adjunction_data n h

/-- Every Hausdorff CW complex, its native subcomplexes, and its finite-dimensional skeleta
are normal and compactly generated in their existing topologies.

`X` carries the CW structure on its whole underlying set. Subcomplex carriers and skeleton
carriers below use their ordinary induced subtype topology. The standard `n`-skeleton consists
of all cells of dimensions at most `n`; it may have infinitely many cells. No nonemptiness,
countability, local finiteness, or bound on the dimensions of `X` is assumed.

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), Proposition 1.2.1,
printed pp. 22–23; Appendix A.4.8(iv), printed pp. 260–261; A.5.1(iv), printed p. 274;
Section 1.0, pp. 7–8, and Appendix A.4 Example 1, p. 251, for the disk-prism retraction.
Hatcher, Algebraic Topology, Appendix A.2, p. 521, and the closed-cell compact-generation
argument, p. 523. Local files: literature/Fritsch-Piccinini-Cellular-Structures-1990.pdf/.txt
and literature/hatcher-at.pdf/.txt.

Complete natural-language proof of `topo.cw_normality_g8`:
CN1. Use the CW topology on X and the inherited topologies on its finite skeleta X^n. The zero skeleton
is discrete; each successor skeleton is the adjunction of all n-disks along their boundary maps,
and X is the union with the final topology of its skeleta, as in FP’s CW filtration definition p22
and Hatcher A.2 p521. In the actual characteristic-map interface, the original skeleton selects
the original lower-dimensional cell indices, the inherited subcomplex retains those same maps and
the ambient topology, and every such subcomplex is closed. Establish the k-space guard
independently of normality: every original closed cell is compact. If a set S has closed
intersection with every compact subset, then S intersect each closed cell is closed in the
Hausdorff ambient space. The CW closed-cell criterion makes S closed. The exact
compactlyGeneratedSpace_of_isClosed_of_t2 constructor therefore proves compact generation of X;
the same argument on each inherited skeleton proves it there. This is Hatcher p523’s written
generation-by-compact-closed-cells argument, not a newly installed topology or an assumption of
normality.

CN2. The zero skeleton is normal because all of its subsets are open and closed; for disjoint closed
sets they themselves are disjoint open neighborhoods. For a successor stage, the attaching space
Y_n is the topological coproduct of its n-dimensional closed disks. Each disk is a metric subtype,
hence completely normal and therefore normal. For two disjoint closed sets in Y_n, restrict to
each disk summand, choose disjoint open separating neighborhoods there, and take their coproduct
unions. Each summand is open and closed in the original coproduct, so these unions are open and
disjoint and contain the prescribed sets; this proves normality for arbitrary cell index sets,
without a product-normality claim. Y_n is Hausdorff by the same summand separation. Each disk is
compact (finite-dimensional proper real space, closed-ball compactness and the induced
CompactSpace conversion), so testing a set on all compact subsets tests it on every disk summand.
The coproduct topology then makes the set closed, and the same compact-test constructor proves Y_n
compactly generated. These are the precise disk-coproduct hypotheses needed to apply the source
adjunction theorem.

CN3. The attaching domain D_n is the coproduct of the disk boundary spheres and is closed in Y_n. The
closed-cofibration guard is the actual written disk-prism retraction in FP Section1.0 pp7–8,
identified as such by AppendixA.4 Example1 p251. For a Euclidean disk point s of norm r and t in
I, its retraction to disk×{0} union sphere×I is (s/(1-t/2),0) when t≤2(1-r), and (s/r,2+(t-2)/r)
when t≥2(1-r). The formulas agree at equality; the first denominator is positive, and the second
region forces r≥1/2, so no zero denominator occurs. The two closed regions cover the disk prism,
closed pasting gives continuity, and the formula fixes the bottom and side. Thus composing any
compatible bottom/side data with this retraction gives a homotopy extension. For the native
maximum-norm disk, use precisely the reviewed Bredon construction in
topo.euclidean_closed_disk_unit_cube_homeomorphism BC3–BC5 BEFORE its final affine rescaling A of
BC6: for n>0 its map H from the Euclidean closed unit disk to the centered cube
D_n={x:N_infty(x)≤1} has H(0)=0 and H(x)=(N_2(x)/N_infty(x))x for nonzero x. It takes the
Euclidean unit sphere N_2(x)=1 homeomorphically to the native maximum-norm sphere N_infty(y)=1.
The coordinates have the same finite-dimensional topology, and D_n is exactly the native
closedBall(0,1) in Fin n→Real, with boundary the native sphere by dist(x,0)=norm(x). Equivalently,
if one uses the provider’s final stated homeomorphism h=A composed with H into Fin n→unitInterval,
undo A by the continuous inverse coordinates z_i↦2*z_i−1; the [0,1]^n codomain is not itself
silently identified with D_n. Conjugate the written Euclidean retraction by H times the identity
of I and its inverse. The resulting retraction has native source D_n×I and target D_n×{0} union
S_n×I, and fixes that bottom and side because H preserves the boundary. For n=0 both disk models
are singletons, the boundary spheres are empty, and BC1 supplies the unique disk homeomorphism
without a maximum over an empty index set. Projection to D_0×{0} gives the required empty-boundary
retraction and hence the closed-cofibration guard in that case. On a coproduct choose these
extensions summand by summand. Each disk-summand times I is open in the ordinary product, so joint
continuity is local on these open pieces. This expands the “easy” coproduct closed-cofibration
property of FP A.4.2(ii) pp251–252 and verifies D_n↪Y_n. Attaching maps are continuous
restrictions of the original characteristic maps into the lower skeleton, and are continuous on
their coproduct by the coproduct criterion.

CN4. Induct on n. The predecessor skeleton is Hausdorff and compactly generated by CN1, and normal by
the inductive hypothesis. CN2–CN3 give normal compactly generated Hausdorff Y_n and its closed-
cofibration boundary domain. Apply normality_of_successor_skeleton to the original skeletal
attachment; its direct FP A.4.8(iv) interface identifies the native final topology with the
existing successor-skeleton topology, not a replacement. Therefore the next skeleton is normal.
Together with the discrete base case this is exactly FP1.2.1’s normality induction through its
A.4.8(iv) input.

CN5. Expand the printed A.5.1(iv) union proof p274. Fix a closed C in X and continuous f:C→I. Construct
compatible continuous f_n:X^n→I extending f on C intersect X^n. At n=0 use interval-valued Tietze
in the normal zero skeleton. At a successor stage the closed subset E_n=X^(n-1) union (C intersect
X^n) of X^n carries the prescription f_(n-1) on the previous skeleton and f on C intersect X^n. On
their intersection these agree by the previous extension equation. Finite closed pasting makes
this prescription continuous, and Tietze in normal X^n gives f_n. Thus f_n restricts exactly to
f_(n-1). Define F(x)=f_n(x) whenever x belongs to X^n; skeletal exhaustion supplies such n and
compatibility makes this independent of n. The original skeletal final topology makes F
continuous: each restriction to X^n is the continuous f_n, or equivalently each original
characteristic disk has its continuous finite-stage pullback. Every x in C lies in a finite
skeleton, so F|C=f. No finite dimension, finite or countable cell set, local finiteness or finite
collection of attachments is used.

CN6. For disjoint closed sets P,Q of X, prescribe 0 on P and 1 on Q inside their closed union. Closed
pasting makes an I-valued continuous map on that union; CN5 extends it to X. Its inverse images of
[0,1/3) and (2/3,1] are disjoint open neighborhoods of P and Q. This is the normality definition,
making explicit the Tietze-converse step used in the source. Compact generation was already proved
independently in CN1. Apply the identical proof to any inherited CW subcomplex or skeleton. Empty
complexes, arbitrary zero-cell sets, empty cell families in a dimension and unbounded dimensions
all satisfy the same argument; only the sequence of dimensions is indexed by natural numbers.
-/
theorem normality_and_compact_generation
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] :
    (NormalSpace X ∧ CompactlyGeneratedSpace X) ∧
    (∀ A : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set X),
      NormalSpace ↥(A : Set X) ∧ CompactlyGeneratedSpace ↥(A : Set X)) ∧
    (∀ n : ℕ,
      NormalSpace ↥(_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) ∧
      CompactlyGeneratedSpace
        ↥(_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)) := by
  obtain ⟨hcompact, hcompactSub, hcompactSkel⟩ :=
    compactlyGeneratedSpace_of_cw_subspaces (X := X)
  suffices hnormal : NormalSpace X by
    let : NormalSpace X := hnormal
    refine ⟨⟨hnormal, hcompact⟩, ?_, ?_⟩
    · intro A
      exact ⟨A.closed.isClosedEmbedding_subtypeVal.normalSpace, hcompactSub A⟩
    · intro n
      have hs := (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)).closed
      exact ⟨hs.isClosedEmbedding_subtypeVal.normalSpace, hcompactSkel n⟩
  apply normalSpace_of_normal_skeleta
  -- The compatible extension argument handles the infinite union. It remains
  -- to establish normality at each finite skeletal stage by the direct successor interface.
  intro n
  induction n with
  | zero =>
      let : DiscreteTopology ↥(_root_.Topology.RelCWComplex.skeleton
        (Set.univ : Set X) 0 : Set X) := zero_skeleton_discrete Set.univ
      change NormalSpace ↥(_root_.Topology.RelCWComplex.skeleton
        (Set.univ : Set X) 0 : Set X)
      refine ⟨fun s t _ _ hst ↦ ?_⟩
      exact ⟨s, t, isOpen_discrete s, isOpen_discrete t, subset_rfl, subset_rfl, hst⟩
  | succ n ih =>
      -- The zero stage now has its native discrete topology. Only the
      -- normality-preserving successor attachment remains to be supplied.
      exact normality_of_successor_skeleton n

end HolomorphicAnosov.Topology.CWComplex
