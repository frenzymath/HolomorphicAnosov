import HolomorphicAnosov.Topology.OpenCoverPathReplacement
import HolomorphicAnosov.Topology.Pi1SurjectiveLoopCriterion
import HolomorphicAnosov.Topology.AttachmentPathConnected
import HolomorphicAnosov.Topology.AttachedStripRetraction
import HolomorphicAnosov.Topology.OpenCoverPathSubdivision
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Constructions
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import HolomorphicAnosov.Topology.FiniteHigherCellAttachmentPi1Nonempty

/-! The one-batch higher-cell attachment theorem from Hatcher,
Proposition 1.26(a),(b), pp.50–51, with Lemma 1.15, p.35. -/

namespace HolomorphicAnosov
universe u
open CategoryTheory

/-- A finite simultaneous batch of cells of dimension at least two preserves path
connectedness and induces surjections on the original based fundamental groups.
The input is Mathlib's categorical pushout of coproducts of Euclidean boundary
inclusions. No classical CW structure or separation hypothesis is required.

Source: Hatcher, *Algebraic Topology*, Proposition 1.26(a),(b), pp.50–51,
with the finite open-cover loop argument of Lemma 1.15, p.35.

Natural-language proof. The colimit cocones in `AttachCells` identify its two
coproducts with the disjoint unions of the indexed spheres and disks. Its pushout
therefore identifies Y homeomorphically with the adjunction quotient of X and
those disks along the supplied attaching maps, and identifies f with the original
inclusion. For an empty family the pushout gives a homeomorphism X → Y.
For a nonempty finite family, enumerate the cells and attach them successively.
All attaching maps of this simultaneous batch already have target X, so each
successive attaching map is its composite with the preceding inclusion. The
universal property of successive pushouts identifies the last quotient with the
original simultaneous pushout and preserves the map out of X. This is a finite
reordering within one batch, with no ordering by cell dimension.

At each step path connectedness is preserved: a point represented in a disk joins
a point of its nonempty boundary by a disk path, then joins any point in X using
the attaching map and a path in X. The adjunction quotient is surjective, so this
covers every point of the new space. For surjectivity at any original basepoint,
apply the following one-cell argument and compose the resulting loop maps.

1. First prove the assertion for one attached d-cell, d≥2, as a specialization of Hatcher
Proposition 1.26(a),(b), pp.50–51. Write the cell as the unit closed Euclidean disk D⊂ℝ^d with
attaching map φ:∂D→X and characteristic map into Y. Choose a unit vector θ0 and a path γ in X from
x0 to φ(θ0), using path connectedness. Form exactly the source auxiliary space Z by
adjoining one strip S=I×I to Y, attaching (u,0) along γ(u) and (1,s) along the radial arc
a(s)=(1−s)θ0 in the attached cell. The lower-right corner agrees because γ(1)=φ(θ0); no embedding of
γ or injectivity of φ is required. The unattached left edge starts at x0 and the top edge is free.
Equivalently Z is the adjunction quotient of X ⊔ D ⊔ S by these boundary relations, with its
quotient topology. Its projection q is continuous, surjective and quotient by construction. The maps
below are defined on those original summands, agree on every attaching identification, and therefore
define maps on this Z; the quotient continuity criterion proves continuity of the resulting point
maps.

2. Expand Hatcher’s assertion that the free strip deformation retracts Z onto Y. For (u,s)∈I² put
k=u(1+s) and r(u,s)=(min(k,1),max(k−1,0)). This is a continuous retraction of I² onto its
bottom∪right edges: when s=0 it is (u,0), and when u=1 it is (1,s). The straight homotopy
(1−t)(u,s)+t r(u,s) stays in the square and fixes both attached edges. Use the identity homotopy on
Y. The formulas agree along γ and a, including their common corner; hence they descend to Z. Joint
continuity follows from topo.quotient_map_locally_compact_product_descent_g8 applied to q and the
compact, locally compact homotopy interval I. The endpoint strip formula into Y is γ(k) for k≤1 and
a(k−1) for k≥1, composed with the cell characteristic map in the second branch. The branches agree
at k=1 and are continuous on the closed regions, so the closed-pair pasting theorem and quotient
criterion give a continuous retraction rY:Z→Y. It restricts to the identity on the original Y and
the descended homotopy fixes Y, in particular x0. Thus the original topology on Y is retained: its
inclusion into Z is continuous and has continuous inverse rY on its image.

3. Choose the omitted interior point y=−θ0/2, which lies off the chosen radial arc, as required by
Hatcher p.50. Let A=Z\{q(y)} and B=Z\X. Their actual quotient preimages prove they are open:
q⁻¹(A)=X ⊔ (D\{y}) ⊔ S, and q⁻¹(B) is empty on X, the open disk on D, and I×(0,1] on S. These are
open in the disjoint summands; quotient openness gives open A,B⊂Z and A∪B=Z. This does not require a
separate separation theorem for Z. The restricted maps onto A and B remain quotient by
topo.mathlib_quotient_open_restriction_g8. With the locally compact interval product-descent
theorem, continuous compatible homotopy formulas on their restricted summands therefore give jointly
continuous homotopies in the original subspace topologies of A and B.

4. Expand the source assertion that A deformation retracts onto X, including compatibility with the
strip attachment. For v∈D\{y}, write v=y+ρω with ρ=|v−y|>0 and |ω|=1. The positive boundary distance
on that ray is R(ω)=−⟨y,ω⟩+sqrt(⟨y,ω⟩²+1−|y|²). Since |y|=1/2, the radicand is at least 3/4; this is
a continuous positive function, and 0<ρ≤R(ω). Set F_t(v)=y+((1−t)ρ+tR(ω))ω. It stays in D\{y}, fixes
∂D, and at t=1 lies in ∂D. On the right-edge arc v=a(s)=(1−s)θ0, ρ=3/2−s and R=3/2, so
F_t(a(s))=a((1−t)s). On the strip use (u,s)↦(u,(1−t)s), and on X use the identity. The bottom edge
is fixed and the right edge matches the displayed disk formula exactly; all other quotient
identifications remain fixed. S3 gives a continuous descended homotopy on A, fixing X. At t=1 the
disk maps to X through φ and the strip maps to γ(u); these continuous compatible formulas separately
define the continuous retraction rX:A→X in the original topology by the quotient criterion. Hence
this is a strong deformation retraction, rather than an unverified homotopy of one disk that might
disagree with the strip. In particular A is path connected because X is and each point is joined to
X by its retraction track.

5. Expand Hatcher’s assertion that B is contractible. On the open unit disk put
P(v)=max(0,⟨v,θ0⟩)θ0. Its image is the radial segment [0,1)θ0, which is exactly the part of the
right-edge arc remaining in B. It fixes that segment. The straight homotopy from v to P(v) stays in
the open disk by convexity and agrees with the identity on the attached right-edge arc. Keep the
positive-height strip I×(0,1] fixed during this first stage. At its endpoint the disk has become
that strip edge. Now collapse the strip horizontally by (u,s)↦((1−t)u,s), also moving each disk
endpoint P(v)=a(s) as the corresponding strip point (1−t,s). Lastly move the left-edge height s to
(1−t)s+t/2, which remains positive. These stages agree on the right-edge identifications and at
their successive time endpoints; S3 product descent and closed-pair time pasting make the
concatenated contraction jointly continuous. It contracts B to b=q(0,1/2), fixing b. Thus B is path
connected and its based loop classes at b are trivial, by the named contractible/simply-connected
path leaves.

6. The intersection A∩B is the image of (int D\{y}) ⊔ (I×(0,1]), with the same right-edge arc
identifications. The punctured open disk is path connected for d≥2: given two points, choose ε>0
smaller than both of their distances to y and smaller than 1−|y|. Each point joins y+εω on its ray
from y by a straight radial segment that stays in the convex open disk and avoids y. The ε-sphere
centred at y lies inside that disk, and mathlib.standard_sphere_path_connected_g8 applies because
the real ambient rank is d>1 and ε>0. It joins the two ray endpoints. Every positive-height strip
point joins its right edge by a horizontal segment, and that edge lies in the punctured disk since y
is off the arc. Therefore A∩B is path connected, and it contains b. This verifies the overlap
hypothesis actually used in the source cover argument; no assertion that an arbitrary punctured
space is connected is made.

7. Apply the written Hatcher Lemma 1.15, p.35, to the open cover {A,B} of Z at b. Its proof gives a
finite subdivision of any based loop with each closed subpath in A or B. First merge each maximal
consecutive block of pieces assigned to the same member; a whole merged subpath still lies in that
member. At each remaining change vertex one incident subpath lies in A and the other in B, so that
vertex lies in A∩B. Choose paths in A∩B from b only to these change vertices (the initial and final
vertices are already b), and insert each chosen path followed by its reverse between the adjacent
blocks. The named compact open-cover subdivision and finite subpath-concatenation inputs, together
with the path-homotopy quotient operations, give exactly the source product of loops each based at b
and lying in one cover member. Every B factor is the identity by S5, so every class in π1(Z,b) is
the image of a class in π1(A,b). This is the surjectivity specialization of the printed Proposition
1.26 auxiliary-strip proof. The stronger van-Kampen kernel/presentation assertion is neither assumed
nor needed.

8. Use the left-edge path from x0=q(0,0) to b=q(0,1/2), which lies in A. Basepoint-change
equivalences along this same path commute with A→Z by literal postcomposition of the concatenated
paths. Thus S7 also gives surjectivity at x0. The strong retraction rX and its homotopy from S4 fix
x0, so X→A is a based homotopy equivalence and induces an isomorphism on the actual fundamental
group. Likewise Y→Z and rY from S2 are based homotopy inverses fixing x0. Finally rY composed with
X→A→Z is the original inclusion X→Y, because both retractions fix the original X. The
fundamental-group map composition rule now gives surjectivity of the original inclusion at the
prescribed x0. All basepoint changes and maps use the same path-class multiplication convention, so
no opposite-group or relabelled inclusion is inserted.


Every assertion above is made in the adjunction quotient topology. The explicit
quotient-preimage and quotient-product continuity arguments do not use Hausdorffness
or a CW structure on X. Thus they apply again at each successive attachment.
-/
theorem finite_higher_cell_attachment_pathConnected_pi1_surjective
    {X Y : TopCat.{u}} [PathConnectedSpace X] (f : X ⟶ Y)
    (attachments : HomotopicalAlgebra.AttachCells.{u}
      (fun (n : {n : ℕ // 2 ≤ n}) ↦ TopCat.diskBoundaryInclusion.{u} n.val) f)
    [Finite attachments.ι] :
    PathConnectedSpace Y ∧ ∀ x : X,
      Function.Surjective (FundamentalGroup.map f.hom x) := by
  refine ⟨attachCells_pathConnectedSpace _ f attachments ?_ ?_, ?_⟩
  · intro n
    have hn : 0 < n.val := lt_of_lt_of_le (by decide : 0 < 2) n.property
    refine ⟨ULift.up ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), ?_⟩⟩
    simp
  · intro n
    have : PathConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n.val)) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp (Metric.isPathConnected_closedBall (by norm_num))
    exact Homeomorph.ulift.symm.pathConnectedSpace
  · classical
    intro x
    apply (pi1_surjective_iff_loop_homotopic f.hom x).2
    intro γ
    cases isEmpty_or_nonempty attachments.ι with
    | inl hempty =>
      -- The empty coproducts give a genuine inverse to the attachment map.
      let k : attachments.cofan₂.pt ⟶ X := attachments.isColimit₂.desc
        (CategoryTheory.Limits.Cofan.mk X (fun i ↦ isEmptyElim i))
      have hcomm : attachments.g₁ ≫ 𝟙 X = attachments.m ≫ k := by
        apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext attachments.isColimit₁
        intro i
        exact isEmptyElim i
      let r : Y ⟶ X := attachments.isPushout.desc (𝟙 X) k hcomm
      have hleft : f ≫ r = 𝟙 X := attachments.isPushout.inl_desc _ _ _
      have hright : r ≫ f = 𝟙 Y := by
        apply attachments.hom_ext
        · simp only [← Category.assoc, hleft, Category.id_comp, Category.comp_id]
        · intro i
          exact isEmptyElim i
      have hbase : x = r (f x) :=
        (congrArg (fun h : X ⟶ X ↦ h x) hleft).symm
      refine ⟨(γ.map r.hom.continuous).cast hbase hbase, ?_⟩
      have hloop : ((γ.map r.hom.continuous).cast hbase hbase).map
          f.hom.continuous = γ := by
        ext t
        exact congrArg (fun h : Y ⟶ Y ↦ h (γ t)) hright
      rw [hloop]
    | inr hnonempty =>
      exact finite_higher_cell_attachment_nonempty_pi1_surjective
        f attachments hnonempty x γ

end HolomorphicAnosov
