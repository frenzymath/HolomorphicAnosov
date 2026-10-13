import HolomorphicAnosov.Topology.CairnsJordanOpenRegions
import HolomorphicAnosov.Topology.CairnsTwoRegionsPackaging

/-!
# The two complementary regions of an arbitrary Jordan curve

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
Section 5, pp.866–867; preliminaries 2(A,B)/Theorem 2.1, p.860, and 4(D), pp.865–866.
The final component classification and closure identity are proved here; the
geometric construction remains in CairnsJordanOpenRegions.
-/

namespace HolomorphicAnosov

/--
Let c⊂Complex be the image of any topological embedding of S1. Its complement has exactly two
nonempty connected components: a bounded open component Q and an unbounded open component E, with
frontier(Q)=frontier(E)=c and closure(Q)=Q∪c. In particular a bounded complementary component
exists. No regularity beyond topological embedding is required.

Source: Cairns, An Elementary Proof of the Jordan-Schoenflies Theorem (1951), Section5 pp.866–867:
extreme-contact polygon, two applications of Lemma5.1, Lemma5.2 and final recombination;
preliminary2(A,B)/Theorem2.1 p.860 and cell-amalgamation4(D) pp.865–866. Authoritative
literature/cairns-jordan-schoenflies-1951.pdf physical2,7–9 and corresponding text read directly on
2026-10-07. The full round-disk crosscut conclusion supplies the cut-region coverage and boundary
traces used below.

Natural-language proof:

Choose two distinct points of c and rotate orthonormal coordinates so their ordinates differ.
Compactness of c gives maximum M and minimum m with M>m, attained at distinct P1=(a1,M), P2=(a2,m).
Choose a rectangle [L,R]×[B,T] strictly containing c. Replace a short interval of its top edge by
the two segments from (a1−δ1,T) through P1 to (a1+δ1,T), and similarly replace a short bottom
interval by a triangular notch with tip P2; choose the widths inside (L,R). The top notch lies in
y≥M and the bottom in y≤m, so their edges are disjoint, each meets c only at its tip, and the
vertical sides miss c. The resulting p is a simple polygon with p∩c={P1,P2}, even when other curve
points share an extreme ordinate. More explicitly its bounded geometric region is {L<x<R,
ℓ(x)<y<u(x)}, where ℓ≤m<M≤u are the lower and upper piecewise affine notch graphs. Every vertical
section joins the horizontal strip m<y<M; hence this region is connected, open and bounded, and its
boundary is exactly p. It contains c except P1,P2. This construction uses only compact extrema and
finite affine geometry, and does not define an exterior of c before separation is proved.

Apply the polygon Schoenflies theorem to p. Denote its bounded component by D and its unbounded
component by O. The explicit connected bounded notch region in JC1 is D: it is closed as well as
open relative to the complement of p and contains the indicated vertical sections. Obtain a
homeomorphism F:closure(D)→closedBall(0,1) sending p to S1; it sends D onto the open ball because
closure(D)=D∪p. In any such closed-cell parametrization, a crosscut transports legitimately: the map
restricted to the original open cell and the open ball is a homeomorphism between ambient-open
subsets of the plane, so preimages of cut components are ambient-open and connected. Apply
Homeomorph.image_closure on the closed-cell subtypes. The transported relative closures are compact
and therefore closed in the plane; relative density gives that they are also the ambient closures.
For each open transported component, its ambient frontier is consequently its closed-cell closure
minus that component, namely the transported cut arc plus the appropriate boundary arc. This
establishes the exact closure/frontier transport used in both cuts, without an invariance-of-domain
inference from an arbitrary embedded disk.

The embedding of the circle gives two compact simple arcs c1,c2 joining P1 to P2, with disjoint
interiors and union c. Their interiors lie in D. Apply the round-disk crosscut theorem to F(c1), and
transport it using JC2. Thus D\c1° is exactly the disjoint union of two nonempty connected
ambient-open disk cells. The connected set c2° is disjoint from c1 and lies in precisely one of
them; call that cell B1 and the other A1. Label the two polygon boundary arcs J1,J2 from P1 to P2 so
frontier(A1)=c1∪J1 and frontier(B1)=c1∪J2. Their closures are the corresponding cells plus these
full boundaries, meet exactly in c1, and admit closed-disk homeomorphisms with the stated boundary
maps. The supplier gives all of these conclusions, including coverage; none is inferred from
separation alone.

Use the closed-disk parametrization of closure(B1) supplied by the first cut. Its boundary is
exactly c1∪J2, a simple curve; its two boundary arcs between P1,P2 are c1 and J2. The map sends B1
onto the open disk since B1 is open and closure(B1)=B1∪frontier(B1). The second curve arc c2 is
therefore a legitimate crosscut of this disk. Apply the same round-disk crosscut theorem and JC2
transport to get B1\c2°=A ⊔ A2, with nonempty connected ambient-open A,A2, frontier(A)=c1∪c2=c and
frontier(A2)=c2∪J2. Their compact closures are their interiors plus those full boundaries. In
particular closure(A)=A∪c is bounded. These conclusions hold at the shared endpoints as well as on
the open arcs.

Substitute the second exact cut partition into the first: D is the disjoint union of
A1,A,A2,c1°,c2°. Consequently D\c=A1 ⊔ A ⊔ A2. In Cairns’s two final amalgamations, recombining A1
with A along c1° and then adding A2 along c2° restores exactly D as a set, with outer boundary p
already identified by the polygon theorem. This complement conclusion requires no new abstract-disk
pasting claim or separate seam-openness theorem: those geometric matters are included in the full
cut-region conclusions used in JC3–JC4. There cannot be an additional region hidden inside D because
the two crosscut partitions are exhaustive. Outside closure(D) there is the single polygon exterior
O.

Set Q=A and E=(Complex\c)\A. The exact partitions give E=O∪A1∪A2∪(p\{P1,P2}); also
E=Complex\closure(A), so E is open. To identify its connectivity without a seam assertion, for every
q∈p\{P1,P2} choose a small open ball Bq disjoint from the closed set closure(A)=A∪c. Since
q∈frontier(O)=p, every such ball meets the connected exterior O. For each i=1,2 choose
q_i∈Ji\{P1,P2}. The full frontier(Ai)=ci∪Ji ensures B_(q_i) also meets Ai. Thus O together with
these balls and the two connected Ai forms a connected subset; adjoining every Bq preserves
connectivity, as each meets O. This union is contained in E and covers E by the displayed
decomposition, so E is connected. O is nonempty and unbounded, hence so is E. This is the precise
source conclusion that the two outer cells are exterior to c, justified by full cut frontiers and
elementary connected-ball unions.

Q is nonempty, open, connected and bounded, and frontier(Q)=c by the second cut. E is nonempty, open
and connected by JC6. They are disjoint and exhaust Complex\c; therefore each is closed as well as
open relative to that complement, and a connected subset of the complement cannot meet both. They
are exactly its two connected components. For every point of c1, including P1,P2, frontier(A1)=c1∪J1
supplies arbitrarily close points of A1⊂E. For every point of c2, frontier(A2)=c2∪J2 does the same.
Hence c⊂frontier(E), since c is disjoint from E. Conversely any point outside c is in one of the two
open regions Q,E and cannot belong to frontier(E), so frontier(E)⊂c. Thus frontier(E)=frontier(Q)=c,
and closure(Q)=Q∪c. In particular the construction itself supplies a bounded complementary
component, without invoking the provisional bounded-component extension directly.
-/
theorem cairns_jordan_complement_two_regions
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) :
    let c : Set ℂ := Set.range γ
    ∃ Q E : Set ℂ,
      Q.Nonempty ∧ E.Nonempty ∧ Q ≠ E ∧
      Q ∪ E = cᶜ ∧ Disjoint Q E ∧
      (fun z : ℂ ↦ connectedComponentIn cᶜ z) '' cᶜ = {Q, E} ∧
      IsConnected Q ∧ IsConnected E ∧
      IsOpen Q ∧ IsOpen E ∧ Bornology.IsBounded Q ∧ ¬ Bornology.IsBounded E ∧
      frontier Q = c ∧ frontier E = c ∧ closure Q = Q ∪ c := by
  intro c
  obtain ⟨Q, E, hQ, hE, hQo, hEo, hQb, hEb, hcover, hdisj, hQfront, hEfront⟩ := cairns_jordan_open_regions γ hγ
  obtain ⟨hQne, hEne, hne, hcover, hdisj, hcomponents, hclosure⟩ :=
    cairns_two_regions_component_package hQ hE hQo hEo hQb hEb hcover hdisj
      hQfront hEfront
  exact ⟨Q, E, hQne, hEne, hne, hcover, hdisj, hcomponents,
    hQ, hE, hQo, hEo, hQb, hEb, hQfront, hEfront, hclosure⟩

end HolomorphicAnosov

