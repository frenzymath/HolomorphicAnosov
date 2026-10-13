import HolomorphicAnosov.Topology.CairnsCrosscutAmbientTransport
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UnitInterval
import HolomorphicAnosov.Topology.CairnsSimplePolygonSchoenflies
import HolomorphicAnosov.Topology.CairnsBoundedComponentDiskExtension
import HolomorphicAnosov.Topology.CairnsRoundDiskCrosscutSeparation
import HolomorphicAnosov.Topology.JordanComplementTwoRegions
import HolomorphicAnosov.Topology.CairnsBoundedComponentAmbientExtension

/-!
# Jordan separation, ambient Schoenflies extension, and arbitrary crosscuts

Source: Stewart S. Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*,
Proc. AMS 2 (1951), printed pp.860–867: main theorem p.860, Theorem 4.1 and Lemma 4.1
pp.864–865, crosscut Lemma 5.1 and interior-existence Lemma 5.2 p.866, final amalgamation p.867.
DAG node: `topo.marked_rectangle_g3_jordan_separation_schoenflies`.

The embedded curve, complementary components, ambient homeomorphism, and closed-disk extension
are all actual Mathlib maps and sets in the original Euclidean topology. A crosscut is an actual
embedding of `unitInterval` into the original closed inside region. Its two boundary arcs are
explicitly the pullbacks, through the returned ambient homeomorphism, of the two closed sides of
the endpoint chord on the unit circle. This defines the two arcs without requiring a regular
boundary or an independent Jordan oracle. The proof assembles the two-region, prescribed
boundary-extension, ambient-extension, and crosscut-transport theorems.
-/

open Set Metric
open scoped ComplexConjugate

namespace HolomorphicAnosov

/-- Every embedded circle admits an ambient plane homeomorphism onto the unit circle and has
exactly two complementary regions. Every prescribed boundary homeomorphism extends over the
closed bounded region, and every embedded distinct-endpoint crosscut separates the bounded
region into two components with their full respective cut boundaries.

Source: Cairns (1951), printed pp.860–867, especially the main theorem p.860, prescribed boundary
extension Theorem 4.1 pp.864–865, crosscut Lemma 5.1 p.866 and final amalgamation p.867.
`Circle` is Mathlib's ordinary unit circle. All frontiers and closures below are ambient-plane
frontiers and closures. The image of `connectedComponentIn` on the complement specifies ALL
components, with nonemptiness, openness, connectedness, and boundedness separately retained.
The arbitrary boundary homeomorphism is universally quantified, with equality at every boundary
point, and its extension maps the whole bounded region onto the open unit disk. Crosscuts have
no polygonal, differentiability, length, or local connectedness hypothesis. Either orientation of
the boundary map is permitted; the two endpoint-chord signs only index the two original arcs.

Complete current DAG natural-language proof:
1. Put c=gamma(S1). The embedding gives a homeomorphism S1→c in its original subspace topology, so c
is a compact simple closed curve and the inverse provides a boundary homeomorphism to S1. Cairns
first proves the polygon theorem2.1 by triangle base case and extreme-vertex diagonal induction; the
polygon child keeps its nonintersection, disk amalgamation, exterior and transverse-crossing steps
explicit. No arbitrary Jordan separation or conformal map is a prerequisite.

2. Cairns theorem4.1 is used only under its provisional hypothesis that a bounded complementary
component exists. The component-extension child proves the full prescribed homeomorphism of
closure(a) onto the closed disk, with a mapping to its interior and frontier(a)=c. Its source
argument is chord3.1, convex-hull star sectors3(D,E), linear radial extension4(A), compatible
recurrence(4.3), uniform residual shrinking4.1 and source/target exhaustion. These lower obligations
are written in that child and remain open. The parent does not replace the uniform-limit proof by
polygon approximation or invoke Caratheodory.

3. The genuine round-disk crosscut child follows Cairns5.1: a proposed path between the two sides
avoiding the arc completes to a polygon outside the disk, contradicting the polygon crossing
theorem; each cut curve then has a bounded component, to which the provisional extension applies;
the two cells amalgamate to exhaust the round disk. Only its later transport from the round disk to
a parametrized component is elementary. This source child occurs before any assertion of interior
existence for an arbitrary curve.

4. Apply the two-regions child to c. Its source5.2 constructs a polygon enclosing c with only two
extreme-point contacts, successively cuts its disk by the two curve arcs using the crosscut theorem,
and obtains a nonempty bounded cell with boundary c. The final two source amalgamations show that
this cell is the whole bounded complement, and all other points join the polygon exterior. It yields
exactly two open nonempty connected components Q,E, Q bounded, E unbounded,
frontier(Q)=frontier(E)=c and closure(Q)=Q∪c. This is the source step that removes the provisional
interior-existence hypothesis; neither the embedding nor the component-extension child alone
supplies it.

5. Let h:c→S1 be any prescribed homeomorphism. Apply the bounded-component extension child to Q to
get f:closure(Q)→closedD, f|c=h and f(Q)=D. This proves the full boundary-extension clause
immediately from the genuine component theorem. In particular choosing h as the inverse of gamma
supplies one disk chart, but arbitrary h is preserved. To obtain an ambient map rather than only
this inside chart, the remaining steps construct an outside map agreeing with that chosen h.

6. Choose a∈Q and define I(z)=1/(z−a) on Complex\{a}, with inverse Iinverse(w)=a+1/w on Complex\{0}.
These maps are continuous at every point of their domains by division with nonzero denominator, and
the algebra gives both inverse equations. The norm equation ||I(z)||=1/||z−a|| proves that infinity
corresponds to0. Let cprime=I(c); restricting I to c gives another embedded circle. Since a has a
ball contained in Q, E lies a positive distance from a, so I(E) is bounded. Since compact c is
contained in a large disk and E contains its connected outside region, I(E) contains a punctured
neighbourhood of0. Therefore B=I(E)∪{0} is nonempty, bounded, open and connected in the complement
of cprime. At every nonzero point its component membership is transported by the punctured-plane
homeomorphism. A small neighbourhood of0 lies in B; hence B has no frontier except on cprime. The
two-regions child applied to cprime identifies B with its bounded component. In particular
closure(B)=B∪cprime and0∈B. This uses the theorem only on a different curve after its source proof
is established, with no dependency backedge.

7. On cprime prescribe the boundary map k(I(z))=1/h(z). Inversion on S1 is a homeomorphism, so k is
a homeomorphism cprime→S1. Apply the component-extension child to B to obtain g:closure(B)→closedD
with g|cprime=k and g(B)=D. Put w=g(0), which lies in D. Correct this chart to send0 to0 while
keeping its boundary unchanged. Define T_w on closedD by T_w(0)=w and T_w(r*s)=(1−r)w+r*s for 0<r≤1,
s∈S1. Convexity puts its values in closedD, T_w fixes S1, and each ray from w has a unique first
circle endpoint. Thus T_w is bijective: the point w has unique preimage0, and every other point lies
on exactly one segment from w to its circle endpoint. The formula gives continuity away from0 and
||T_w(r*s)−w||≤r(1+||w||) gives continuity at0. The inverse is continuous by compact-to-Hausdorff
continuous bijection (equivalently by the ray-intersection quadratic). Set g0=T_w inverse composed
with g. Then g0(0)=0, g0|cprime=k and g0(B)=D. This elementary ray chart is an explicit expansion of
Cairns2(A)/final familiar extension, rather than an assumed ambient Schoenflies map.

8. For z∈E∪c define fout(z)=1/g0(I(z)). The denominator is nonzero: I(z)≠0 for finite z, and g0 is
injective with g0(0)=0. The chart maps B\{0} onto D\{0}, so fout maps E bijectively to {y:||y||>1}
and maps c to S1. On c, fout(z)=1/k(I(z))=h(z), exactly the same boundary values as f. Its
continuous inverse on the closed exterior is y↦a+1/(g0 inverse(1/y)); the intermediate point is
never0 for finite nonzero y. Both formulas are continuous by the existing division leaf. Properness
at infinity is also explicit: z→infinity implies I(z)→0, hence g0(I(z))→0 and ||fout(z)||→infinity.
No continuity of complex inversion at0 is asserted.

9. Define H on the plane by f on closure(Q) and fout on closure(E). The two-regions child gives a
closed cover closure(Q)∪closure(E)=Complex whose intersection is c. The formulas agree there, and
the exact closed-pair pasting theorem proves H continuous. On the target plane the closed disk and
closed exterior also form a closed cover meeting on S1. Paste the continuous inverses, which agree
there because each restricts to h inverse. Thus H is an ambient plane homeomorphism, H(c)=S1, H(Q)=D
and H(E)=the circle exterior. This is a full exterior construction; an inside disk homeomorphism
alone would not imply the ambient statement.

10. For the final crosscut clause, let eta:[0,1]→closure(Q) be an embedded simple arc with distinct
endpoints on c and interior in Q. The homeomorphism f carries it to a round-disk simple crosscut
with distinct endpoints. Apply the round-disk child to obtain exactly two components with respective
boundaries equal to the image arc together with the two circle arcs. Transport them back through f:
components are preserved by homeomorphisms, the two circle arcs correspond to the two original
boundary arcs, and closure/interior transport gives their boundaries in the original plane. Thus
each component has boundary eta([0,1]) plus its corresponding boundary arc. This transport is a
parent step, not a new theorem wrapper.

11. All component and boundary conclusions are in the original Euclidean topology on Complex. An
arbitrary boundary orientation is allowed, and the interior chart/exterior chart agree with the same
h. No piecewise smoothness, polygonality, local regularity, Riemann map, Caratheodory extension, or
preexisting Jordan separation of c has entered the hypotheses. The four lower source children remain
open with their constructive gaps; completing this parent split asserts the theorem conditional on
those exact named statements, not transitive proof completion.
-/
theorem markedRectangleG3JordanSeparationSchoenflies
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) :
    let c : Set ℂ := range γ
    ∃ (H : ℂ ≃ₜ ℂ) (Q E : Set ℂ),
      H '' c = sphere (0 : ℂ) 1 ∧
      H '' Q = ball (0 : ℂ) 1 ∧ H '' E = {z : ℂ | 1 < ‖z‖} ∧
      Q.Nonempty ∧ E.Nonempty ∧ Q ≠ E ∧ Q ∪ E = cᶜ ∧ Disjoint Q E ∧
      (fun z : ℂ ↦ connectedComponentIn cᶜ z) '' cᶜ = {Q, E} ∧
      IsOpen Q ∧ IsOpen E ∧ IsConnected Q ∧ IsConnected E ∧
      Bornology.IsBounded Q ∧ ¬ Bornology.IsBounded E ∧
      frontier Q = c ∧ frontier E = c ∧ closure Q = Q ∪ c ∧
      (∀ b : c ≃ₜ Circle, ∃ F : closure Q ≃ₜ closedBall (0 : ℂ) 1,
        (∀ z : closure Q, (z : ℂ) ∈ Q ↔ (F z : ℂ) ∈ ball (0 : ℂ) 1) ∧
        (∀ z : c, ∃ hz : (z : ℂ) ∈ closure Q,
          (F ⟨(z : ℂ), hz⟩ : ℂ) = (b z : ℂ))) ∧
      (∀ (η : unitInterval → closure Q), Topology.IsEmbedding η →
        (η 0 : ℂ) ∈ c → (η 1 : ℂ) ∈ c → η 0 ≠ η 1 →
        (∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → (η t : ℂ) ∈ Q) →
        let δ : unitInterval → ℂ := fun t ↦ (η t : ℂ)
        let K : Set ℂ := range δ
        let Kopen : Set ℂ := δ '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
        let Ω : Set ℂ := Q \ Kopen
        let A : Fin 2 → Set ℂ := fun i ↦
          {z | z ∈ c ∧
            if i = 0 then (conj (H (δ 1) - H (δ 0)) * (H z - H (δ 0))).im ≤ 0
            else 0 ≤ (conj (H (δ 1) - H (δ 0)) * (H z - H (δ 0))).im}
        ∃ V : Fin 2 → Set ℂ,
          (∀ i, (V i).Nonempty ∧ IsOpen (V i) ∧ IsConnected (V i)) ∧
          Disjoint (V 0) (V 1) ∧ (⋃ i, V i) = Ω ∧
          (fun z : ℂ ↦ connectedComponentIn Ω z) '' Ω = range V ∧
          (∀ i, frontier (V i) = K ∪ A i)) := by
  obtain ⟨Q, E, hQne, hEne, hne, hunion, hdis, hcomponents,
    hQconn, hEconn, hQopen, hEopen, hQbounded, hEunbounded,
    hQfrontier, hEfrontier, hclosure⟩ := cairns_jordan_complement_two_regions γ hγ
  have hQcomponent : ∃ z : ℂ, Q = connectedComponentIn (range γ)ᶜ z := by
    have hmem : Q ∈ (fun z : ℂ ↦ connectedComponentIn (range γ)ᶜ z) '' (range γ)ᶜ := by
      rw [hcomponents]
      exact Or.inl rfl
    obtain ⟨z, _, hz⟩ := hmem
    exact ⟨z, hz.symm⟩
  have hEeq : E = (closure Q)ᶜ := by
    rw [hclosure]
    ext z
    simp only [mem_compl_iff, mem_union]
    constructor
    · intro hz hbad
      rcases hbad with hzQ | hzc
      · exact Set.disjoint_left.mp hdis hzQ hz
      · have hzc' : z ∈ (range γ)ᶜ := hunion ▸ Or.inr hz
        exact hzc' hzc
    · intro hz
      have hzc : z ∈ (range γ)ᶜ := fun h ↦ hz (Or.inr h)
      have hpartition : z ∈ Q ∪ E := hunion.symm ▸ hzc
      exact hpartition.resolve_left (fun h ↦ hz (Or.inl h))
  obtain ⟨H, hHc, hHQ, hHE⟩ :=
    cairns_bounded_component_ambient_extension γ hγ Q hQne hQcomponent hQbounded
  rw [← hEeq] at hHE
  refine ⟨H, Q, E, hHc, hHQ, hHE, hQne, hEne, hne, hunion, hdis,
    hcomponents, hQopen, hEopen, hQconn, hEconn, hQbounded, hEunbounded,
    hQfrontier, hEfrontier, hclosure, ?_, ?_⟩
  · intro b
    obtain ⟨_, _, F, hFboundary, hFimage⟩ :=
      cairns_bounded_component_disk_extension γ hγ Q hQne hQcomponent hQbounded b
    refine ⟨F, ?_, ?_⟩
    · intro z
      constructor
      · intro hz
        exact hFimage ▸ ⟨z, hz, rfl⟩
      · intro hz
        have hz' : (F z : ℂ) ∈
            (fun w : closure Q ↦ (F w : ℂ)) '' {w : closure Q | (w : ℂ) ∈ Q} :=
          hFimage.symm ▸ hz
        obtain ⟨w, hw, heq⟩ := hz'
        have hwz : w = z := F.injective (Subtype.ext heq)
        exact hwz ▸ hw
    · intro z
      have hz : (z : ℂ) ∈ closure Q := by
        rw [hclosure]
        exact Or.inr z.property
      exact ⟨hz, hFboundary ⟨(z : ℂ), hz⟩ z.property⟩
  · intro η hη h0 h1 h01 hinterior
    exact cairns_crosscut_ambient_transport H Q (range γ) hHQ hHc
      η hη h0 h1 h01 hinterior

end HolomorphicAnosov
