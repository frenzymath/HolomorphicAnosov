import HolomorphicAnosov.Dynamics.Bowen.CanonicalCoordinatesOfCompactData
import HolomorphicAnosov.Topology.ManningBowenMarkovClosureTransport
import HolomorphicAnosov.Dynamics.Bowen.OrbitPlaqueOpenCollar
import HolomorphicAnosov.Topology.BowenAtomMembershipProfile
import HolomorphicAnosov.Topology.RegularClosedCollarComplement
import HolomorphicAnosov.Analysis.GeometricIterateTail
import HolomorphicAnosov.Topology.FiniteClosedQuadrantAtoms
import HolomorphicAnosov.Dynamics.Bowen.EnlargedRectangles
import HolomorphicAnosov.Dynamics.Bowen.PlaqueRebase
import HolomorphicAnosov.Dynamics.Bowen.ProductChart
import HolomorphicAnosov.Topology.ManningBowenInitialCoverUniformSaturation
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Dynamics.Bowen.CompactBracketUniformModulus

/-!
# Bowen's explicitly constructed positive-iterate Markov atoms

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), Fact 1,
pp.726–727, Lemmas 5–11, pp.728–731, and Lemmas 13–22, pp.731–738.
DAG node: `topo.manning_bowen_iterate_atom_markov`.
All auxiliary notions in the statement are literal local definitions on the original carrier.
-/

namespace HolomorphicAnosov

open scoped _root_.Topology

set_option maxHeartbeats 1000000 in
/-- Bowen’s explicit seed, iterate, quadrant and atom construction has the two Markov inclusions.

Source: Rufus Bowen, Markov Partitions for Axiom A Diffeomorphisms, Amer.J.Math.92 (1970), Fact1
pp.726–727, Lemmas5–11 pp.728–731, initial seed cover and Lemmas13–21 pp.731–736, Lemma22 and
proof pp.736–738. Obtained literature/Markov Partitions for Axiom A Diffeomorphisms.pdf, printed
p.727 and p.728 visually checked for bracket and scales; pp.737–738 unstable/complementary-factor
argument. Smale, Differentiable Dynamical Systems (1967), §7 pp.780ff. is background for
Fact1/canonical coordinates, not a replacement for the named Bowen construction. Source
applicability reconciliation: the independently reviewed SOURCE/split/complete product-chart
supplier now explicitly exports continuity of the SAME original modulus bracket on A_delta for
every0<delta<=gamma/3, proved in its retained Bredon I§8 Proposition8.2/Shub source application.
Step2 uses delta=alpha4/3 and3*alpha5<epsilon(alpha4/3) on its compact pair core; Step7 uses
delta=alpha3/3 and anchor mesh<alpha4<epsilon(alpha3/3)/3 for every approximating and limiting
pair. These settle the two recorded direct continuity interfaces without an initial-epsilon cap.
The inherited product openness/compactness, slice, rebase and interior laws use the reviewed
complete named product/enlargement providers at their existing exact scale bounds. This restores
complete ONE-LEVEL Stage1 decomposition only relative to the stated lower Fact1 and named
source/Mathlib obligations; the original-f connected refinement and whole-plaque holomorphic
branch obligations remain distinct and open. The Lean proof below preserves the theorem statement and applies these named dependencies.
It does not settle the separate original-map refinement or the lower providers themselves.

The theorem-local definitions use the original all-n orbit plaques and their induced topologies.
The bracket is total notation for its constrained small product domains only; no continuity
outside those domains is assumed. The Bool value true chooses the original positive factor, false
the relative closure of its collar complement. The union over quadrants in O selects the unique
interior quadrant, as asserted, and introduces no arbitrary Markov predicate. All finite labels,
both recursive sequences and the identical positive iterate are retained. No connectedness of seed
rectangles or final atoms is assumed or concluded.

Complete natural-language proof of topo.manning_bowen_iterate_atom_markov:

Step 1. Derive the initial seed theorem’s product premise from the literal Fact1 data. The
existing Denker/Bowen Lemma7 provider has exactly these plaque definitions, contraction, unique
continuous bracket, moduli and α₀,…,α₄ scales. Choose 0<r₀<min(α₂,γ,ε/3). Every relatively open
factor in a size-r₀ plaque lies in its α₂ plaque, so the provider makes its bracket product X-open
and a homeomorphism, with inverse q↦([q,x],[x,q]). Its guarded proof reconstructs a nearby q from
these two projections by the unique diagonal γ-intersection; it requires no manifold or
basic-set/transitivity hypothesis. Thus the seed theorem’s extra product premise is a deduction,
not an added premise of this parent.

Step 2. Obtain sufficiently small seeds and both saturation directions. Apply the seed theorem
with arbitrarily small η, keeping f as its map. Choose η so that its δ is below α₇ and its
diameter bound below α₅/2. Enforce additionally the fixed-parent transverse bound
[C_i⁰,y]⊂W_α₅ᵘ(y) for y∈W_{2α₅}ˢ(x_i), and the stable dual, by making these seeds smaller before
finite selection: the closed pair core d(c,y)≤3α₅ is compact, and lies strictly in the bracket
domain by 3α₅<ε(α₄/3). Uniform bracket continuity there compares [c,y] with [x_i,y]=y when c is
uniformly close to x_i, giving d([c,y],y)<α₅. Because the bracket already belongs to Wγᵘ(y),
contraction identifies its small plaque membership with this time-zero bound. Choose η<α₅ smaller
than the two uniform continuity tolerances once, uniformly over all centers, for both directions.
The compared pairs (c,y),(x_i,y) lie in the same compact core because d(c,y)≤δ+2α₅<3α₅ and
d(x_i,y)≤2α₅. The seed theorem then gives marked compact regular-closed factors, an interior cover
and its common F,a. Reduce a if necessary to 0<a<min(γ,α₃); saturation remains true for smaller
closed plaques. Its own small scale is not silently identified with the parent α₅. Explicit
supplier application: use the newly exported SAME b_delta continuity of
dynamics.bowen_fact1_product_chart_g6 with delta=alpha4/3, which is positive and at most gamma/3.
The recurrence gives3*alpha5<epsilon(alpha4/3). Thus EVERY pair in the closed core
d(c,y)<=3*alpha5, including both compared pairs, lies in A_delta. Restrict the continuous b_delta
to this compact core, using the continuous inclusion into its pair-domain subtype, and apply the
already named compact uniform-continuity theorem. This supplies the actual fixed-parent transverse
comparison; it does not identify the seed theorem’s separately chosen scale with alpha5 and
requires no bound by the initial epsilon.

Step 3. Choose m≥1 using λ^m→0 and the geometric sum Σ_{k≥1}(λ^m)^k=λ^m/(1−λ^m), making that sum
smaller than min(1,a/γ). The enlargement theorem applies to these very seeds and this m. Its
finite Lemma14 labels and recursions are exactly those in the statement; it constructs compact
regular-closed C_i,D_i, both lying in W_{2α₅}, with the same m in reverse time. Their
A_i=[C_i,D_i] cover X and have mesh<α₄. In particular it supplies the strict 3α₄ collar
conclusion: if d(q,x_i)<3α₄ and [q,x_i]∈C_i, some j∈N(hq) satisfies hq∈[C_j,hq]⊂h[C_i,q] and
h⁻¹(int_{Wγᵘ(hq)}[C_j,hq])⊂int_{Wγᵘ(q)}[C_i,q]. This conclusion includes all boundary
positive-factor points and has its explicit finite-orbit proof in the source provider; no extra
global plaque-openness premise is imposed here. To verify the displayed finite-stage plaque
condition, bound every geometric partial sum by 2 using the strict tail bound. The supplier
then puts each finite-stage slice in the radius-2α₅ plaque. Shifting the orbit inequalities
through h or h⁻¹ and adding the label displacement α₅ gives radius 3α₅≤γ at the original
center, for both recursive sequences.

Step 4. Choose the displayed collars explicitly as E_iᵘ=Wγᵘ(x_i)∩ball(x_i,r_i) and
E_iˢ=Wγˢ(x_i)∩ball(x_i,r_i), with α₃/3<r_i<2α₃/3. Contraction gives W_δ=Wγ∩closedBall(x_i,δ), so
they have the required containments. Since C_i,D_i lie in W_{2α₅}, they are strictly inside these
collars. Every full γ-plaque is X-closed, being the intersection of its continuous finite-orbit
closed-distance conditions, hence compact. The complements E_iᵘ\C_i and E_iˢ\D_i are relatively
open; their full-plaque closures are regular closed, compact, and contained in the closed
radius-r_i plaques. Choose larger open plaque neighborhoods U_i,V_i containing all positive and
negative factors with radii between 2α₃/3 and α₂. The product-chart theorem identifies [U_i,V_i]
with U_i×V_i and gives an X-open image. Product closure/interior and homeomorphism transport now
show that every nonempty K_i^{στ} is compact and regular closed in X. Closedness makes the ambient
regular-closed identity valid, since the chart is open and contains K. Empty products have empty
frontier. For a regular-closed C inside open E, (int closure(E\C))∩E=E\C: one inclusion follows
from openness, and the other from C=closure(int C), since an open neighborhood meeting C must meet
int C. Hence negative interiors are disjoint from closed positive factors. Product interiors are
therefore disjoint for distinct signs. This step makes no diameter or proper-rectangle claim about
auxiliary K_i.

Step 5. All factor products here are bracket closed, including the large auxiliary products, with
guarded algebra rather than a diameter premise. If c,c′∈U_i and d,d′∈V_i, let p=[c,d], q=[c′,d′].
The radius bound <α₂ gives d(c,d),d(c′,d′)<2α₂<ε(α₁/3), so p is in the stable α₁/3-plaque of c and
unstable α₁/3-plaque of d, and likewise q. Also d(p,q)<2α₁/3+2α₂<ε(γ/3), so r=[p,q] has
stable/unstable γ/3 margins relative to p,q. Triangle inequalities along all forward and backward
iterates put r in Wγˢ(c)∩Wγᵘ(d′), because γ/3+α₁/3<γ. Uniqueness yields [[c,d],[c′,d′]]=[c,d′]. If
p,q belong to one K its c and d′ factors belong to that same sign product. If p,q belong to int K,
the product-interior formula puts both coordinates in the corresponding open factor interiors, and
the same identity puts their bracket in int K. These are the only rectangle-algebra properties
needed of oversized K; their diameter can exceed α₃.

Step 6. For every y∈V_i, some A_j containing y meets A_i. Since both A_i,A_j have mesh<α₄ and
x_i∈A_i, d(y,x_i)<2α₄. The modulus gives [y,x_i]∈W_{α₃/3}ᵘ(x_i), [x_i,y]∈W_{α₃/3}ˢ(x_i), hence
both projections lie in the collars; uniqueness reconstructs y=[[y,x_i],[x_i,y]]. Each collar
point is in its positive factor or its negative factor, so the four products cover V_i. Every K is
closed, and the frontier of a closed set has empty interior. The finite union of these closed
nowhere-dense frontiers is closed nowhere dense; its complement Z is therefore dense open. For z∈Z
and i∈N(z), coverage and disjoint interiors give precisely one K_i(z) with z∈int K_i(z). Thus O(z)
is nonempty open. Its closure lies in each selected closed quadrant; taking interiors therefore
puts int closure O(z) inside every selected quadrant interior and hence inside O(z). Openness
gives the opposite inclusion. Thus int closure O(z)=O(z).

Step 7. The final atoms get smallness from an original anchor. Choose i₀ with z∈A_i₀. Then
i₀∈N(z), and z lies in the interior of A_i₀=K_i₀^{++}, since z avoids its frontier. Hence O(z)⊂int
A_i₀ and P(z)⊂A_i₀, giving compactness and mesh<α₄. The guarded algebra of the previous step makes
O(z) bracket closed, since it lies in each int K_i(z). For any x,y∈P(z), approximate each by
points of O(z); continuity of the bracket on this small common domain puts [x,y] in P(z).
Consequently P(z) is a nonempty compact bracket-closed regular-closed set with diam<α₄<α₃: it is a
proper rectangle. No auxiliary-quadrant diameter is invoked. Explicit supplier application: use
dynamics.bowen_fact1_product_chart_g6 at delta=alpha3/3, positive and at most gamma/3. The parent
recurrence gives alpha4<epsilon(alpha3/3)/3. The anchor A_i0 has mesh<alpha4 and contains O(z) and
its closure P(z), so ALL approximating pairs and their limiting pair(x,y) have
distance<alpha4<epsilon(alpha3/3) and belong to the SAME A_delta. The ambient pair convergences
are therefore convergences in that subspace, and the exported continuous b_delta gives the exact
bracket limit in the already closed P(z). No initial-epsilon cap or new continuity extension is
assumed.

Step 8. Prove the all-point profile without assuming t∈Z. Fix t∈O(z) and the preceding anchor i₀.
If z∈A_i then i∈N(z) and K_i(z)=A_i, so t∈A_i. Conversely, if t∈A_i then t∈A_i₀ too, so A_i meets
A_i₀. Because z∈A_i₀, this puts i∈N(z). If z∉A_i, the selected K_i(z) has a negative sign; its
interior is disjoint from the closed positive-positive A_i by the product complement law,
contradicting t∈O(z)∩A_i. Thus t,z belong to exactly the same A_i. The finite star definition
N(q)={i: some A_j containing q meets A_i} gives N(t)=N(z). If O(y)∩O(z) is nonempty, choose w in
this open intersection and in dense Z. The just-proved memberships give N(w)=N(y)=N(z), and
uniqueness of each quadrant interior at w gives K_i(w)=K_i(y)=K_i(z) for every active i. Thus
O(y)=O(z). There are only finitely many profiles and sign choices, so finitely many distinct O,P.
Their open union covers dense Z, and the finite closed union of their closures covers X. Distinct
O are disjoint and int P=O, proving the desired partition.

Step 9. Establish exactly the slice density needed at z∈Z. Since z∈O(z), continuity of
q↦[q,z] on the small anchor carries points of O(z) approaching any p∈P(z)∩Wγᵘ(z) to
points of O(z)∩Wγᵘ(z). Bracket closure puts these projections in O(z); the small modulus
puts them in the required plaque; diagonal uniqueness gives [p,z]=p. The closed plaque
and closed P(z) give the reverse containment. Hence P(z)∩Wγᵘ(z)=closure(O(z)∩Wγᵘ(z)).
The stable proof uses q↦[z,q]. This argument requires only interior basepoints z∈Z.

Step 10. Prove the inverse unstable inclusion on O. Fix z,hz∈Z and t∈O(hz)∩Wγᵘ(hz),
and put w=h⁻¹t. Backward contraction and the target atom mesh give d(w,z)<α₄ and
w∈Wγᵘ(z). Thus each active source center is within 3α₄ of w, and the small modulus puts
both projections strictly inside the collars. Guarded uniqueness shows [x_i,w]=[x_i,z]
and reconstructs w from [w,x_i] and z. For a positive source unstable sign, apply the
enlargement collar at z to obtain j∈N(hz), hz∈[C_j,hz], and the inverse relative-interior
inclusion. The positive target slice at hz forces its selected unstable sign to be positive:
a negative interior is disjoint from closed C_j. Every point of O(hz)∩Wγᵘ(hz) then lies in
the relative interior of [C_j,hz]. Indeed O(hz) is open, the selected quadrant puts its
unstable projection in C_j, and the rebase chart identifies the same local plaque. The
collar and rebase chart now put [w,x_i] in the relative interior of C_i.

Step 11. For a negative source sign, suppose [w,x_i]∈C_i. Apply the collar at w and use
the all-point profile N(t)=N(hz) to obtain an active target j with t∈[C_j,t]. Since
t∈O(hz), disjointness of negative interiors from closed positive factors forces the
selected j-sign at hz to be positive. Guarded reconstruction on the common small
unstable plaque gives hz∈[C_j,t]. The collar inclusion then gives z∈[C_i,w], by
injectivity of h, and the projection identity gives [z,x_i]∈C_i. This contradicts the
negative interior at z. Therefore [w,x_i] lies in the open collar complement and hence
in the interior of its relative closure. All stable coordinates of w equal those of z;
the product-interior identity gives w∈O(z). This proves
h⁻¹(O(hz)∩Wγᵘ(hz))⊆O(z)∩Wγᵘ(z).

Step 12. Repeat Steps 9–11 for f⁻¹, bracket [x,y]′=[y,x], with C,D and the sign pairs
exchanged. Its iterate is h⁻¹, its unstable plaques are the original stable plaques,
and its quadrants, Z, O and P are the same sets after transposition. This gives
h(O(z)∩Wγˢ(z))⊆O(hz)∩Wγˢ(hz). Finally use the two slice-closure identities from Step 9
and continuity of h and h⁻¹ to extend both inclusions to closed atom slices. This is the
existing Markov-closure-transport theorem specialized to the actual O,P and orbit plaques.
Together with the preceding finite partition construction, it proves the exact displayed
positive-iterate conclusion.

The module contains a Lean proof with no local admissions. The proof remains relative to
its imported named geometric providers; their independent proof status is recorded in the DAG.

-/
theorem manning_bowen_iterate_atom_markov
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X ≃ₜ X) (lam γ ε : ℝ)
    (hlam : 0 < lam) (hlam1 : lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (α : Fin 8 → ℝ) (εmod : ℝ → ℝ)
    (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdescending : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαscale : ∀ i : Fin 7,
      α i.succ < (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmap : ∀ i : Fin 7, ∀ x y : X, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (bracket : X → X → X) :
    let Ws : ℝ → X → Set X := fun δ x ↦
      {y | ∀ n : ℕ, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ δ}
    let Wu : ℝ → X → Set X := fun δ x ↦
      {y | ∀ n : ℕ, dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] x) ≤ δ}
    let product : Set X → Set X → Set X := fun C D ↦
      {z | ∃ c ∈ C, ∃ d ∈ D, bracket c d = z}
    let plaqueClosure : Set X → Set X → Set X := fun S A ↦
      (Subtype.val : S → X) '' closure ((Subtype.val : S → X) ⁻¹' A)
    let plaqueInterior : Set X → Set X → Set X := fun S A ↦
      (Subtype.val : S → X) '' interior ((Subtype.val : S → X) ⁻¹' A)
    let regularFactor : Set X → Set X → Prop := fun S A ↦
      A ⊆ S ∧ (Subtype.val : S → X) ⁻¹' A =
        closure (interior ((Subtype.val : S → X) ⁻¹' A))
    let proper : Set X → Prop := fun A ↦
      A.Nonempty ∧ IsCompact A ∧ (∀ x ∈ A, ∀ y ∈ A, bracket x y ∈ A) ∧
        Metric.diam A ≤ α 3 ∧ A = closure (interior A)
    (∀ x y z : X, ∀ n : ℕ, y ∈ Ws γ x → z ∈ Ws γ x →
      dist ((f : X → X)^[n] y) ((f : X → X)^[n] z) ≤ lam ^ n * dist y z) →
    (∀ x y z : X, ∀ n : ℕ, y ∈ Wu γ x → z ∈ Wu γ x →
      dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] z) ≤ lam ^ n * dist y z) →
    (∀ x y : X, dist x y ≤ ε →
      bracket x y ∈ Ws γ x ∩ Wu γ y ∧
        ∀ z ∈ Ws γ x ∩ Wu γ y, z = bracket x y) →
    ContinuousOn (fun p : X × X ↦ bracket p.1 p.2) {p | dist p.1 p.2 ≤ ε} →
    (∀ δ : ℝ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y : X, dist x y ≤ εmod δ → bracket x y ∈ Ws δ x ∩ Wu δ y) →
    ∃ m : ℕ, 0 < m ∧
      let h := f ^ m
      ∃ r : ℕ, 0 < r ∧
      ∃ (center : Fin r → X) (C0 D0 : Fin r → Set X) (F : X → Fin r) (a : ℝ)
        (s t : Fin r → ℕ)
        (target : ∀ i, Fin (s i) → Fin r) (y : ∀ i, Fin (s i) → X)
        (reverseTarget : ∀ i, Fin (t i) → Fin r) (reverseY : ∀ i, Fin (t i) → X)
        (Cseq Dseq : ℕ → Fin r → Set X) (C D Eu Es : Fin r → Set X),
      let A0 : Fin r → Set X := fun i ↦ product (C0 i) (D0 i)
      let A : Fin r → Set X := fun i ↦ product (C i) (D i)
      let Cu : Fin r → Bool → Set X := fun i σ ↦
        if σ then C i else plaqueClosure (Wu γ (center i)) (Eu i \ C i)
      let Ds : Fin r → Bool → Set X := fun i τ ↦
        if τ then D i else plaqueClosure (Ws γ (center i)) (Es i \ D i)
      let K : Fin r → Bool → Bool → Set X := fun i σ τ ↦ product (Cu i σ) (Ds i τ)
      let V : Fin r → Set X := fun i ↦ ⋃ j, ⋃ (_ : (A i ∩ A j).Nonempty), A j
      let N : X → Set (Fin r) := fun q ↦ {i | q ∈ V i}
      let Z : Set X := (⋃ i, ⋃ σ : Bool, ⋃ τ : Bool, frontier (K i σ τ))ᶜ
      let O : X → Set X := fun z ↦
        ⋂ i, ⋂ (_ : i ∈ N z),
          ⋃ σ : Bool, ⋃ τ : Bool, ⋃ (_ : z ∈ interior (K i σ τ)), interior (K i σ τ)
      let P : X → Set X := fun z ↦ closure (O z)
      (∀ i, IsCompact (C0 i) ∧ IsCompact (D0 i) ∧
        C0 i ⊆ Wu (α 7) (center i) ∧ D0 i ⊆ Ws (α 7) (center i) ∧
        regularFactor (Wu γ (center i)) (C0 i) ∧
        regularFactor (Ws γ (center i)) (D0 i) ∧
        center i ∈ plaqueInterior (Wu γ (center i)) (C0 i) ∧
        center i ∈ plaqueInterior (Ws γ (center i)) (D0 i) ∧
        proper (A0 i) ∧ center i ∈ interior (A0 i) ∧ Metric.diam (A0 i) < α 5 / 2) ∧
      (⋃ i, interior (A0 i)) = Set.univ ∧
      (∀ i, ∀ q ∈ Ws (2 * α 5) (center i), product (C0 i) {q} ⊆ Wu (α 5) q) ∧
      (∀ i, ∀ q ∈ Wu (2 * α 5) (center i), product {q} (D0 i) ⊆ Ws (α 5) q) ∧
      0 < a ∧ a < min γ (α 3) ∧
      (∀ q : X, q ∈ A0 (F q) ∧
        (∀ z ∈ Wu γ q ∩ A0 (F q), Ws a z ⊆ A0 (F q)) ∧
        (∀ z ∈ Ws γ q ∩ A0 (F q), Wu a z ⊆ A0 (F q))) ∧
      (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ) ∧
      (∀ i, (∀ j : Fin (s i), y i j ∈ Wu (α 5) (center i) ∧
        h (y i j) ∈ D0 (target i j) ∧
        ((h '' C0 i) ∩ product (C0 (target i j)) {h (y i j)}).Nonempty ∧
        ∀ z ∈ Wu γ (h (y i j)) ∩ A0 (target i j), Ws a z ⊆ A0 (target i j)) ∧
        h '' C0 i ⊆ ⋃ j : Fin (s i), product (C0 (target i j)) {h (y i j)}) ∧
      (∀ i, (∀ j : Fin (t i), reverseY i j ∈ Ws (α 5) (center i) ∧
        h.symm (reverseY i j) ∈ C0 (reverseTarget i j) ∧
        ((h.symm '' D0 i) ∩
          product {h.symm (reverseY i j)} (D0 (reverseTarget i j))).Nonempty ∧
        ∀ z ∈ Ws γ (h.symm (reverseY i j)) ∩ A0 (reverseTarget i j),
          Wu a z ⊆ A0 (reverseTarget i j)) ∧
        h.symm '' D0 i ⊆
          ⋃ j : Fin (t i), product {h.symm (reverseY i j)} (D0 (reverseTarget i j))) ∧
      Cseq 0 = C0 ∧ Dseq 0 = D0 ∧
      (∀ n i, Cseq (n + 1) i =
        ⋃ j : Fin (s i), h.symm '' product (Cseq n (target i j)) {h (y i j)}) ∧
      (∀ n i, Dseq (n + 1) i =
        ⋃ j : Fin (t i), h '' product {h.symm (reverseY i j)} (Dseq n (reverseTarget i j))) ∧
      (∀ n i, Cseq n i ⊆ Wu γ (center i) ∧ Dseq n i ⊆ Ws γ (center i)) ∧
      (∀ i, C i = plaqueClosure (Wu γ (center i)) (⋃ n : ℕ, Cseq n i) ∧
        D i = plaqueClosure (Ws γ (center i)) (⋃ n : ℕ, Dseq n i)) ∧
      (∀ i, IsCompact (C i) ∧ IsCompact (D i) ∧
        regularFactor (Wu γ (center i)) (C i) ∧
        regularFactor (Ws γ (center i)) (D i) ∧
        C0 i ⊆ C i ∧ D0 i ⊆ D i ∧
        C i ⊆ Wu (2 * α 5) (center i) ∧ D i ⊆ Ws (2 * α 5) (center i) ∧
        proper (A i) ∧ center i ∈ interior (A i) ∧ Metric.diam (A i) < α 4) ∧
      (⋃ i, A i) = Set.univ ∧
      (∀ i, Eu i ⊆ Wu γ (center i) ∧ Es i ⊆ Ws γ (center i) ∧
        IsOpen ((Subtype.val : Wu γ (center i) → X) ⁻¹' Eu i) ∧
        IsOpen ((Subtype.val : Ws γ (center i) → X) ⁻¹' Es i) ∧
        Wu (α 3 / 3) (center i) ⊆ Eu i ∧ Eu i ⊆ Wu (2 * α 3 / 3) (center i) ∧
        Ws (α 3 / 3) (center i) ⊆ Es i ∧ Es i ⊆ Ws (2 * α 3 / 3) (center i)) ∧
      IsOpen Z ∧ Dense Z ∧
      (∀ z ∈ Z, ∀ i ∈ N z, ∃! στ : Bool × Bool, z ∈ interior (K i στ.1 στ.2)) ∧
      (P '' Z).Finite ∧ (⋃ z ∈ Z, P z) = Set.univ ∧
      (∀ z ∈ Z, proper (P z) ∧ interior (P z) = O z) ∧
      (∀ z ∈ Z, ∀ w ∈ Z, P z ≠ P w → Disjoint (interior (P z)) (interior (P w))) ∧
      (∀ z ∈ Z, h z ∈ Z →
        P (h z) ∩ Wu γ (h z) ⊆ h '' (P z ∩ Wu γ z) ∧
        h '' (P z ∩ Ws γ z) ⊆ P (h z) ∩ Ws γ (h z)) := by
  intro Ws Wu product plaqueClosure plaqueInterior regularFactor proper
    hcontract_s hcontract_u hunique hcontinuous hmodulus
  have hα3γ : α 3 ≤ γ := by
    calc
      α 3 ≤ α 2 := (hαdescending 2).le
      _ ≤ α 1 := (hαdescending 1).le
      _ ≤ α 0 := (hαdescending 0).le
      _ = γ := hα0
  have hr : 0 ≤ α 3 / 3 := div_nonneg (hαpos 3).le (by norm_num)
  have hrR : α 3 / 3 < 2 * α 3 / 3 := by linarith only [hαpos 3]
  have hRγ : 2 * α 3 / 3 ≤ γ := by linarith only [hαpos 3,hα3γ]
  have stableCollar := fun x ↦ bowen_orbit_plaque_open_collar
    (f : X → X) hlam.le hlam1.le hr hrR hRγ hcontract_s x
  have unstableCollar := fun x ↦ bowen_orbit_plaque_open_collar
    (f.symm : X → X) hlam.le hlam1.le hr hrR hRγ hcontract_u x
  -- Build the seed theorem's canonical coordinates from the given original bracket.
  let αshort : Fin 5 → ℝ := fun i ↦ α ⟨i.val, by omega⟩
  have hcharts := (Bowen.bowen_fact1_product_chart_g6 f lam γ ε
    hlam hlam1 hγ hε αshort εmod (fun δ hδ hδγ ↦ (hmodulus δ hδ hδγ).1)
    hα0 (fun i ↦ hαpos ⟨i.val, by omega⟩)
    (fun i ↦ hαscale ⟨i.val, by omega⟩)
    (fun i ↦ hαmap ⟨i.val, by omega⟩) bracket hcontract_s hcontract_u
    (fun x y hxy ↦ ⟨bracket x y, (hunique x y hxy).1, (hunique x y hxy).2⟩)
    (fun x y hxy ↦ (hunique x y hxy).1) hcontinuous
    (fun δ hδ hδγ ↦ (hmodulus δ hδ hδγ).2))
  have hα2γ : α 2 < γ := by
    calc
      α 2 < α 1 := hαdescending 1
      _ < α 0 := hαdescending 0
      _ = γ := hα0
  let H : Dynamics.Bowen.CompactLocalProductData f γ lam := {
    gamma_pos := hγ
    lambda_pos := hlam
    lambda_lt_one := hlam1
    stable_contraction := fun x y z hy hz n ↦ hcontract_s x y z n hy hz
    unstable_contraction := fun x y z hy hz n ↦ hcontract_u x y z n hy hz
    closeRadius := ε
    closeRadius_pos := hε
    bracket := bracket
    bracket_mem := fun x y hxy ↦ (hunique x y hxy).1
    bracket_unique := fun x y z hxy hz ↦ (hunique x y hxy).2 z hz
    bracket_continuous := hcontinuous
    product_chart := by
      intro x
      let ρ := min (α 2) (ε / 2)
      refine ⟨ρ, lt_min (hαpos 2) (half_pos hε),
        (min_le_left _ _).trans hα2γ.le, ?_, ?_⟩
      · dsimp [ρ]
        linarith [min_le_right (α 2) (ε / 2)]
      · intro U V hU hV hUo hVo
        obtain ⟨hopen, h, hh, _⟩ := hcharts.2 x U V
          (fun z hz n ↦ (hU hz n).trans (min_le_left _ _))
          (fun z hz n ↦ (hV hz n).trans (min_le_left _ _)) hUo hVo
        exact ⟨hopen, h, hh⟩ }
  obtain ⟨K, hKbracket⟩ := Dynamics.Bowen.canonicalCoordinatesOfCompactData f γ lam H
  -- Choose the seed tolerance on the fixed-parent compact pair core before
  -- selecting seeds; the seed theorem's own smaller scale need not equal α 5.
  have hα4γ : α 4 ≤ γ := (hαdescending 3).le.trans hα3γ
  have hcoreScale : 3 * α 5 < εmod (α 4 / 3) := by
    have hs := (hαscale 4).trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num at hs
    linarith
  let core : Set (X × X) := {p | dist p.1 p.2 ≤ 3 * α 5}
  have hcoreCompact : IsCompact core :=
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const).isCompact
  have hcoreContinuous : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2) core :=
    (hcharts.1 (α 4 / 3) (div_pos (hαpos 4) (by norm_num)) (by linarith only [hα4γ])).mono
      (fun p hp ↦ (show dist p.1 p.2 ≤ 3 * α 5 from hp).trans hcoreScale.le)
  obtain ⟨ρ, hρ, hρmod⟩ := Bowen.compact_bracket_uniform_modulus bracket core
    hcoreCompact hcoreContinuous (hαpos 5)
  let η := min (α 7) (min (α 5) ρ)
  have hη : 0 < η := lt_min (hαpos 7) (lt_min (hαpos 5) hρ)
  obtain ⟨δ, β, hδ, hδβ, hβη, hβγ, hβε, ⟨seeds⟩⟩ :=
    manningBowenInitialCoverUniformSaturation f γ lam ε K η hη
  have hδ7 : δ < α 7 := hδβ.trans (hβη.trans_le (min_le_left _ _))
  have hβ5 : β < α 5 := hβη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ5 : δ < α 5 := hδβ.trans hβ5
  have hδρ : δ < ρ := hδβ.trans
    (hβη.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have h45γ : α 4 / 3 + 2 * α 5 ≤ γ := by
    have hs := (hαscale 4).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num only [Fin.reduceSucc, Fin.reduceCastSucc] at hs
    linarith [hαpos 4]
  have hsmall := (hmodulus (α 4 / 3) (div_pos (hαpos 4) (by norm_num))
    (by linarith only [hαpos 4,hα4γ])).2
  have hdiag (x : X) : bracket x x = x := by
    symm
    exact (hunique x x (by simpa using hε.le)).2 x
      ⟨fun n ↦ by simpa using hγ.le, fun n ↦ by simpa using hγ.le⟩
  have hfix_s (x q : X)
      (hq : ∀ n : ℕ, dist ((f : X → X)^[n] q) ((f : X → X)^[n] x) ≤ 2 * α 5) :
      bracket x q = q := by
    have hxq : dist x q ≤ εmod (α 4 / 3) := by
      have hq0 := hq 0
      simpa only [Function.iterate_zero_apply, dist_comm x q] using
        hq0.trans (show 2 * α 5 ≤ εmod (α 4 / 3) by linarith [hαpos 5])
    have hb := hsmall x q hxq
    have hqdiag := (hunique q q (by simpa using hε.le)).2 (bracket x q)
      ⟨fun n ↦ (dist_triangle _ ((f : X → X)^[n] x) _).trans
        ((add_le_add (hb.1 n) (by simpa only [dist_comm] using hq n)).trans h45γ),
       fun n ↦ (hb.2 n).trans (by linarith only [hαpos 4,hα4γ])⟩
    exact hqdiag.trans (hdiag q)
  have hfix_u (x q : X)
      (hq : ∀ n : ℕ,
        dist ((f.symm : X → X)^[n] q) ((f.symm : X → X)^[n] x) ≤ 2 * α 5) :
      bracket q x = q := by
    have hqx : dist q x ≤ εmod (α 4 / 3) :=
      (hq 0).trans (by linarith [hαpos 5])
    have hb := hsmall q x hqx
    have hqdiag := (hunique q q (by simpa using hε.le)).2 (bracket q x)
      ⟨fun n ↦ (hb.1 n).trans (by linarith only [hαpos 4,hα4γ]),
       fun n ↦ (dist_triangle _ ((f.symm : X → X)^[n] x) _).trans
        ((add_le_add (hb.2 n) (by simpa only [dist_comm] using hq n)).trans h45γ)⟩
    exact hqdiag.trans (hdiag q)
  have hseed_u : ∀ i, ∀ q : X,
      (∀ n : ℕ, dist ((f : X → X)^[n] q) ((f : X → X)^[n] (seeds.center i)) ≤ 2 * α 5) →
      ∀ c ∈ seeds.unstableFactor i, ∀ n : ℕ,
        dist ((f.symm : X → X)^[n] (bracket c q)) ((f.symm : X → X)^[n] q) ≤ α 5 := by
    intro i q hq c hc n
    have hcx : dist c (seeds.center i) ≤ δ := by
      simpa only [manningBowenUnstablePlaque, Set.mem_ofPred_eq,
        Function.iterate_zero_apply, dist_comm] using seeds.unstableFactor_subset i hc 0
    have hqx : dist q (seeds.center i) ≤ 2 * α 5 := hq 0
    have hpair : (c, q) ∈ core := by
      change dist c q ≤ 3 * α 5
      have ht := dist_triangle c (seeds.center i) q
      rw [dist_comm (seeds.center i) q] at ht
      linarith
    have hpair0 : (seeds.center i, q) ∈ core := by
      change dist (seeds.center i) q ≤ 3 * α 5
      rw [dist_comm]
      linarith [hαpos 5]
    have hdist : dist (bracket c q) q < α 5 := by
      have hh := hρmod (c, q) hpair (seeds.center i, q) hpair0
        (show dist (c, q) (seeds.center i, q) < ρ by simpa using hcx.trans_lt hδρ)
      simpa only [hfix_s _ _ hq] using hh
    have hb := hsmall c q (hpair.trans hcoreScale.le)
    calc
      dist ((f.symm : X → X)^[n] (bracket c q)) ((f.symm : X → X)^[n] q) ≤
          lam ^ n * dist (bracket c q) q := hcontract_u q (bracket c q) q n
            (fun k ↦ (hb.2 k).trans (by linarith only [hαpos 4,hα4γ]))
            (fun k ↦ by simpa using hγ.le)
      _ ≤ dist (bracket c q) q := mul_le_of_le_one_left dist_nonneg
        (pow_le_one₀ hlam.le hlam1.le)
      _ ≤ α 5 := hdist.le
  have hseed_s : ∀ i, ∀ q : X,
      (∀ n : ℕ,
        dist ((f.symm : X → X)^[n] q) ((f.symm : X → X)^[n] (seeds.center i)) ≤ 2 * α 5) →
      ∀ d ∈ seeds.stableFactor i, ∀ n : ℕ,
        dist ((f : X → X)^[n] (bracket q d)) ((f : X → X)^[n] q) ≤ α 5 := by
    intro i q hq d hd n
    have hdx : dist d (seeds.center i) ≤ δ := by
      simpa only [manningBowenStablePlaque, Set.mem_ofPred_eq,
        Function.iterate_zero_apply, dist_comm] using seeds.stableFactor_subset i hd 0
    have hqx : dist q (seeds.center i) ≤ 2 * α 5 := hq 0
    have hpair : (q, d) ∈ core := by
      change dist q d ≤ 3 * α 5
      have ht := dist_triangle q (seeds.center i) d
      rw [dist_comm (seeds.center i) d] at ht
      linarith
    have hpair0 : (q, seeds.center i) ∈ core := by
      change dist q (seeds.center i) ≤ 3 * α 5
      linarith [hαpos 5]
    have hdist : dist (bracket q d) q < α 5 := by
      have hh := hρmod (q, d) hpair (q, seeds.center i) hpair0
        (show dist (q, d) (q, seeds.center i) < ρ by simpa using hdx.trans_lt hδρ)
      simpa only [hfix_u _ _ hq] using hh
    have hb := hsmall q d (hpair.trans hcoreScale.le)
    calc
      dist ((f : X → X)^[n] (bracket q d)) ((f : X → X)^[n] q) ≤
          lam ^ n * dist (bracket q d) q := hcontract_s q (bracket q d) q n
            (fun k ↦ (hb.1 k).trans (by linarith only [hαpos 4,hα4γ]))
            (fun k ↦ by simpa using hγ.le)
      _ ≤ dist (bracket q d) q := mul_le_of_le_one_left dist_nonneg
        (pow_le_one₀ hlam.le hlam1.le)
      _ ≤ α 5 := hdist.le
  let a := min (seeds.saturationRadius / 2) (min γ (α 3) / 2)
  have ha : 0 < a := lt_min (half_pos seeds.saturationRadius_pos)
    (half_pos (lt_min hγ (hαpos 3)))
  have hasat : a ≤ seeds.saturationRadius :=
    (min_le_left _ _).trans (half_le_self seeds.saturationRadius_pos.le)
  have hasmall : a < min γ (α 3) :=
    (min_le_right _ _).trans_lt (half_lt_self (lt_min hγ (hαpos 3)))
  obtain ⟨m, hm, htail⟩ := exists_pos_iterate_geometric_tail_lt hlam.le hlam1
    (lt_min (by norm_num : (0 : ℝ) < 1) (div_pos ha hγ))
  let h := f ^ m
  suffices hremaining :
    ∃ (s t : Fin seeds.count → ℕ)
        (target : ∀ i, Fin (s i) → Fin seeds.count) (y : ∀ i, Fin (s i) → X)
        (reverseTarget : ∀ i, Fin (t i) → Fin seeds.count) (reverseY : ∀ i, Fin (t i) → X)
        (Cseq Dseq : ℕ → Fin seeds.count → Set X) (C D Eu Es : Fin seeds.count → Set X),
      let A0 : Fin seeds.count → Set X := fun i ↦ product (seeds.unstableFactor i) (seeds.stableFactor i)
      let A : Fin seeds.count → Set X := fun i ↦ product (C i) (D i)
      let Cu : Fin seeds.count → Bool → Set X := fun i σ ↦
        if σ then C i else plaqueClosure (Wu γ (seeds.center i)) (Eu i \ C i)
      let Ds : Fin seeds.count → Bool → Set X := fun i τ ↦
        if τ then D i else plaqueClosure (Ws γ (seeds.center i)) (Es i \ D i)
      let K : Fin seeds.count → Bool → Bool → Set X := fun i σ τ ↦ product (Cu i σ) (Ds i τ)
      let V : Fin seeds.count → Set X := fun i ↦ ⋃ j, ⋃ (_ : (A i ∩ A j).Nonempty), A j
      let N : X → Set (Fin seeds.count) := fun q ↦ {i | q ∈ V i}
      let Z : Set X := (⋃ i, ⋃ σ : Bool, ⋃ τ : Bool, frontier (K i σ τ))ᶜ
      let O : X → Set X := fun z ↦
        ⋂ i, ⋂ (_ : i ∈ N z),
          ⋃ σ : Bool, ⋃ τ : Bool, ⋃ (_ : z ∈ interior (K i σ τ)), interior (K i σ τ)
      let P : X → Set X := fun z ↦ closure (O z)
      (∀ i, IsCompact (seeds.unstableFactor i) ∧ IsCompact (seeds.stableFactor i) ∧
        seeds.unstableFactor i ⊆ Wu (α 7) (seeds.center i) ∧ seeds.stableFactor i ⊆ Ws (α 7) (seeds.center i) ∧
        regularFactor (Wu γ (seeds.center i)) (seeds.unstableFactor i) ∧
        regularFactor (Ws γ (seeds.center i)) (seeds.stableFactor i) ∧
        seeds.center i ∈ plaqueInterior (Wu γ (seeds.center i)) (seeds.unstableFactor i) ∧
        seeds.center i ∈ plaqueInterior (Ws γ (seeds.center i)) (seeds.stableFactor i) ∧
        proper (A0 i) ∧ seeds.center i ∈ interior (A0 i) ∧ Metric.diam (A0 i) < α 5 / 2) ∧
      (⋃ i, interior (A0 i)) = Set.univ ∧
      (∀ q : X, q ∈ A0 (seeds.select q) ∧
        (∀ z ∈ Wu γ q ∩ A0 (seeds.select q), Ws a z ⊆ A0 (seeds.select q)) ∧
        (∀ z ∈ Ws γ q ∩ A0 (seeds.select q), Wu a z ⊆ A0 (seeds.select q))) ∧
      (∀ i, (∀ j : Fin (s i), y i j ∈ Wu (α 5) (seeds.center i) ∧
        h (y i j) ∈ seeds.stableFactor (target i j) ∧
        ((h '' seeds.unstableFactor i) ∩ product (seeds.unstableFactor (target i j)) {h (y i j)}).Nonempty ∧
        ∀ z ∈ Wu γ (h (y i j)) ∩ A0 (target i j), Ws a z ⊆ A0 (target i j)) ∧
        h '' seeds.unstableFactor i ⊆ ⋃ j : Fin (s i), product (seeds.unstableFactor (target i j)) {h (y i j)}) ∧
      (∀ i, (∀ j : Fin (t i), reverseY i j ∈ Ws (α 5) (seeds.center i) ∧
        h.symm (reverseY i j) ∈ seeds.unstableFactor (reverseTarget i j) ∧
        ((h.symm '' seeds.stableFactor i) ∩
          product {h.symm (reverseY i j)} (seeds.stableFactor (reverseTarget i j))).Nonempty ∧
        ∀ z ∈ Ws γ (h.symm (reverseY i j)) ∩ A0 (reverseTarget i j),
          Wu a z ⊆ A0 (reverseTarget i j)) ∧
        h.symm '' seeds.stableFactor i ⊆
          ⋃ j : Fin (t i), product {h.symm (reverseY i j)} (seeds.stableFactor (reverseTarget i j))) ∧
      Cseq 0 = seeds.unstableFactor ∧ Dseq 0 = seeds.stableFactor ∧
      (∀ n i, Cseq (n + 1) i =
        ⋃ j : Fin (s i), h.symm '' product (Cseq n (target i j)) {h (y i j)}) ∧
      (∀ n i, Dseq (n + 1) i =
        ⋃ j : Fin (t i), h '' product {h.symm (reverseY i j)} (Dseq n (reverseTarget i j))) ∧
      (∀ n i, Cseq n i ⊆ Wu γ (seeds.center i) ∧ Dseq n i ⊆ Ws γ (seeds.center i)) ∧
      (∀ i, C i = plaqueClosure (Wu γ (seeds.center i)) (⋃ n : ℕ, Cseq n i) ∧
        D i = plaqueClosure (Ws γ (seeds.center i)) (⋃ n : ℕ, Dseq n i)) ∧
      (∀ i, IsCompact (C i) ∧ IsCompact (D i) ∧
        regularFactor (Wu γ (seeds.center i)) (C i) ∧
        regularFactor (Ws γ (seeds.center i)) (D i) ∧
        seeds.unstableFactor i ⊆ C i ∧ seeds.stableFactor i ⊆ D i ∧
        C i ⊆ Wu (2 * α 5) (seeds.center i) ∧ D i ⊆ Ws (2 * α 5) (seeds.center i) ∧
        proper (A i) ∧ seeds.center i ∈ interior (A i) ∧ Metric.diam (A i) < α 4) ∧
      (⋃ i, A i) = Set.univ ∧
      (∀ i, Eu i ⊆ Wu γ (seeds.center i) ∧ Es i ⊆ Ws γ (seeds.center i) ∧
        IsOpen ((Subtype.val : Wu γ (seeds.center i) → X) ⁻¹' Eu i) ∧
        IsOpen ((Subtype.val : Ws γ (seeds.center i) → X) ⁻¹' Es i) ∧
        Wu (α 3 / 3) (seeds.center i) ⊆ Eu i ∧ Eu i ⊆ Wu (2 * α 3 / 3) (seeds.center i) ∧
        Ws (α 3 / 3) (seeds.center i) ⊆ Es i ∧ Es i ⊆ Ws (2 * α 3 / 3) (seeds.center i)) ∧
      IsOpen Z ∧ Dense Z ∧
      (∀ z ∈ Z, ∀ i ∈ N z, ∃! στ : Bool × Bool, z ∈ interior (K i στ.1 στ.2)) ∧
      (P '' Z).Finite ∧ (⋃ z ∈ Z, P z) = Set.univ ∧
      (∀ z ∈ Z, proper (P z) ∧ interior (P z) = O z) ∧
      (∀ z ∈ Z, ∀ w ∈ Z, P z ≠ P w → Disjoint (interior (P z)) (interior (P w))) ∧
      (∀ z ∈ Z, h z ∈ Z →
        P (h z) ∩ Wu γ (h z) ⊆ h '' (P z ∩ Wu γ z) ∧
        h '' (P z ∩ Ws γ z) ⊆ P (h z) ∩ Ws γ (h z)) by
    obtain ⟨s, t, target, y, reverseTarget, reverseY, Cseq, Dseq, C, D, Eu, Es,
      hseed, hcover, hselection, hremaining⟩ := hremaining
    refine ⟨m, hm, seeds.count, seeds.count_pos, seeds.center, seeds.unstableFactor,
      seeds.stableFactor, seeds.select, a, s, t, target, y, reverseTarget, reverseY,
      Cseq, Dseq, C, D, Eu, Es, hseed, hcover, ?_, ?_, ha, hasmall,
      hselection, htail, hremaining⟩
    · intro i q hq z hz
      obtain ⟨c, hc, d, hd, rfl⟩ := hz
      have hdq : d = q := hd
      subst d
      exact hseed_u i q hq c hc
    · intro i q hq z hz
      obtain ⟨c, hc, d, hd, rfl⟩ := hz
      have hcq : c = q := hc
      subst c
      exact hseed_s i q hq d hd
  classical
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdescending i).le)
  have hWs (r : ℝ) (x : X) : manningBowenStablePlaque f r x = Ws r x := by
    ext y
    simp only [manningBowenStablePlaque, Ws, Set.mem_ofPred_eq, dist_comm]
  have hWu (r : ℝ) (x : X) : manningBowenUnstablePlaque f r x = Wu r x := by
    ext y
    simp only [manningBowenUnstablePlaque, Wu, Set.mem_ofPred_eq, dist_comm]
  have hws (r : ℝ) (x : X) : Bowen.ws f r x = Ws r x := by
    simp only [Bowen.ws, Ws, BowenRegularClosedPreparation.pow_apply_iterate]
  have hwu (r : ℝ) (x : X) : Bowen.wu f r x = Wu r x := by
    simp only [Bowen.wu, Wu, BowenRegularClosedPreparation.pow_apply_iterate]
  have hrect (i : Fin seeds.count) :
      seeds.rectangle i = product (seeds.unstableFactor i) (seeds.stableFactor i) := by
    rw [seeds.rectangle_eq]
    ext z
    constructor
    · rintro ⟨p, hc, hd, hp⟩
      exact ⟨p.val.1, hc, p.val.2, hd, (hKbracket p).symm.trans hp⟩
    · rintro ⟨c, hc, d, hd, he⟩
      exact ⟨⟨(c, d), seeds.factor_brackets_defined i c hc d hd⟩, hc, hd,
        (hKbracket _).trans he⟩
  have hCsub (i : Fin seeds.count) : seeds.unstableFactor i ⊆ Wu (α 7) (seeds.center i) := by
    intro c hc n
    have hh := seeds.unstableFactor_subset i hc n
    exact (show dist _ _ ≤ δ by simpa only [dist_comm] using hh).trans hδ7.le
  have hDsub (i : Fin seeds.count) : seeds.stableFactor i ⊆ Ws (α 7) (seeds.center i) := by
    intro c hc n
    have hh := seeds.stableFactor_subset i hc n
    exact (show dist _ _ ≤ δ by simpa only [dist_comm] using hh).trans hδ7.le
  have hCγ (i : Fin seeds.count) : seeds.unstableFactor i ⊆ Wu γ (seeds.center i) :=
    fun c hc n ↦ (hCsub i hc n).trans ((hmono (Fin.zero_le _)).trans_eq hα0)
  have hDγ (i : Fin seeds.count) : seeds.stableFactor i ⊆ Ws γ (seeds.center i) :=
    fun c hc n ↦ (hDsub i hc n).trans ((hmono (Fin.zero_le _)).trans_eq hα0)
  have hCreg (i : Fin seeds.count) : regularFactor (Wu γ (seeds.center i))
      (seeds.unstableFactor i) := by
    refine ⟨hCγ i, ?_⟩
    have hh := seeds.unstableFactor_regular i
    unfold manningBowenRelativeRegularClosed at hh
    rw [hWu] at hh
    exact hh.symm
  have hDreg (i : Fin seeds.count) : regularFactor (Ws γ (seeds.center i))
      (seeds.stableFactor i) := by
    refine ⟨hDγ i, ?_⟩
    have hh := seeds.stableFactor_regular i
    unfold manningBowenRelativeRegularClosed at hh
    rw [hWs] at hh
    exact hh.symm
  have hCi (i : Fin seeds.count) : seeds.center i ∈
      plaqueInterior (Wu γ (seeds.center i)) (seeds.unstableFactor i) := by
    obtain ⟨N, hNo, hx, hN⟩ := seeds.unstableFactor_neighborhood i
    refine ⟨⟨seeds.center i, fun n ↦ by simpa using hγ.le⟩, ?_, rfl⟩
    apply interior_mono (show (Subtype.val : Wu γ (seeds.center i) → X) ⁻¹' N ⊆
      Subtype.val ⁻¹' seeds.unstableFactor i from fun y hy ↦
        hN ⟨by simpa only [hWu] using y.property, hy⟩)
    rw [(hNo.preimage continuous_subtype_val).interior_eq]
    exact hx
  have hDi (i : Fin seeds.count) : seeds.center i ∈
      plaqueInterior (Ws γ (seeds.center i)) (seeds.stableFactor i) := by
    obtain ⟨N, hNo, hx, hN⟩ := seeds.stableFactor_neighborhood i
    refine ⟨⟨seeds.center i, fun n ↦ by simpa using hγ.le⟩, ?_, rfl⟩
    apply interior_mono (show (Subtype.val : Ws γ (seeds.center i) → X) ⁻¹' N ⊆
      Subtype.val ⁻¹' seeds.stableFactor i from fun y hy ↦
        hN ⟨by simpa only [hWs] using y.property, hy⟩)
    rw [(hNo.preimage continuous_subtype_val).interior_eq]
    exact hx
  have hseedProper (i : Fin seeds.count) :
      proper (product (seeds.unstableFactor i) (seeds.stableFactor i)) := by
    rw [← hrect]
    refine ⟨seeds.rectangle_nonempty i, seeds.rectangle_compact i, ?_, ?_,
      seeds.rectangle_regular i⟩
    · intro x hx y hy
      have hh := seeds.rectangle_bracket_closed i
        ⟨(x, y), seeds.rectangle_brackets_defined i x hx y hy⟩ hx hy
      simpa only [hKbracket] using hh
    · exact (seeds.rectangle_diam i).le.trans
        ((half_le_self (hδ.trans hδβ).le).trans
          (hβ5.le.trans (hmono (show (3 : Fin 8) ≤ 5 by decide))))
  have hseedDiam (i : Fin seeds.count) :
      Metric.diam (product (seeds.unstableFactor i) (seeds.stableFactor i)) < α 5 / 2 := by
    rw [← hrect]
    exact (seeds.rectangle_diam i).trans (div_lt_div_of_pos_right hβ5 (by norm_num))
  have hseedCover : (⋃ i, interior
      (product (seeds.unstableFactor i) (seeds.stableFactor i))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := seeds.interior_cover x
    exact Set.mem_iUnion.mpr ⟨i, by simpa only [hrect] using hi⟩
  have hFmem (q : X) : q ∈ product (seeds.unstableFactor (seeds.select q))
      (seeds.stableFactor (seeds.select q)) := by
    simpa only [hrect] using seeds.selected_membership q
  have hFs (q z : X) (hz : z ∈ Wu γ q ∩ product
      (seeds.unstableFactor (seeds.select q)) (seeds.stableFactor (seeds.select q))) :
      Ws a z ⊆ product (seeds.unstableFactor (seeds.select q))
        (seeds.stableFactor (seeds.select q)) := by
    intro p hp
    rw [← hrect]
    apply seeds.selected_stable_saturation q z
      ⟨by simpa only [hrect] using hz.2, by simpa only [hWu] using hz.1⟩
    rw [hWs]
    exact fun n ↦ (hp n).trans hasat
  have hFu (q z : X) (hz : z ∈ Ws γ q ∩ product
      (seeds.unstableFactor (seeds.select q)) (seeds.stableFactor (seeds.select q))) :
      Wu a z ⊆ product (seeds.unstableFactor (seeds.select q))
        (seeds.stableFactor (seeds.select q)) := by
    intro p hp
    rw [← hrect]
    apply seeds.selected_unstable_saturation q z
      ⟨by simpa only [hrect] using hz.2, by simpa only [hWs] using hz.1⟩
    rw [hWu]
    exact fun n ↦ (hp n).trans hasat
  have hrelative {S B : Set X} (hB : regularFactor S B) :
      B = Bowen.rc S (Bowen.ri S B) := by
    dsimp [Bowen.rc, Bowen.ri]
    rw [Set.preimage_image_eq _ Subtype.val_injective, ← hB.2]
    exact (Set.image_preimage_eq_of_subset (by simpa using hB.1)).symm
  have : Nonempty (Fin seeds.count) := Fin.pos_iff_nonempty.mp seeds.count_pos
  obtain ⟨s, t, target, y, reverseTarget, reverseY, hy, hys, hyr, hyrs,
      hC, hD, hCu, hDs, hCnr, hDnr, hproper, hcover, htransportU, htransportS,
      hcollarU, hcollarS⟩ :=
    Bowen.manning_bowen_iterate_g3_enlarged_rectangles
      f lam γ ε bracket εmod ⟨hlam, hlam1⟩ hγ hε
      (fun x y z n hy hz ↦ by
        simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
          hcontract_s x y z n (by rwa [hws] at hy) (by rwa [hws] at hz))
      (fun x y z n hy hz ↦ by
        simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
          hcontract_u x y z n (by rwa [hwu] at hy) (by rwa [hwu] at hz))
      (fun x y hxy ↦ by simpa only [hws, hwu] using (hunique x y hxy).1)
      (fun x y z hxy hz1 hz2 ↦ (hunique x y hxy).2 z
        ⟨by rwa [hws] at hz1, by rwa [hwu] at hz2⟩)
      hcontinuous (by simpa only [hws, hwu] using hmodulus)
      α hα0 hαpos hαdescending hαscale hαmap
      seeds.center seeds.unstableFactor seeds.stableFactor
      (fun i ↦ ⟨seeds.unstableFactor_nonempty i, seeds.unstableFactor_compact i,
        by simpa only [hwu] using hCsub i,
        by simpa only [hwu] using hrelative (hCreg i), by rw [hwu]; exact hCi i⟩)
      (fun i ↦ ⟨seeds.stableFactor_nonempty i, seeds.stableFactor_compact i,
        by simpa only [hws] using hDsub i,
        by simpa only [hws] using hrelative (hDreg i), by rw [hws]; exact hDi i⟩)
      hseedProper (by change Set.univ ⊆ ⋃ i, interior (product _ _); rw [hseedCover]) hseedDiam
      (by
        intro i q hq z hz
        obtain ⟨c, hc, d, hd, rfl⟩ := hz
        have hdq : d = q := hd
        subst d
        simpa only [hwu, Wu, Set.mem_ofPred_eq] using hseed_u i q (by rwa [hws] at hq) c hc)
      (by
        intro i q hq z hz
        obtain ⟨c, hc, d, hd, rfl⟩ := hz
        have hcq : c = q := hc
        subst c
        simpa only [hws, Ws, Set.mem_ofPred_eq] using hseed_s i q (by rwa [hwu] at hq) d hd)
      a ⟨ha, hasmall⟩ seeds.select hFmem
      (by simpa only [hwu, hws, product, Bowen.bi] using hFs)
      (by simpa only [hwu, hws, product, Bowen.bi] using hFu) m hm htail
  simp_rw [hwu, hws] at hC hD hproper hcover
  let Cseq := Bowen.stage h bracket seeds.unstableFactor s target y
  let Dseq := Bowen.stage h.symm (fun x y ↦ bracket y x)
    seeds.stableFactor t reverseTarget reverseY
  let C := fun i ↦ plaqueClosure (Wu γ (seeds.center i)) (⋃ n, Cseq n i)
  let D := fun i ↦ plaqueClosure (Ws γ (seeds.center i)) (⋃ n, Dseq n i)
  let A := fun i ↦ product (C i) (D i)
  have hCdata (i : Fin seeds.count) : IsCompact (C i) ∧ seeds.unstableFactor i ⊆ C i ∧
      C i ⊆ Wu (2 * α 5) (seeds.center i) ∧
      C i = plaqueClosure (Wu γ (seeds.center i))
        (plaqueInterior (Wu γ (seeds.center i)) (C i)) := by
    simpa only [hwu, C, Cseq, h, Bowen.rc, Bowen.ri, plaqueClosure, plaqueInterior] using hC i
  have hDdata (i : Fin seeds.count) : IsCompact (D i) ∧ seeds.stableFactor i ⊆ D i ∧
      D i ⊆ Ws (2 * α 5) (seeds.center i) ∧
      D i = plaqueClosure (Ws γ (seeds.center i))
        (plaqueInterior (Ws γ (seeds.center i)) (D i)) := by
    simpa only [hws, D, Dseq, h, Bowen.rc, Bowen.ri, plaqueClosure, plaqueInterior] using hD i
  have hAproper (i : Fin seeds.count) : proper (A i) ∧ Metric.diam (A i) < α 4 := by
    simpa only [hwu, hws, A, C, D, Cseq, Dseq, h, product, proper, Bowen.proper, Bowen.bi, Bowen.rc, plaqueClosure] using hproper i
  have hAcover : (⋃ i, A i) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    simpa only [hwu, hws, A, C, D, Cseq, Dseq, h, product, Bowen.bi, Bowen.rc, plaqueClosure] using hcover
  have hβ0 : 0 ≤ lam ^ m := pow_nonneg hlam.le _
  have hβ1 : lam ^ m < 1 := pow_lt_one₀ hlam.le hlam1 (Nat.ne_of_gt hm)
  have hsum (n : ℕ) : (∑ j ∈ Finset.range (n + 1), (lam ^ m) ^ j) < 2 := by
    rw [Finset.sum_range_succ']
    have hb := (((hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (lam ^ m)).summable)
    have hb' : Summable (fun j : ℕ ↦ (lam ^ m) ^ (j + 1)) := by
      simpa only [pow_succ, mul_comm] using hb
    have hh := hb'.sum_le_tsum (Finset.range n) (fun j _ ↦ pow_nonneg hβ0 (j + 1))
    have ht := htail.trans_le (min_le_left _ _)
    norm_num only [pow_zero]
    linarith only [hh,ht]
  have h3γ : 3 * α 5 ≤ γ := by
    have hs := (hαscale 4).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num only [Fin.reduceSucc, Fin.reduceCastSucc] at hs
    linarith
  have hseedSmall : α 7 ≤ 2 * α 5 := by
    linarith [hmono (show (5 : Fin 8) ≤ 7 by decide), hαpos 5]
  have hCstageSlice (n : ℕ) (i : Fin seeds.count) (q : X)
      (hq : q ∈ Ws (2 * α 5) (seeds.center i)) :
      product (Cseq n i) {q} ⊆ Wu (2 * α 5) q := by
    cases n with
    | zero =>
      rintro v ⟨c, hc, d, hd, rfl⟩
      have he : d = q := hd
      subst d
      exact fun k ↦ (hseed_u i q hq c hc k).trans (by linarith only [hαpos 5])
    | succ n =>
      have hh := hCu (n + 1) (by omega) i q (by rwa [hws])
      intro v hv k
      have hb := hh.2.2 (hh.2.1 hv) k
      rw [BowenRegularClosedPreparation.pow_apply_iterate,
        BowenRegularClosedPreparation.pow_apply_iterate] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (hsum (n + 1)).le (hαpos 5).le)
  have hDstageSlice (n : ℕ) (i : Fin seeds.count) (q : X)
      (hq : q ∈ Wu (2 * α 5) (seeds.center i)) :
      product {q} (Dseq n i) ⊆ Ws (2 * α 5) q := by
    cases n with
    | zero =>
      rintro v ⟨c, hc, d, hd, rfl⟩
      have he : c = q := hc
      subst c
      exact fun k ↦ (hseed_s i q hq d hd k).trans (by linarith only [hαpos 5])
    | succ n =>
      have hh := hDs (n + 1) (by omega) i q (by rwa [hwu])
      intro v hv k
      have hb := hh.2.2 (hh.2.1 hv) k
      rw [BowenRegularClosedPreparation.pow_apply_iterate,
        BowenRegularClosedPreparation.pow_apply_iterate] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (hsum (n + 1)).le (hαpos 5).le)
  have hshift (g : X ≃ₜ X) (r : ℝ) (q v : X)
      (hv : ∀ n : ℕ, dist ((g ^ n) v) ((g ^ n) q) ≤ r) :
      ∀ n : ℕ, dist ((g ^ n) ((g ^ m) v)) ((g ^ n) ((g ^ m) q)) ≤ r := by
    intro n
    simpa only [pow_add, Homeomorph.mul_apply] using hv (n + m)
  have hpowInv : f.symm ^ m = h.symm := by
    change (f⁻¹) ^ m = (f ^ m)⁻¹
    exact inv_pow f m
  have hstages (n : ℕ) (i : Fin seeds.count) :
      Cseq n i ⊆ Wu γ (seeds.center i) ∧ Dseq n i ⊆ Ws γ (seeds.center i) := by
    cases n with
    | zero => exact ⟨hCγ i, hDγ i⟩
    | succ n =>
      constructor
      · intro c hc k
        obtain ⟨j, v, hv, rfl⟩ := Set.mem_iUnion.mp hc
        have hq : h (y i j) ∈ Ws (2 * α 5) (seeds.center (target i j)) :=
          fun n ↦ (hDsub _ (hy i j).2.1 n).trans hseedSmall
        have hv' := hCstageSlice n (target i j) (h (y i j)) hq hv
        have hbound := hshift f.symm (2 * α 5) (h (y i j)) v
          (by simpa only [BowenRegularClosedPreparation.pow_apply_iterate, Wu, Set.mem_ofPred_eq] using hv') k
        rw [hpowInv, h.symm_apply_apply] at hbound
        rw [BowenRegularClosedPreparation.pow_apply_iterate,
          BowenRegularClosedPreparation.pow_apply_iterate] at hbound
        have hbase := (hy i j).1 k
        rw [BowenRegularClosedPreparation.pow_apply_iterate,
          BowenRegularClosedPreparation.pow_apply_iterate] at hbase
        exact (dist_triangle _ ((f.symm : X → X)^[k] (y i j)) _).trans
          ((add_le_add hbound hbase).trans (by linarith only [h3γ]))
      · intro d hd k
        obtain ⟨j, v, hv, rfl⟩ := Set.mem_iUnion.mp hd
        have hq : h.symm (reverseY i j) ∈ Wu (2 * α 5)
            (seeds.center (reverseTarget i j)) :=
          fun n ↦ (hCsub _ (hyr i j).2.1 n).trans hseedSmall
        have hv' : v ∈ product {h.symm (reverseY i j)} (Dseq n (reverseTarget i j)) := by
          obtain ⟨c, hc, e, he, hce⟩ := hv
          exact ⟨e, he, c, hc, hce⟩
        have hv'' := hDstageSlice n (reverseTarget i j) (h.symm (reverseY i j)) hq hv'
        have hbound := hshift f (2 * α 5) (h.symm (reverseY i j)) v
          (by simpa only [BowenRegularClosedPreparation.pow_apply_iterate, Ws, Set.mem_ofPred_eq] using hv'') k
        change dist ((f ^ k) (h v)) ((f ^ k) (h (h.symm (reverseY i j)))) ≤ _ at hbound
        have hbound : dist ((f : X → X)^[k] (h v))
            ((f : X → X)^[k] (reverseY i j)) ≤ 2 * α 5 := by
          simpa only [h, Homeomorph.apply_symm_apply,
            BowenRegularClosedPreparation.pow_apply_iterate] using hbound
        have hbase := (hyr i j).1 k
        rw [BowenRegularClosedPreparation.pow_apply_iterate,
          BowenRegularClosedPreparation.pow_apply_iterate] at hbase
        exact (dist_triangle _ ((f : X → X)^[k] (reverseY i j)) _).trans
          ((add_le_add hbound hbase).trans (by linarith only [h3γ]))
  clear hCu hDs hCnr hDnr htransportU htransportS hC hD hproper hcover
  have hclosedWs (r : ℝ) (x : X) : IsClosed (Ws r x) := by
    simp only [Ws, Set.ofPred_forall]
    exact isClosed_iInter fun n ↦ isClosed_le
      ((f.continuous.iterate n).dist continuous_const) continuous_const
  have hclosedWu (r : ℝ) (x : X) : IsClosed (Wu r x) := by
    simp only [Wu, Set.ofPred_forall]
    exact isClosed_iInter fun n ↦ isClosed_le
      ((f.symm.continuous.iterate n).dist continuous_const) continuous_const
  have hrelativeReg {S B : Set X} (hBS : B ⊆ S)
      (hB : B = plaqueClosure S (plaqueInterior S B)) : regularFactor S B := by
    refine ⟨hBS, ?_⟩
    have he := congrArg (fun A : Set X ↦ (Subtype.val : S → X) ⁻¹' A) hB
    simpa only [plaqueClosure, plaqueInterior, Set.preimage_image_eq _ Subtype.val_injective] using he
  have hfactorSmall : 2 * α 5 ≤ α 3 / 3 := by
    have hs := (hαscale 3).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num only [Fin.reduceSucc, Fin.reduceCastSucc] at hs
    have hd : α 5 < α 4 := hαdescending 4
    linarith
  have hClimitReg (i : Fin seeds.count) : regularFactor (Wu γ (seeds.center i)) (C i) :=
    hrelativeReg (fun c hc n ↦ ((hCdata i).2.2.1 hc n).trans (by linarith only [h3γ,hαpos 5]))
      (hCdata i).2.2.2
  have hDlimitReg (i : Fin seeds.count) : regularFactor (Ws γ (seeds.center i)) (D i) :=
    hrelativeReg (fun c hc n ↦ ((hDdata i).2.2.1 hc n).trans (by linarith only [h3γ,hαpos 5]))
      (hDdata i).2.2.2
  choose Eu hEuγ hEuo hEuinner hEuouter using fun i : Fin seeds.count ↦
    unstableCollar (seeds.center i)
  choose Es hEsγ hEso hEsinner hEsouter using fun i : Fin seeds.count ↦
    stableCollar (seeds.center i)
  let Cu : Fin seeds.count → Bool → Set X := fun i σ ↦ if σ then C i else
    plaqueClosure (Wu γ (seeds.center i)) (Eu i \ C i)
  let Ds : Fin seeds.count → Bool → Set X := fun i τ ↦ if τ then D i else
    plaqueClosure (Ws γ (seeds.center i)) (Es i \ D i)
  let Quad := fun i σ τ ↦ product (Cu i σ) (Ds i τ)
  have hnegative {S B E T : Set X} (hS : IsClosed S) (hT : IsClosed T)
      (hTS : T ⊆ S) (hB : regularFactor S B)
      (hE : IsOpen ((Subtype.val : S → X) ⁻¹' E)) (hET : E ⊆ T) :
      IsCompact (plaqueClosure S (E \ B)) ∧
      regularFactor S (plaqueClosure S (E \ B)) ∧
      plaqueClosure S (E \ B) ⊆ T ∧
      Disjoint (plaqueInterior S (plaqueClosure S (E \ B))) B ∧
      E ⊆ B ∪ plaqueClosure S (E \ B) := by
    have hn := Topology.regularClosed_collar_complement
      ((Subtype.val : S → X) ⁻¹' B) ((Subtype.val : S → X) ⁻¹' E) hB.2 hE
    have hsub : plaqueClosure S (E \ B) ⊆ T := by
      rintro z ⟨v, hv, rfl⟩
      exact closure_minimal
        (show (Subtype.val : S → X) ⁻¹' (E \ B) ⊆ Subtype.val ⁻¹' T from
          fun v hv ↦ hET hv.1) (hT.preimage continuous_subtype_val) hv
    have hclosed : IsClosed (plaqueClosure S (E \ B)) :=
      hS.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure
    refine ⟨hclosed.isCompact, ⟨hsub.trans hTS, ?_⟩, hsub, ?_, ?_⟩
    · simpa only [plaqueClosure, Set.preimage_image_eq _ Subtype.val_injective,
        Set.preimage_sdiff] using hn.1
    · rw [Set.disjoint_left]
      rintro z ⟨v, hv, rfl⟩ hz
      have hv' : v ∈ interior (closure
          ((Subtype.val : S → X) ⁻¹' E \ Subtype.val ⁻¹' B)) := by
        simpa only [plaqueClosure, Set.preimage_image_eq _ Subtype.val_injective,
          Set.preimage_sdiff] using hv
      exact Set.disjoint_left.mp hn.2.1 hv' hz
    · intro z hz
      by_cases hb : z ∈ B
      · exact Or.inl hb
      · exact Or.inr ⟨⟨z, hTS (hET hz)⟩, subset_closure ⟨hz, hb⟩, rfl⟩
  have hCuData (i : Fin seeds.count) (σ : Bool) :
      IsCompact (Cu i σ) ∧ regularFactor (Wu γ (seeds.center i)) (Cu i σ) ∧
      Cu i σ ⊆ Wu (2 * α 3 / 3) (seeds.center i) := by
    cases σ with
    | false =>
      have hn := hnegative (hclosedWu γ (seeds.center i))
        (hclosedWu (2 * α 3 / 3) (seeds.center i))
        (fun c hc n ↦ (hc n).trans hRγ) (hClimitReg i) (hEuo i) (hEuouter i)
      exact ⟨hn.1, hn.2.1, hn.2.2.1⟩
    | true =>
      exact ⟨(hCdata i).1, hClimitReg i,
        fun c hc n ↦ ((hCdata i).2.2.1 hc n).trans (by linarith only [hαpos 3,hfactorSmall])⟩
  have hDsData (i : Fin seeds.count) (τ : Bool) :
      IsCompact (Ds i τ) ∧ regularFactor (Ws γ (seeds.center i)) (Ds i τ) ∧
      Ds i τ ⊆ Ws (2 * α 3 / 3) (seeds.center i) := by
    cases τ with
    | false =>
      have hn := hnegative (hclosedWs γ (seeds.center i))
        (hclosedWs (2 * α 3 / 3) (seeds.center i))
        (fun c hc n ↦ (hc n).trans hRγ) (hDlimitReg i) (hEso i) (hEsouter i)
      exact ⟨hn.1, hn.2.1, hn.2.2.1⟩
    | true =>
      exact ⟨(hDdata i).1, hDlimitReg i,
        fun c hc n ↦ ((hDdata i).2.2.1 hc n).trans (by linarith only [hαpos 3,hfactorSmall])⟩
  have hprodMono {B B' E E' : Set X} (hB : B ⊆ B') (hE : E ⊆ E') :
      product B E ⊆ product B' E' := by
    rintro z ⟨b, hb, e, he, rfl⟩
    exact ⟨b, hB hb, e, hE he, rfl⟩
  have hriSub (S B : Set X) : plaqueInterior S B ⊆ B := by
    rintro z ⟨v, hv, rfl⟩
    exact @interior_subset S _ ((Subtype.val : S → X) ⁻¹' B) v hv
  have hscale (i : Fin 7) : 3 * α i.succ < α i.castSucc / 3 ∧
      3 * α i.succ < εmod (α i.castSucc / 3) := by
    have hh := hαscale i
    have h1 := min_le_left (α i.castSucc / 3) (εmod (α i.castSucc / 3))
    have h2 := min_le_right (α i.castSucc / 3) (εmod (α i.castSucc / 3))
    constructor <;> linarith only [hh,h1,h2]
  have hproductData (x : X) (B E : Set X) (hBc : IsCompact B) (hEc : IsCompact E)
      (hBr : regularFactor (Wu γ x) B) (hEr : regularFactor (Ws γ x) E)
      (hBs : B ⊆ Wu (2 * α 3 / 3) x) (hEs : E ⊆ Ws (2 * α 3 / 3) x) :
      IsCompact (product B E) ∧ product B E = closure (interior (product B E)) ∧
      interior (product B E) = product (plaqueInterior (Wu γ x) B)
        (plaqueInterior (Ws γ x) E) ∧
      (∀ c ∈ B, ∀ d ∈ E,
        bracket (bracket c d) x = c ∧ bracket x (bracket c d) = d) ∧
      (∀ z ∈ product B E, bracket z x ∈ B ∧ bracket x z ∈ E ∧
        bracket (bracket z x) (bracket x z) = z) := by
    have h32 : 2 * α 3 / 3 < α 2 := by
      have hs : 3 * α 3 < α 2 / 3 := (hscale 2).1
      linarith [hαpos 3]
    obtain ⟨U, hUγ, hUo, hUin, hUout⟩ := bowen_orbit_plaque_open_collar
      (f.symm : X → X) hlam.le hlam1.le (by linarith only [hαpos 3] : 0 ≤ 2 * α 3 / 3)
      h32 hα2γ.le hcontract_u x
    obtain ⟨V, hVγ, hVo, hVin, hVout⟩ := bowen_orbit_plaque_open_collar
      (f : X → X) hlam.le hlam1.le (by linarith only [hαpos 3] : 0 ≤ 2 * α 3 / 3)
      h32 hα2γ.le hcontract_s x
    have hBU : B ⊆ U := hBs.trans hUin
    have hEV : E ⊆ V := hEs.trans hVin
    have hch := hcharts.2 x U V hUout hVout hUo hVo
    change IsOpen (product U V) ∧ ∃ chart :
      ({u : Wu γ x // (u : X) ∈ U} × {v : Ws γ x // (v : X) ∈ V}) ≃ₜ product U V,
      (∀ p, (chart p : X) = bracket p.1.val.val p.2.val.val) ∧
      (∀ z : product U V, (chart.symm z).1.val.val = bracket z.val x ∧
        (chart.symm z).2.val.val = bracket x z.val) at hch
    obtain ⟨hUV, chart, hchart, hinv⟩ := hch
    let CU : Set {u : Wu γ x // (u : X) ∈ U} := {u | (u.val : X) ∈ B}
    let DV : Set {v : Ws γ x // (v : X) ∈ V} := {v | (v.val : X) ∈ E}
    let map := (Subtype.val : product U V → X) ∘ chart
    have hmapC : Continuous map := continuous_subtype_val.comp chart.continuous
    have hmapO : IsOpenMap map := hUV.isOpenMap_subtype_val.comp chart.isOpenMap
    have hmapI : Function.Injective map := Subtype.val_injective.comp chart.injective
    have himage (B' E' : Set X) (hB' : B' ⊆ U) (hE' : E' ⊆ V) :
        map '' ({u : {u : Wu γ x // (u : X) ∈ U} | (u.val : X) ∈ B'} ×ˢ
          {v : {v : Ws γ x // (v : X) ∈ V} | (v.val : X) ∈ E'}) = product B' E' := by
      ext z
      constructor
      · rintro ⟨⟨u,v⟩, ⟨hu,hv⟩, rfl⟩
        exact ⟨u.val.val, hu, v.val.val, hv, (hchart (u,v)).symm⟩
      · rintro ⟨u, hu, v, hv, rfl⟩
        exact ⟨(⟨⟨u, hUγ (hB' hu)⟩, hB' hu⟩, ⟨⟨v, hVγ (hE' hv)⟩, hE' hv⟩),
          ⟨hu,hv⟩, hchart _⟩
    have hcomp : IsCompact (product B E) := by
      have hα1γ : α 1 ≤ γ := (hmono (Fin.zero_le _)).trans_eq hα0
      have hct := hcharts.1 (α 1 / 3) (by linarith only [hαpos 1]) (by linarith only [hα1γ,hαpos 1])
      have hbpair : B ×ˢ E ⊆ {p : X × X | dist p.1 p.2 ≤ εmod (α 1 / 3)} := by
        rintro ⟨b,e⟩ ⟨hb,he⟩
        have hd1 : dist b x ≤ α 2 := hUout (hBU hb) 0
        have hd2 : dist e x ≤ α 2 := hVout (hEV he) 0
        have hs : 3 * α 2 < εmod (α 1 / 3) := (hscale 1).2
        have ht := dist_triangle b x e
        rw [dist_comm x e] at ht
        change dist b e ≤ εmod (α 1 / 3)
        linarith [hαpos 2]
      have heq : (fun p : X × X ↦ bracket p.1 p.2) '' (B ×ˢ E) = product B E := by
        ext z
        constructor
        · rintro ⟨⟨b,e⟩, ⟨hb,he⟩, hh⟩
          exact ⟨b,hb,e,he,hh⟩
        · rintro ⟨b,hb,e,he,hh⟩
          exact ⟨(b,e),⟨hb,he⟩,hh⟩
      rw [← heq]
      exact (hBc.prod hEc).image_of_continuousOn (hct.mono hbpair)
    have hCUreg : CU = closure (interior CU) :=
      BowenRegularClosedPreparation.regular_preimage continuous_subtype_val
        hUo.isOpenMap_subtype_val hBr.2
    have hDVreg : DV = closure (interior DV) :=
      BowenRegularClosedPreparation.regular_preimage continuous_subtype_val
        hVo.isOpenMap_subtype_val hEr.2
    have hreg : product B E = closure (interior (product B E)) := by
      rw [← himage B E hBU hEV]
      apply BowenRegularClosedPreparation.regular_image hmapC hmapO
        (BowenRegularClosedPreparation.regular_product hCUreg hDVreg)
      apply (_root_.Topology.IsEmbedding.subtypeVal.comp chart.isEmbedding).isCompact_iff.mpr
      rw [himage B E hBU hEV]
      exact hcomp
    have hpre : map ⁻¹' product B E = CU ×ˢ DV := by
      rw [← himage B E hBU hEV, Set.preimage_image_eq _ hmapI]
    have hpreInt : map ⁻¹' interior (product B E) = interior CU ×ˢ interior DV := by
      rw [hmapO.preimage_interior_eq_interior_preimage hmapC, hpre, interior_prod_eq]
    have hCUint : {u : {u : Wu γ x // (u : X) ∈ U} |
        (u.val : X) ∈ plaqueInterior (Wu γ x) B} = interior CU := by
      change (Subtype.val : {u : Wu γ x // (u : X) ∈ U} → Wu γ x) ⁻¹'
        ((Subtype.val : Wu γ x → X) ⁻¹' plaqueInterior (Wu γ x) B) = _
      simp only [plaqueInterior, Set.preimage_image_eq _ Subtype.val_injective]
      exact hUo.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
        continuous_subtype_val _
    have hDVint : {v : {v : Ws γ x // (v : X) ∈ V} |
        (v.val : X) ∈ plaqueInterior (Ws γ x) E} = interior DV := by
      change (Subtype.val : {v : Ws γ x // (v : X) ∈ V} → Ws γ x) ⁻¹'
        ((Subtype.val : Ws γ x → X) ⁻¹' plaqueInterior (Ws γ x) E) = _
      simp only [plaqueInterior, Set.preimage_image_eq _ Subtype.val_injective]
      exact hVo.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
        continuous_subtype_val _
    refine ⟨hcomp, hreg, ?_, ?_, ?_⟩
    · rw [← himage _ _ ((hriSub _ _).trans hBU) ((hriSub _ _).trans hEV),
        hCUint, hDVint, ← hpreInt]
      exact (Set.image_preimage_eq_of_subset (interior_subset.trans (by
        rw [← himage B E hBU hEV]
        exact Set.image_subset_range _ _))).symm
    · intro c hc d hd
      let p : {u : Wu γ x // (u : X) ∈ U} × {v : Ws γ x // (v : X) ∈ V} :=
        (⟨⟨c,hBr.1 hc⟩,hBU hc⟩,⟨⟨d,hEr.1 hd⟩,hEV hd⟩)
      have hp := hinv (chart p)
      have hcq := hchart p
      constructor
      · simpa only [chart.symm_apply_apply, hcq] using hp.1.symm
      · simpa only [chart.symm_apply_apply, hcq] using hp.2.symm
    · intro z hz
      have hzUV := hprodMono hBU hEV hz
      have hp := hinv ⟨z,hzUV⟩
      have hzi : chart.symm ⟨z,hzUV⟩ ∈ CU ×ˢ DV := by
        rw [← hpre]
        change ((chart (chart.symm ⟨z,hzUV⟩) : product U V) : X) ∈ product B E
        simpa only [chart.apply_symm_apply] using hz
      refine ⟨hp.1 ▸ hzi.1, hp.2 ▸ hzi.2, ?_⟩
      have hh := hchart (chart.symm ⟨z,hzUV⟩)
      simpa only [chart.apply_symm_apply, hp.1, hp.2] using hh.symm
  have hQdata (i : Fin seeds.count) (σ τ : Bool) := hproductData
    (seeds.center i) (Cu i σ) (Ds i τ) (hCuData i σ).1 (hDsData i τ).1
    (hCuData i σ).2.1 (hDsData i τ).2.1 (hCuData i σ).2.2 (hDsData i τ).2.2
  have hQint (i : Fin seeds.count) (σ τ : Bool) (z : X)
      (hz : z ∈ interior (Quad i σ τ)) :
      bracket z (seeds.center i) ∈ plaqueInterior (Wu γ (seeds.center i)) (Cu i σ) ∧
      bracket (seeds.center i) z ∈ plaqueInterior (Ws γ (seeds.center i)) (Ds i τ) := by
    rw [(hQdata i σ τ).2.2.1] at hz
    obtain ⟨c,hc,d,hd,rfl⟩ := hz
    have hp := (hQdata i σ τ).2.2.2.1 c (hriSub _ _ hc) d (hriSub _ _ hd)
    rw [hp.1, hp.2]
    exact ⟨hc, hd⟩
  have hUsep (i : Fin seeds.count) :
      Disjoint (plaqueInterior (Wu γ (seeds.center i)) (Cu i false)) (C i) :=
    (hnegative (hclosedWu γ (seeds.center i))
      (hclosedWu (2 * α 3 / 3) (seeds.center i))
      (fun c hc n ↦ (hc n).trans hRγ) (hClimitReg i) (hEuo i) (hEuouter i)).2.2.2.1
  have hSsep (i : Fin seeds.count) :
      Disjoint (plaqueInterior (Ws γ (seeds.center i)) (Ds i false)) (D i) :=
    (hnegative (hclosedWs γ (seeds.center i))
      (hclosedWs (2 * α 3 / 3) (seeds.center i))
      (fun c hc n ↦ (hc n).trans hRγ) (hDlimitReg i) (hEso i) (hEsouter i)).2.2.2.1
  have hUintSep (i : Fin seeds.count) : Pairwise fun σ τ ↦
      Disjoint (plaqueInterior (Wu γ (seeds.center i)) (Cu i σ))
        (plaqueInterior (Wu γ (seeds.center i)) (Cu i τ)) := by
    intro σ τ hne
    cases σ <;> cases τ
    · exact (hne rfl).elim
    · exact (hUsep i).mono_right (hriSub _ _)
    · exact ((hUsep i).mono_right (hriSub _ _)).symm
    · exact (hne rfl).elim
  have hSintSep (i : Fin seeds.count) : Pairwise fun σ τ ↦
      Disjoint (plaqueInterior (Ws γ (seeds.center i)) (Ds i σ))
        (plaqueInterior (Ws γ (seeds.center i)) (Ds i τ)) := by
    intro σ τ hne
    cases σ <;> cases τ
    · exact (hne rfl).elim
    · exact (hSsep i).mono_right (hriSub _ _)
    · exact ((hSsep i).mono_right (hriSub _ _)).symm
    · exact (hne rfl).elim
  have hQdisjoint (i : Fin seeds.count) : Pairwise fun a b : Bool × Bool ↦
      Disjoint (interior (Quad i a.1 a.2)) (interior (Quad i b.1 b.2)) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro z hza hzb
    have ha := hQint i a.1 a.2 z hza
    have hb := hQint i b.1 b.2 z hzb
    have he1 : a.1 = b.1 := by
      by_contra hn
      exact Set.disjoint_left.mp (hUintSep i hn) ha.1 hb.1
    have he2 : a.2 = b.2 := by
      by_contra hn
      exact Set.disjoint_left.mp (hSintSep i hn) ha.2 hb.2
    exact hab (Prod.ext he1 he2)
  have hA0sub (i : Fin seeds.count) :
      product (seeds.unstableFactor i) (seeds.stableFactor i) ⊆ A i :=
    hprodMono (hCdata i).2.1 (hDdata i).2.1
  have hAcenter (i : Fin seeds.count) : seeds.center i ∈ interior (A i) :=
    interior_mono (hA0sub i) (by simpa only [hrect] using seeds.center_interior i)
  let V := fun i ↦ ⋃ j, ⋃ (_ : (A i ∩ A j).Nonempty), A j
  let N := fun q ↦ {i | q ∈ V i}
  have hcollar (i : Fin seeds.count) (q : X)
      (hd : dist q (seeds.center i) < 3 * α 4) (hc : bracket q (seeds.center i) ∈ C i) :
      ∃ j ∈ N (h q), h q ∈ product (C j) {h q} ∧
        product (C j) {h q} ⊆ h '' product (C i) {q} ∧
        h.symm '' plaqueInterior (Wu γ (h q)) (product (C j) {h q}) ⊆
          plaqueInterior (Wu γ q) (product (C i) {q}) := by
    simp_rw [hwu,hws] at hcollarU
    obtain ⟨j,⟨k,hjk,hqk⟩,hjmem,hjsub,hjint⟩ := hcollarU i q hd hc
    exact ⟨j,Set.mem_iUnion₂.mpr ⟨k,hjk,hqk⟩,hjmem,hjsub,hjint⟩
  have hcollarSLocal (i : Fin seeds.count) (q : X)
      (hd : dist q (seeds.center i) < 3 * α 4) (hc : bracket (seeds.center i) q ∈ D i) :
      ∃ j ∈ N (h.symm q), h.symm q ∈ product {h.symm q} (D j) ∧
        product {h.symm q} (D j) ⊆ h.symm '' product {q} (D i) ∧
        h '' plaqueInterior (Ws γ (h.symm q)) (product {h.symm q} (D j)) ⊆
          plaqueInterior (Ws γ q) (product {q} (D i)) := by
    simp_rw [hwu,hws] at hcollarS
    obtain ⟨j,⟨k,hjk,hqk⟩,hjmem,hjsub,hjint⟩ := hcollarS i q hd hc
    exact ⟨j,Set.mem_iUnion₂.mpr ⟨k,hjk,hqk⟩,hjmem,hjsub,hjint⟩
  have hCseqDef : Cseq = Bowen.stage h bracket seeds.unstableFactor s target y := rfl
  have hDseqDef : Dseq = Bowen.stage h.symm (fun x y ↦ bracket y x)
      seeds.stableFactor t reverseTarget reverseY := rfl
  have hCDef : C = fun i ↦ plaqueClosure (Wu γ (seeds.center i)) (⋃ n, Cseq n i) := rfl
  have hDDef : D = fun i ↦ plaqueClosure (Ws γ (seeds.center i)) (⋃ n, Dseq n i) := rfl
  clear hcollarU hcollarS
  clear_value C D Cseq Dseq
  have hVdist (i : Fin seeds.count) (q : X) (hq : q ∈ V i) :
      dist q (seeds.center i) < 2 * α 4 := by
    obtain ⟨j, ⟨v,hvi,hvj⟩, hqj⟩ := Set.mem_iUnion₂.mp hq
    have h1 := Metric.dist_le_diam_of_mem (hAproper j).1.2.1.isBounded hqj hvj
    have h2 := Metric.dist_le_diam_of_mem (hAproper i).1.2.1.isBounded hvi
      (interior_subset (hAcenter i))
    have ht := dist_triangle q v (seeds.center i)
    linarith only [h1,h2,ht,(hAproper j).2,(hAproper i).2]
  have hsmallProj (x q : X) (hq : dist q x < 3 * α 4) :
      bracket q x ∈ Wu (α 3 / 3) x ∧ bracket x q ∈ Ws (α 3 / 3) x ∧
      bracket (bracket q x) (bracket x q) = q := by
    have hs3 : 3 * α 4 < εmod (α 3 / 3) := (hscale 3).2
    have hqp := (hmodulus (α 3 / 3) (by linarith only [hαpos 3]) (by linarith only [hα3γ,hαpos 3])).2
      q x (hq.le.trans hs3.le)
    have hpq := (hmodulus (α 3 / 3) (by linarith only [hαpos 3]) (by linarith only [hα3γ,hαpos 3])).2
      x q (by simpa only [dist_comm] using hq.le.trans hs3.le)
    refine ⟨hqp.2, hpq.1, ?_⟩
    have hd : dist (bracket q x) (bracket x q) ≤ 2 * (α 3 / 3) := by
      have h1 := hqp.2 0
      have h2 := hpq.1 0
      have ht := dist_triangle (bracket q x) x (bracket x q)
      simp only [Function.iterate_zero_apply] at h1 h2
      rw [dist_comm x (bracket x q)] at ht
      linarith
    have hs2 : 3 * α 3 < εmod (α 2 / 3) := (hscale 2).2
    have hp := (hmodulus (α 2 / 3) (by linarith only [hαpos 2]) (by linarith only [hα2γ,hαpos 2])).2
      (bracket q x) (bracket x q) (hd.trans (by linarith only [hαpos 3,hs2]))
    refine ((hunique q q (by simpa using hε.le)).2 _ ?_).trans (hdiag q)
    constructor
    · intro n
      exact (dist_triangle _ ((f : X → X)^[n] (bracket q x)) _).trans
        ((add_le_add (hp.1 n) (hqp.1 n)).trans (by linarith only [hα2γ,hα3γ,hγ]))
    · intro n
      exact (dist_triangle _ ((f.symm : X → X)^[n] (bracket x q)) _).trans
        ((add_le_add (hp.2 n) (hpq.2 n)).trans (by linarith only [hα2γ,hα3γ,hγ]))
  have hQcover (i : Fin seeds.count) : V i ⊆ ⋃ a : Bool × Bool, Quad i a.1 a.2 := by
    intro q hq
    have hp := hsmallProj (seeds.center i) q
      ((hVdist i q hq).trans (by linarith only [hαpos 4]))
    have hc : ∃ σ, bracket q (seeds.center i) ∈ Cu i σ := by
      by_cases hc : bracket q (seeds.center i) ∈ C i
      · exact ⟨true,hc⟩
      · exact ⟨false, ⟨⟨_, fun n ↦ (hp.1 n).trans (by linarith only [hα3γ,hαpos 3])⟩,
          subset_closure ⟨hEuinner i hp.1,hc⟩,rfl⟩⟩
    have hd : ∃ τ, bracket (seeds.center i) q ∈ Ds i τ := by
      by_cases hd : bracket (seeds.center i) q ∈ D i
      · exact ⟨true,hd⟩
      · exact ⟨false, ⟨⟨_, fun n ↦ (hp.2.1 n).trans (by linarith only [hα3γ,hαpos 3])⟩,
          subset_closure ⟨hEsinner i hp.2.1,hd⟩,rfl⟩⟩
    obtain ⟨σ,hc⟩ := hc
    obtain ⟨τ,hd⟩ := hd
    exact Set.mem_iUnion.mpr ⟨(σ,τ),_,hc,_,hd,hp.2.2⟩
  have hcross (x c₁ c₂ d₁ d₂ : X)
      (hc₁ : c₁ ∈ Wu (2 * α 3 / 3) x) (hc₂ : c₂ ∈ Wu (2 * α 3 / 3) x)
      (hd₁ : d₁ ∈ Ws (2 * α 3 / 3) x) (hd₂ : d₂ ∈ Ws (2 * α 3 / 3) x) :
      bracket (bracket c₁ d₁) (bracket c₂ d₂) = bracket c₁ d₂ := by
    have hα1γ : α 1 ≤ γ := (hmono (Fin.zero_le _)).trans_eq hα0
    have h12 : 3 * α 2 < α 1 / 3 := (hscale 1).1
    have h23 : 3 * α 3 < α 2 / 3 := (hscale 2).1
    have h0 : 3 * α 1 < εmod (γ / 3) := by simpa only [Fin.succ_zero_eq_one, Fin.castSucc_zero, hα0] using (hscale 0).2
    have h1 : 3 * α 2 < εmod (α 1 / 3) := (hscale 1).2
    have hpair (c d : X) (hc : c ∈ Wu (2 * α 3 / 3) x)
        (hd : d ∈ Ws (2 * α 3 / 3) x) :
        bracket c d ∈ Ws (α 1 / 3) c ∩ Wu (α 1 / 3) d := by
      apply (hmodulus (α 1 / 3) (by linarith only [hαpos 1]) (by linarith only [hα1γ,hαpos 1])).2
      have ht := dist_triangle c x d
      rw [dist_comm x d] at ht
      have hc0 : dist c x ≤ 2 * α 3 / 3 := hc 0
      have hd0 : dist d x ≤ 2 * α 3 / 3 := hd 0
      linarith [hαpos 2, hαpos 3]
    have hp := hpair c₁ d₁ hc₁ hd₁
    have hq := hpair c₂ d₂ hc₂ hd₂
    have hr := hpair c₁ d₂ hc₁ hd₂
    have hd : dist (bracket c₁ d₁) (bracket c₂ d₂) ≤ εmod (γ / 3) := by
      have hcc := dist_triangle c₁ x c₂
      rw [dist_comm x c₂] at hcc
      have ht1 := dist_triangle (bracket c₁ d₁) c₁ (bracket c₂ d₂)
      have ht2 := dist_triangle c₁ c₂ (bracket c₂ d₂)
      rw [dist_comm c₂ (bracket c₂ d₂)] at ht2
      have hcp : dist (bracket c₁ d₁) c₁ ≤ α 1 / 3 := hp.1 0
      have hcq : dist (bracket c₂ d₂) c₂ ≤ α 1 / 3 := hq.1 0
      have hc10 : dist c₁ x ≤ 2 * α 3 / 3 := hc₁ 0
      have hc20 : dist c₂ x ≤ 2 * α 3 / 3 := hc₂ 0
      linarith [hαpos 1]
    have hout := (hmodulus (γ / 3) (by linarith only [hγ]) (by linarith only [hγ])).2 _ _ hd
    refine ((hunique (bracket c₁ d₂) (bracket c₁ d₂) (by simpa using hε.le)).2 _ ?_).trans
      (hdiag _)
    constructor
    · intro n
      have h1 := dist_triangle ((f : X → X)^[n] (bracket (bracket c₁ d₁) (bracket c₂ d₂)))
        ((f : X → X)^[n] (bracket c₁ d₁)) ((f : X → X)^[n] (bracket c₁ d₂))
      have h2 := dist_triangle ((f : X → X)^[n] (bracket c₁ d₁))
        ((f : X → X)^[n] c₁) ((f : X → X)^[n] (bracket c₁ d₂))
      rw [dist_comm ((f : X → X)^[n] c₁) _] at h2
      linarith only [h1,h2,hout.1 n,hp.1 n,hr.1 n,hα1γ]
    · intro n
      have h1 := dist_triangle ((f.symm : X → X)^[n] (bracket (bracket c₁ d₁) (bracket c₂ d₂)))
        ((f.symm : X → X)^[n] (bracket c₂ d₂)) ((f.symm : X → X)^[n] (bracket c₁ d₂))
      have h2 := dist_triangle ((f.symm : X → X)^[n] (bracket c₂ d₂))
        ((f.symm : X → X)^[n] d₂) ((f.symm : X → X)^[n] (bracket c₁ d₂))
      rw [dist_comm ((f.symm : X → X)^[n] d₂) _] at h2
      linarith only [h1,h2,hout.2 n,hq.2 n,hr.2 n,hα1γ]
  have hQintBracket (i : Fin seeds.count) (σ τ : Bool) :
      ∀ x ∈ interior (Quad i σ τ), ∀ y ∈ interior (Quad i σ τ),
        bracket x y ∈ interior (Quad i σ τ) := by
    intro x hx y hy
    rw [(hQdata i σ τ).2.2.1] at hx hy ⊢
    obtain ⟨c₁,hc₁,d₁,hd₁,rfl⟩ := hx
    obtain ⟨c₂,hc₂,d₂,hd₂,rfl⟩ := hy
    exact ⟨c₁,hc₁,d₂,hd₂,(hcross (seeds.center i) c₁ c₂ d₁ d₂
      ((hCuData i σ).2.2 (hriSub _ _ hc₁)) ((hCuData i σ).2.2 (hriSub _ _ hc₂))
      ((hDsData i τ).2.2 (hriSub _ _ hd₁)) ((hDsData i τ).2.2 (hriSub _ _ hd₂))).symm⟩
  let Z := (⋃ i, ⋃ σ : Bool, ⋃ τ : Bool, frontier (Quad i σ τ))ᶜ
  let chosen := fun z i ↦ ⋃ σ : Bool, ⋃ τ : Bool,
    ⋃ (_ : z ∈ interior (Quad i σ τ)), interior (Quad i σ τ)
  let O := fun z ↦ ⋂ i, ⋂ (_ : i ∈ N z), chosen z i
  let P := fun z ↦ closure (O z)
  have hfinite := Topology.finite_closed_quadrant_atoms
    (fun i (a : Bool × Bool) ↦ Quad i a.1 a.2) V
    (fun i a ↦ (hQdata i a.1 a.2).1.isClosed) hQdisjoint hQcover
  simp only [Set.iUnion_prod'] at hfinite
  change IsOpen Z ∧ Dense Z ∧
    (∀ z ∈ Z, ∀ i, i ∈ N z → ∃! a : Bool × Bool, z ∈ interior (Quad i a.1 a.2)) ∧
    (∀ z ∈ Z, IsOpen (O z) ∧ z ∈ O z) ∧
    (Set.range P).Finite ∧ (⋃ z ∈ Z, P z) = Set.univ at hfinite
  obtain ⟨hZo,hZd,hchoice,hOneigh,hPfinite,hPcover⟩ := hfinite
  have hchosenEq (z : X) (hz : z ∈ Z) (i : Fin seeds.count) (hi : i ∈ N z)
      (a : Bool × Bool) (ha : z ∈ interior (Quad i a.1 a.2)) :
      chosen z i = interior (Quad i a.1 a.2) := by
    ext w
    constructor
    · intro hw
      obtain ⟨σ,τ,hb⟩ := Set.mem_iUnion₂.mp hw
      obtain ⟨hbz,hbw⟩ := Set.mem_iUnion.mp hb
      have he : (σ,τ) = a := (hchoice z hz i hi).unique hbz ha
      have he1 : σ = a.1 := congrArg Prod.fst he
      have he2 : τ = a.2 := congrArg Prod.snd he
      simpa only [he1,he2] using hbw
    · intro hw
      exact Set.mem_iUnion₂.mpr ⟨a.1,a.2,Set.mem_iUnion.mpr ⟨ha,hw⟩⟩
  have hOsub (z : X) (i : Fin seeds.count) (hi : i ∈ N z) : O z ⊆ chosen z i :=
    fun w hw ↦ Set.mem_iInter₂.mp hw i hi
  have hOregular (z : X) (hz : z ∈ Z) : interior (P z) = O z := by
    apply Set.Subset.antisymm
    · intro w hw
      apply Set.mem_iInter₂.mpr
      intro i hi
      obtain ⟨a,ha,_⟩ := hchoice z hz i hi
      rw [hchosenEq z hz i hi a ha]
      apply interior_mono (closure_minimal
        ((hOsub z i hi).trans (by rw [hchosenEq z hz i hi a ha]; exact interior_subset))
        (hQdata i a.1 a.2).1.isClosed) hw
    · exact (hOneigh z hz).1.subset_interior_closure
  have hselfN (i : Fin seeds.count) (z : X) (hz : z ∈ A i) : i ∈ N z :=
    Set.mem_iUnion₂.mpr ⟨i,⟨z,hz,hz⟩,hz⟩
  have hZinterior (z : X) (hz : z ∈ Z) (i : Fin seeds.count) (σ τ : Bool)
      (hq : z ∈ Quad i σ τ) : z ∈ interior (Quad i σ τ) := by
    apply (mem_interior_iff_notMem_frontier hq).mpr
    intro hf
    exact hz (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion₂.mpr ⟨σ,τ,hf⟩⟩)
  have hOanchor (z : X) (hz : z ∈ Z) (i : Fin seeds.count) (hi : z ∈ A i) :
      O z ⊆ interior (A i) := by
    have hq : z ∈ interior (Quad i true true) := hZinterior z hz i true true hi
    have hh := hOsub z i (hselfN i z hi)
    rw [hchosenEq z hz i (hselfN i z hi) (true,true) hq] at hh
    exact hh
  have hPanchor (z : X) (hz : z ∈ Z) (i : Fin seeds.count) (hi : z ∈ A i) :
      P z ⊆ A i := closure_minimal ((hOanchor z hz i hi).trans interior_subset)
        (hAproper i).1.2.1.isClosed
  have hAexists (z : X) : ∃ i, z ∈ A i := by
    have hz : z ∈ ⋃ i, A i := by rw [hAcover]; trivial
    exact Set.mem_iUnion.mp hz
  have hprofile (z : X) (hz : z ∈ Z) :
      ∀ w ∈ O z, (∀ i, w ∈ A i ↔ z ∈ A i) ∧ N w = N z := by
    apply Topology.bowen_atom_membership_profile A (chosen z) z (hAexists z)
    · intro i hi
      rw [hchosenEq z hz i (hselfN i z hi) (true,true) (hZinterior z hz i true true hi)]
      exact interior_subset
    · intro i hi
      rw [Set.disjoint_left]
      intro w hw hwi
      obtain ⟨σ,τ,ha⟩ := Set.mem_iUnion₂.mp hw
      let a : Bool × Bool := (σ,τ)
      obtain ⟨hza,hwa⟩ := Set.mem_iUnion.mp ha
      change z ∈ interior (Quad i a.1 a.2) at hza
      change w ∈ interior (Quad i a.1 a.2) at hwa
      have hpw := hQint i a.1 a.2 w hwa
      have hAp := (hQdata i true true).2.2.2.2 w hwi
      have hσ : a.1 = true := by
        cases he : a.1 with
        | false => exact (Set.disjoint_left.mp (hUsep i) (by simpa only [he] using hpw.1) hAp.1).elim
        | true => rfl
      have hτ : a.2 = true := by
        cases he : a.2 with
        | false => exact (Set.disjoint_left.mp (hSsep i) (by simpa only [he] using hpw.2) hAp.2.1).elim
        | true => rfl
      apply hi
      have hz' := interior_subset hza
      simpa only [hσ,hτ,Quad,Cu,Ds,A,Bool.true_eq,ite_true] using hz'
  have hOeq (z w q : X) (hz : z ∈ Z) (hw : w ∈ Z)
      (hqz : q ∈ O z) (hqw : q ∈ O w) : O z = O w := by
    have hN : N z = N w := ((hprofile z hz q hqz).2).symm.trans (hprofile w hw q hqw).2
    have hchosen (i : Fin seeds.count) (hi : i ∈ N z) : chosen z i = chosen w i := by
      have hiw : i ∈ N w := hN ▸ hi
      obtain ⟨a,ha,_⟩ := hchoice z hz i hi
      obtain ⟨b,hb,_⟩ := hchoice w hw i hiw
      have hqa := hOsub z i hi hqz
      have hqb := hOsub w i hiw hqw
      rw [hchosenEq z hz i hi a ha] at hqa
      rw [hchosenEq w hw i hiw b hb] at hqb
      have he : a = b := by
        by_contra hn
        exact Set.disjoint_left.mp (hQdisjoint i hn) hqa hqb
      rw [hchosenEq z hz i hi a ha, hchosenEq w hw i hiw b hb, he]
    ext t
    simp only [O,Set.mem_iInter]
    constructor
    · intro ht i hi
      have hiz : i ∈ N z := hN.symm ▸ hi
      rw [← hchosen i hiz]
      exact ht i hiz
    · intro ht i hi
      rw [hchosen i hi]
      exact ht i (hN ▸ hi)
  have hPdisjoint (z : X) (hz : z ∈ Z) (w : X) (hw : w ∈ Z) (hne : P z ≠ P w) :
      Disjoint (interior (P z)) (interior (P w)) := by
    rw [hOregular z hz, hOregular w hw, Set.disjoint_left]
    intro q hqz hqw
    exact hne (congrArg closure (hOeq z w q hz hw hqz hqw))
  have hObracket (z : X) (hz : z ∈ Z) :
      ∀ x ∈ O z, ∀ y ∈ O z, bracket x y ∈ O z := by
    intro x hx y hy
    apply Set.mem_iInter₂.mpr
    intro i hi
    obtain ⟨a,ha,_⟩ := hchoice z hz i hi
    have hx' := hOsub z i hi hx
    have hy' := hOsub z i hi hy
    rw [hchosenEq z hz i hi a ha] at hx' hy' ⊢
    exact hQintBracket i a.1 a.2 x hx' y hy'
  have hPmesh (z : X) (hz : z ∈ Z) : Metric.diam (P z) < α 4 := by
    obtain ⟨i,hi⟩ := hAexists z
    exact (Metric.diam_mono (hPanchor z hz i hi) (hAproper i).1.2.1.isBounded).trans_lt
      (hAproper i).2
  have hPproper (z : X) (hz : z ∈ Z) : proper (P z) := by
    refine ⟨⟨z,subset_closure (hOneigh z hz).2⟩,isClosed_closure.isCompact,?_,
      (hPmesh z hz).le.trans (hαdescending 3).le,?_⟩
    · have hc : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
          (closure (O z ×ˢ O z)) := by
        apply (hcharts.1 (α 3 / 3) (by linarith only [hαpos 3]) (by linarith only [hα3γ])).mono
        rw [closure_prod_eq]
        intro p hp
        have hd := Metric.dist_le_diam_of_mem (isClosed_closure.isCompact.isBounded :
          Bornology.IsBounded (P z)) hp.1 hp.2
        have hs : 3 * α 4 < εmod (α 3 / 3) := (hscale 3).2
        change dist p.1 p.2 ≤ εmod (α 3 / 3)
        linarith only [hd,hs,hPmesh z hz,hαpos 4]
      have hm : Set.MapsTo (fun p : X × X ↦ bracket p.1 p.2) (O z ×ˢ O z) (O z) :=
        fun p hp ↦ hObracket z hz p.1 hp.1 p.2 hp.2
      have hmc := hm.closure_of_continuousWithinAt (fun p hp ↦ (hc p hp).mono subset_closure)
      intro x hx y hy
      exact hmc (by rw [closure_prod_eq]; exact ⟨hx,hy⟩ : (x,y) ∈ closure (O z ×ˢ O z))
    · rw [hOregular z hz]
  have hsepDiag (p q : X) (hs : p ∈ Ws γ q) (hu : p ∈ Wu γ q) : p = q :=
    ((hunique q q (by simpa using hε.le)).2 p ⟨hs,hu⟩).trans (hdiag q)
  have hshrinkU (p q : X) (hp : p ∈ Wu γ q) : p ∈ Wu (dist p q) q := by
    intro n
    exact (hcontract_u q p q n hp (fun n ↦ by simpa using hγ.le)).trans
      (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le))
  have hshrinkS (p q : X) (hp : p ∈ Ws γ q) : p ∈ Ws (dist p q) q := by
    intro n
    exact (hcontract_s q p q n hp (fun n ↦ by simpa using hγ.le)).trans
      (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le))
  have hsmall32 : α 3 < α 2 := hαdescending 2
  have hsmall43 : 3 * α 4 < α 3 / 3 := (hscale 3).1
  have hα1γ : α 1 ≤ γ := (hmono (Fin.zero_le _)).trans_eq hα0
  have hα12 : 3 * α 2 < α 1 / 3 := (hscale 1).1
  have hα23 : 3 * α 3 < α 2 / 3 := (hscale 2).1
  have hmod2 := (hmodulus (α 2 / 3) (by linarith only [hαpos 2]) (by linarith only [hα2γ,hαpos 2])).2
  have hmod1 := (hmodulus (α 1 / 3) (by linarith only [hαpos 1]) (by linarith only [hα1γ,hαpos 1])).2
  have heps2 : 3 * α 3 < εmod (α 2 / 3) := (hscale 2).2
  have heps1 : 3 * α 2 < εmod (α 1 / 3) := (hscale 1).2
  have hprojSliceU (x c q : X) (hc : c ∈ Wu (2 * α 3 / 3) x)
      (hq : dist q x < 3 * α 4) : bracket (bracket c q) x = c := by
    have hdist : dist c q ≤ εmod (α 2 / 3) := by
      have hc0 : dist c x ≤ 2 * α 3 / 3 := hc 0
      have ht := dist_triangle c x q
      rw [dist_comm x q] at ht
      linarith only [hc0, ht, hq, heps2, hsmall43, hαpos 3]
    have hb := hmod2 c q hdist
    have hb0 : dist (bracket c q) c ≤ α 2 / 3 := hb.1 0
    have hc0 : dist c x ≤ 2 * α 3 / 3 := hc 0
    have hd : dist (bracket c q) x ≤ εmod (α 1 / 3) := by
      have ht := dist_triangle (bracket c q) c x
      linarith only [ht, hb0, hc0, hα23, heps1, hαpos 2]
    have ho := hmod1 (bracket c q) x hd
    apply hsepDiag
    · intro n
      exact (dist_triangle _ ((f : X → X)^[n] (bracket c q)) _).trans
        ((add_le_add (ho.1 n) (hb.1 n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
    · intro n
      exact (dist_triangle _ ((f.symm : X → X)^[n] x) _).trans
        ((add_le_add (ho.2 n) (by simpa only [dist_comm] using hc n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
  have hsameStable (x p q : X) (hp : dist p x < 3 * α 4)
      (hq : dist q x < 3 * α 4) (hpq : p ∈ Wu γ q) (hd : dist p q ≤ α 3) :
      bracket x p = bracket x q := by
    have hbp := hmod2 x p (by rw [dist_comm]; linarith only [hp, heps2, hsmall43, hαpos 3])
    have hbq := hmod2 x q (by rw [dist_comm]; linarith only [hq, heps2, hsmall43, hαpos 3])
    apply hsepDiag
    · intro n
      exact (dist_triangle _ ((f : X → X)^[n] x) _).trans
        ((add_le_add (hbp.1 n) (by simpa only [dist_comm] using hbq.1 n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
    · intro n
      have h1 := dist_triangle ((f.symm : X → X)^[n] (bracket x p))
        ((f.symm : X → X)^[n] p) ((f.symm : X → X)^[n] (bracket x q))
      have h2 := dist_triangle ((f.symm : X → X)^[n] p)
        ((f.symm : X → X)^[n] q) ((f.symm : X → X)^[n] (bracket x q))
      rw [dist_comm ((f.symm : X → X)^[n] q) _] at h2
      linarith only [h1,h2,hbp.2 n,hbq.2 n,(hshrinkU p q hpq n).trans hd,hα1γ,hα12,hα23,hγ,hαpos 1,hαpos 2,hαpos 3]
  have hreconstructU (x p q : X) (hp : dist p x < 3 * α 4)
      (hq : dist q x < 3 * α 4) (hpq : p ∈ Wu γ q) (hd : dist p q ≤ α 3) :
      bracket (bracket p x) q = p := by
    have hbp := hmod2 p x (by linarith only [hp,heps2,hsmall43,hαpos 3])
    have hp0 : dist (bracket p x) p ≤ α 2 / 3 := hbp.1 0
    have hdist : dist (bracket p x) q ≤ εmod (α 1 / 3) := by
      have ht := dist_triangle (bracket p x) p q
      linarith only [ht,hp0,hd,hα23,heps1,hαpos 2]
    have ho := hmod1 (bracket p x) q hdist
    apply hsepDiag
    · intro n
      exact (dist_triangle _ ((f : X → X)^[n] (bracket p x)) _).trans
        ((add_le_add (ho.1 n) (hbp.1 n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
    · intro n
      exact (dist_triangle _ ((f.symm : X → X)^[n] q) _).trans
        ((add_le_add (ho.2 n)
          (by simpa only [dist_comm] using (hshrinkU p q hpq n).trans hd)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
  have hfixSmallU (p q : X) (hpq : p ∈ Wu γ q) (hd : dist p q < α 4) :
      bracket p q = p := by
    have hb := hmod2 p q (by linarith only [hd,hsmall43,heps2,hαpos 3])
    apply hsepDiag
    · exact fun n ↦ (hb.1 n).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4])
    · intro n
      exact (dist_triangle _ ((f.symm : X → X)^[n] q) _).trans
        ((add_le_add (hb.2 n)
          (by simpa only [dist_comm] using hshrinkU p q hpq n)).trans (by linarith only [hd,hsmall43,hα23,hα12,hα1γ,hγ,hαpos 1,hαpos 2,hαpos 3]))
  have hsliceUreg (z : X) (hz : z ∈ Z) :
      P z ∩ Wu γ z = closure (O z ∩ Wu γ z) := by
    apply Set.Subset.antisymm
    · intro p hp
      have hzd : z ∈ P z := subset_closure (hOneigh z hz).2
      have hdist (q : X) (hq : q ∈ P z) : dist q z < α 4 :=
        (Metric.dist_le_diam_of_mem (hPproper z hz).2.1.isBounded hq hzd).trans_lt (hPmesh z hz)
      have hc : ContinuousOn (fun q ↦ bracket q z) (P z) :=
        (hcharts.1 (α 3 / 3) (by linarith only [hαpos 3]) (by linarith only [hα3γ])).comp
          (continuous_id.prodMk continuous_const).continuousOn
          (fun q hq ↦ by
            change dist q z ≤ εmod (α 3 / 3)
            have he : 3 * α 4 < εmod (α 3 / 3) := (hscale 3).2
            linarith only [hdist q hq,hαpos 4,he])
      have hm : Set.MapsTo (fun q ↦ bracket q z) (O z) (O z ∩ Wu γ z) := by
        intro q hq
        refine ⟨hObracket z hz q hq z (hOneigh z hz).2, ?_⟩
        have hb := hmod2 q z (by linarith only [hdist q (subset_closure hq),hαpos 3,hsmall43,heps2])
        exact fun n ↦ (hb.2 n).trans (by linarith only [hα2γ,hαpos 2])
      have he := hm.closure_of_continuousWithinAt (fun q hq ↦ (hc q hq).mono subset_closure) hp.1
      simpa only [hfixSmallU p z hp.2 (hdist p hp.1)] using he
    · exact closure_minimal (Set.inter_subset_inter_left _ subset_closure)
        (isClosed_closure.inter (hclosedWu γ z))
  have hriSliceU (i : Fin seeds.count) (z q : X)
      (hz : dist z (seeds.center i) < 3 * α 4)
      (hq : q ∈ plaqueInterior (Wu γ z) (product (C i) {z})) :
      bracket q (seeds.center i) ∈ plaqueInterior (Wu γ (seeds.center i)) (C i) := by
    obtain ⟨c,hc,d,hd,hcd⟩ := hriSub _ _ hq
    have he : d = z := hd
    subst d
    subst q
    have hcSmall : c ∈ Wu (2 * α 3 / 3) (seeds.center i) :=
      (hCuData i true).2.2 hc
    rw [hprojSliceU (seeds.center i) c z hcSmall hz]
    obtain ⟨U,hUγ,hUo,hUin,hUout⟩ := bowen_orbit_plaque_open_collar
      (f.symm : X → X) hlam.le hlam1.le (by linarith only [hαpos 3] : 0 ≤ 2 * α 3 / 3)
      (by linarith only [hαpos 3,hα23] : 2 * α 3 / 3 < α 2) hα2γ.le hcontract_u (seeds.center i)
    have hCU : C i ⊆ U := (hCuData i true).2.2.trans hUin
    have hrb := (Bowen.bowen_fact1_plaque_rebase_g6 f lam γ ε hlam hlam1 hγ hε
      αshort εmod (fun δ hδ hδγ ↦ (hmodulus δ hδ hδγ).1)
      hα0 (fun j ↦ hαpos _) (fun j ↦ hαscale ⟨j.val,by omega⟩)
      (fun j ↦ hαmap ⟨j.val,by omega⟩) bracket hcontract_s hcontract_u
      (fun x y hxy ↦ ⟨bracket x y,(hunique x y hxy).1,(hunique x y hxy).2⟩)
      (fun x y hxy ↦ (hunique x y hxy).1) hcontinuous
      (fun δ hδ hδγ ↦ (hmodulus δ hδ hδγ).2)
      (seeds.center i) z (by
        change dist (seeds.center i) z ≤ α 3
        rw [dist_comm]
        linarith only [hz,hsmall43,hαpos 3])).1
      U hUout hUo
    change ((fun u ↦ bracket u z) '' U ⊆ Wu γ z) ∧
      IsOpen ((Subtype.val : Wu γ z → X) ⁻¹' ((fun u ↦ bracket u z) '' U)) ∧
      ∃ chart : {u : Wu γ (seeds.center i) // (u : X) ∈ U} ≃ₜ
        {w : Wu γ z // (w : X) ∈ (fun u ↦ bracket u z) '' U},
        (∀ u, (chart u).val.val = bracket u.val.val z) ∧
        (∀ w, (chart.symm w).val.val = bracket w.val.val (seeds.center i)) at hrb
    obtain ⟨himg,hopen,chart,hchart,_⟩ := hrb
    have himage : (fun u ↦ bracket u z) '' C i = product (C i) {z} := by
      ext v
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact ⟨u,hu,z,rfl,rfl⟩
      · rintro ⟨u,hu,d,hd,he⟩
        have hdz : d = z := hd
        subst d
        exact ⟨u,hu,he⟩
    have hh := BowenRegularClosedPreparation.rebase_interior
      (Wu γ (seeds.center i)) (Wu γ z) U (C i) (fun u ↦ bracket u z)
      hUγ hCU himg hUo hopen chart hchart c hc
    apply hh.mp
    change bracket c z ∈ plaqueInterior (Wu γ z) ((fun u ↦ bracket u z) '' C i)
    rwa [himage]
  have hUtarget (z : X) (hz : z ∈ Z) (i : Fin seeds.count) (hi : i ∈ N z)
      (hpos : bracket z (seeds.center i) ∈ C i) :
      ∀ v ∈ O z ∩ Wu γ z, v ∈ plaqueInterior (Wu γ z) (product (C i) {z}) := by
    obtain ⟨a,ha,_⟩ := hchoice z hz i hi
    have hσ : a.1 = true := by
      cases he : a.1 with
      | false => exact (Set.disjoint_left.mp (hUsep i)
          (by simpa only [he] using (hQint i a.1 a.2 z ha).1) hpos).elim
      | true => rfl
    have hsub : O z ∩ Wu γ z ⊆ product (C i) {z} := by
      intro v hv
      have hvi := hOsub z i hi hv.1
      rw [hchosenEq z hz i hi a ha] at hvi
      have hcv := (hQint i a.1 a.2 v hvi).1
      have hc : bracket v (seeds.center i) ∈ C i := by
        have hh := hriSub _ _ hcv
        simpa only [hσ,Cu,Bool.true_eq,ite_true] using hh
      have hiv : i ∈ N v := (hprofile z hz v hv.1).2.symm ▸ hi
      have hvz : dist v z ≤ α 3 :=
        ((Metric.dist_le_diam_of_mem (hPproper z hz).2.1.isBounded
          (subset_closure hv.1) (subset_closure (hOneigh z hz).2)).trans_lt
            (hPmesh z hz)).le.trans (hαdescending 3).le
      exact ⟨_,hc,z,rfl,hreconstructU (seeds.center i) v z
        ((hVdist i v hiv).trans (by linarith only [hαpos 4]))
        ((hVdist i z hi).trans (by linarith only [hαpos 4])) hv.2 hvz⟩
    intro v hv
    refine ⟨⟨v,hv.2⟩,?_,rfl⟩
    apply interior_mono (show (Subtype.val : Wu γ z → X) ⁻¹' O z ⊆
      Subtype.val ⁻¹' product (C i) {z} from fun q hq ↦ hsub ⟨hq,q.property⟩)
    rw [((hOneigh z hz).1.preimage continuous_subtype_val).interior_eq]
    exact hv.1
  have hnegUInt (i : Fin seeds.count) (c : X) (he : c ∈ Eu i) (hc : c ∉ C i) :
      c ∈ plaqueInterior (Wu γ (seeds.center i)) (Cu i false) := by
    refine ⟨⟨c,hEuγ i he⟩,?_,rfl⟩
    change (⟨c,hEuγ i he⟩ : Wu γ (seeds.center i)) ∈ interior
      ((Subtype.val : Wu γ (seeds.center i) → X) ⁻¹'
        plaqueClosure (Wu γ (seeds.center i)) (Eu i \ C i))
    simp only [plaqueClosure,Set.preimage_image_eq _ Subtype.val_injective]
    exact ((hEuo i).sdiff ((hCdata i).1.isClosed.preimage continuous_subtype_val)).subset_interior_closure
      ⟨he,hc⟩
  have hrestoreU (i : Fin seeds.count) (a : Bool × Bool) (z q : X)
      (hz : z ∈ interior (Quad i a.1 a.2))
      (hzd : dist z (seeds.center i) < 3 * α 4)
      (hqd : dist q (seeds.center i) < 3 * α 4)
      (hqz : q ∈ Wu γ z) (hd : dist q z ≤ α 3)
      (hu : bracket q (seeds.center i) ∈ plaqueInterior (Wu γ (seeds.center i)) (Cu i a.1)) :
      q ∈ interior (Quad i a.1 a.2) := by
    rw [(hQdata i a.1 a.2).2.2.1]
    have hs : bracket (seeds.center i) q ∈
        plaqueInterior (Ws γ (seeds.center i)) (Ds i a.2) := by
      rw [hsameStable (seeds.center i) q z hqd hzd hqz hd]
      exact (hQint i a.1 a.2 z hz).2
    exact ⟨_,hu,_,hs,(hsmallProj (seeds.center i) q hqd).2.2⟩
  have hUslicePos (i : Fin seeds.count) (z : X)
      (hz : dist z (seeds.center i) < 3 * α 4) (hs : z ∈ product (C i) {z}) :
      bracket z (seeds.center i) ∈ C i := by
    obtain ⟨c,hc,d,hd,he⟩ := hs
    have hdz : d = z := hd
    subst d
    have hp := hprojSliceU (seeds.center i) c z ((hCuData i true).2.2 hc) hz
    rw [he] at hp
    rw [hp]
    exact hc
  have hUint (z : X) (hz : z ∈ Z) (hhz : h z ∈ Z) :
      h ⁻¹' (O (h z) ∩ Wu γ (h z)) ⊆ O z ∩ Wu γ z := by
    intro q hv
    have hvO : h q ∈ O (h z) := hv.1
    have hvU : h q ∈ Wu γ (h z) := hv.2
    have hqz : q ∈ Wu γ z := by
      intro n
      have hh := hshift f.symm γ (h z) (h q)
        (by simpa only [BowenRegularClosedPreparation.pow_apply_iterate,Wu,Set.mem_ofPred_eq] using hvU) n
      simpa only [hpowInv,h.symm_apply_apply,BowenRegularClosedPreparation.pow_apply_iterate] using hh
    have hvd : dist (h q) (h z) < α 4 :=
      (Metric.dist_le_diam_of_mem (hPproper (h z) hhz).2.1.isBounded
        (subset_closure hvO) (subset_closure (hOneigh (h z) hhz).2)).trans_lt (hPmesh (h z) hhz)
    have hqd : dist q z < α 4 := by
      have hh := hcontract_u (h z) (h q) (h z) m hvU (fun n ↦ by simpa using hγ.le)
      simp only [← BowenRegularClosedPreparation.pow_apply_iterate,hpowInv,h.symm_apply_apply] at hh
      exact (hh.trans (mul_le_of_le_one_left dist_nonneg hβ1.le)).trans_lt hvd
    refine ⟨?_,hqz⟩
    apply Set.mem_iInter₂.mpr
    intro i hi
    obtain ⟨a,ha,_⟩ := hchoice z hz i hi
    rw [hchosenEq z hz i hi a ha]
    have hzi : dist z (seeds.center i) < 3 * α 4 :=
      (hVdist i z hi).trans (by linarith only [hαpos 4])
    have hqi : dist q (seeds.center i) < 3 * α 4 := by
      have ht := dist_triangle q z (seeds.center i)
      linarith only [ht,hqd,hVdist i z hi]
    apply hrestoreU i a z q ha hzi hqi hqz (hqd.le.trans (hαdescending 3).le)
    cases hs : a.1 with
    | true =>
      have hsource : bracket z (seeds.center i) ∈ C i := by
        have hh := hriSub _ _ (hQint i a.1 a.2 z ha).1
        simpa only [hs,Cu,Bool.true_eq,ite_true] using hh
      obtain ⟨j,hj,hjmem,hjsub,hjint⟩ := hcollar i z hzi hsource
      have hjd : dist (h z) (seeds.center j) < 3 * α 4 :=
        (hVdist j (h z) hj).trans (by linarith only [hαpos 4])
      have htarget := hUtarget (h z) hhz j hj (hUslicePos j (h z) hjd hjmem)
        (h q) ⟨hvO,hvU⟩
      have hsourceInt : q ∈ plaqueInterior (Wu γ z) (product (C i) {z}) :=
        hjint ⟨h q,htarget,h.symm_apply_apply q⟩
      have hh := hriSliceU i z q hzi hsourceInt
      simpa only [hs,Cu,Bool.true_eq,ite_true] using hh
    | false =>
      have hqe : bracket q (seeds.center i) ∈ Eu i :=
        hEuinner i (hsmallProj (seeds.center i) q hqi).1
      have hnot : bracket q (seeds.center i) ∉ C i := by
        intro hbad
        obtain ⟨j,hj,hjmem,hjsub,_⟩ := hcollar i q hqi hbad
        have hj' : j ∈ N (h z) := (hprofile (h z) hhz (h q) hvO).2 ▸ hj
        have hvj : dist (h q) (seeds.center j) < 3 * α 4 :=
          (hVdist j (h q) hj).trans (by linarith only [hαpos 4])
        have hzj : dist (h z) (seeds.center j) < 3 * α 4 :=
          (hVdist j (h z) hj').trans (by linarith only [hαpos 4])
        have hvpos := hUslicePos j (h q) hvj hjmem
        obtain ⟨b,hb,_⟩ := hchoice (h z) hhz j hj'
        have hvb := hOsub (h z) j hj' hvO
        rw [hchosenEq (h z) hhz j hj' b hb] at hvb
        have hbtrue : b.1 = true := by
          cases hb1 : b.1 with
          | false => exact (Set.disjoint_left.mp (hUsep j)
              (by simpa only [hb1] using (hQint j b.1 b.2 (h q) hvb).1) hvpos).elim
          | true => rfl
        have hzpos : bracket (h z) (seeds.center j) ∈ C j := by
          have hh := hriSub _ _ (hQint j b.1 b.2 (h z) hb).1
          simpa only [hbtrue,Cu,Bool.true_eq,ite_true] using hh
        have hreverse : h z ∈ Wu γ (h q) := fun n ↦ by simpa only [dist_comm] using hvU n
        have hzslice : h z ∈ product (C j) {h q} :=
          ⟨_,hzpos,h q,rfl,hreconstructU (seeds.center j) (h z) (h q) hzj hvj hreverse
            (by rw [dist_comm]; exact hvd.le.trans (hαdescending 3).le)⟩
        obtain ⟨w,hw,he⟩ := hjsub hzslice
        have hwz : w = z := h.injective he
        subst w
        obtain ⟨c,hc,d,hd,he⟩ := hw
        have hdq : d = q := hd
        subst d
        have hproj := hprojSliceU (seeds.center i) c q ((hCuData i true).2.2 hc) hqi
        rw [he] at hproj
        have hzpos : bracket z (seeds.center i) ∈ C i := by rw [hproj]; exact hc
        exact Set.disjoint_left.mp (hUsep i)
          (by simpa only [hs] using (hQint i a.1 a.2 z ha).1) hzpos
      have hh := hnegUInt i _ hqe hnot
      simpa only [hs] using hh
  -- Drop construction interfaces after their last use.
  try clear hr
  try clear hrR
  try clear hRγ
  try clear stableCollar
  try clear unstableCollar
  try clear hα4γ
  try clear hcoreScale
  try clear hcoreCompact
  try clear hcoreContinuous
  try clear hη
  try clear hδ7
  try clear hβ5
  try clear hδ5
  try clear hδρ
  try clear h45γ
  try clear hsmall
  try clear hdiag
  try clear hfix_s
  try clear hfix_u
  try clear hseed_u
  try clear hseed_s
  try clear hasat
  try clear hasmall
  try clear hmono
  try clear hWs
  try clear hWu
  try clear hCγ
  try clear hDγ
  try clear hrelative
  try clear hβ0
  try clear hsum
  try clear h3γ
  try clear hseedSmall
  try clear hCstageSlice
  try clear hDstageSlice
  try clear hpowInv
  try clear hclosedWu
  try clear hrelativeReg
  try clear hfactorSmall
  try clear hnegative
  try clear hCuData
  try clear hprodMono
  try clear hproductData
  try clear hUsep
  try clear hUintSep
  try clear hSintSep
  try clear hQdisjoint
  try clear hA0sub
  try clear hcollar
  try clear hQcover
  try clear hcross
  try clear hQintBracket
  try clear hfinite
  try clear hselfN
  try clear hZinterior
  try clear hOanchor
  try clear hPanchor
  try clear hAexists
  try clear hOeq
  try clear hshrinkU
  try clear hsmall32
  try clear hmod2
  try clear hmod1
  try clear hprojSliceU
  try clear hsameStable
  try clear hreconstructU
  try clear hfixSmallU
  try clear hriSliceU
  try clear hUtarget
  try clear hnegUInt
  try clear hrestoreU
  try clear hUslicePos
  let fD := f.symm
  let hDmap := h.symm
  let bracketD : X → X → X := fun x y ↦ bracket y x
  let productD : Set X → Set X → Set X := fun B E ↦
    {z | ∃ b ∈ B, ∃ e ∈ E, bracketD b e = z}
  have hflipProduct (B E : Set X) : productD B E = product E B := by
    ext z
    constructor <;> rintro ⟨b,hb,e,he,hbe⟩ <;> exact ⟨e,he,b,hb,hbe⟩
  let QuadD := fun i σ τ ↦ Quad i τ σ
  have hQintD (i : Fin seeds.count) (σ τ : Bool) (z : X)
      (hz : z ∈ interior (QuadD i σ τ)) :
      bracketD z (seeds.center i) ∈ plaqueInterior (Ws γ (seeds.center i)) (Ds i σ) ∧
      bracketD (seeds.center i) z ∈ plaqueInterior (Wu γ (seeds.center i)) (Cu i τ) :=
    (hQint i τ σ z hz).symm
  have hQintEqD (i : Fin seeds.count) (σ τ : Bool) :
      interior (QuadD i σ τ) = productD (plaqueInterior (Ws γ (seeds.center i)) (Ds i σ))
        (plaqueInterior (Wu γ (seeds.center i)) (Cu i τ)) := by
    rw [hflipProduct]
    exact (hQdata i τ σ).2.2.1
  have hsepDiagD (p q : X) (hs : p ∈ Wu γ q) (hu : p ∈ Ws γ q) : p = q :=
    hsepDiag p q hu hs
  have hcontract_sD : ∀ (x y z : X) (n : ℕ), y ∈ Wu γ x → z ∈ Wu γ x →
      dist ((fD : X → X)^[n] y) ((fD : X → X)^[n] z) ≤ lam ^ n * dist y z := hcontract_u
  have hcontract_uD : ∀ (x y z : X) (n : ℕ), y ∈ Ws γ x → z ∈ Ws γ x →
      dist ((fD.symm : X → X)^[n] y) ((fD.symm : X → X)^[n] z) ≤ lam ^ n * dist y z := hcontract_s
  have huniqueD : ∀ x y : X, dist x y ≤ ε →
      bracketD x y ∈ Wu γ x ∩ Ws γ y ∧
      ∀ z ∈ Wu γ x ∩ Ws γ y, z = bracketD x y := by
    intro x y hxy
    have hh := hunique y x (by simpa only [dist_comm] using hxy)
    exact ⟨hh.1.symm,fun z hz ↦ hh.2 z hz.symm⟩
  have hmodulusD : ∀ δ : ℝ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y : X, dist x y ≤ εmod δ → bracketD x y ∈ Wu δ x ∩ Ws δ y := by
    intro δ hδ hδγ
    refine ⟨(hmodulus δ hδ hδγ).1,?_⟩
    intro x y hxy
    exact ((hmodulus δ hδ hδγ).2 y x (by simpa only [dist_comm] using hxy)).symm
  have hcontinuousD : ContinuousOn (fun p : X × X ↦ bracketD p.1 p.2)
      {p | dist p.1 p.2 ≤ ε} := by
    exact hcontinuous.comp continuous_swap.continuousOn (fun p hp ↦ by
      change dist p.1 p.2 ≤ _ at hp
      change dist p.2 p.1 ≤ _
      simpa only [dist_comm] using hp)
  have hchartsD : ∀ δ, 0 < δ → δ ≤ γ / 3 →
      ContinuousOn (fun p : X × X ↦ bracketD p.1 p.2) {p | dist p.1 p.2 ≤ εmod δ} := by
    intro δ hδ hδγ
    exact (hcharts.1 δ hδ hδγ).comp continuous_swap.continuousOn
      (fun p hp ↦ by
      change dist p.1 p.2 ≤ _ at hp
      change dist p.2 p.1 ≤ _
      simpa only [dist_comm] using hp)
  have hαmapD : ∀ i : Fin 7, ∀ x y : X, dist x y ≤ α i.succ →
      dist (fD x) (fD y) < α i.castSucc ∧ dist (fD.symm x) (fD.symm y) < α i.castSucc :=
    fun i x y hxy ↦ (hαmap i x y hxy).symm
  have hmod2D := (hmodulusD (α 2 / 3) (by linarith only [hαpos 2]) (by linarith only [hα2γ,hαpos 2])).2
  have hmod1D := (hmodulusD (α 1 / 3) (by linarith only [hαpos 1]) (by linarith only [hα1γ,hαpos 1])).2
  have hObracketD (z : X) (hz : z ∈ Z) :
      ∀ x ∈ O z, ∀ y ∈ O z, bracketD x y ∈ O z :=
    fun x hx y hy ↦ hObracket z hz y hy x hx
  have hsmallProjD (x q : X) (hq : dist q x < 3 * α 4) :
      bracketD q x ∈ Ws (α 3 / 3) x ∧ bracketD x q ∈ Wu (α 3 / 3) x ∧
      bracketD (bracketD q x) (bracketD x q) = q :=
    ⟨(hsmallProj x q hq).2.1,(hsmallProj x q hq).1,(hsmallProj x q hq).2.2⟩
  have hpowInvD : fD.symm ^ m = hDmap.symm := by
    simp only [fD,hDmap,Homeomorph.symm_symm]
    rfl
  have hprojSliceS (x c q : X) (hc : c ∈ Ws (2 * α 3 / 3) x)
      (hq : dist q x < 3 * α 4) : bracketD (bracketD c q) x = c := by
    have hdist : dist c q ≤ εmod (α 2 / 3) := by
      have hc0 : dist c x ≤ 2 * α 3 / 3 := hc 0
      have ht := dist_triangle c x q
      rw [dist_comm x q] at ht
      linarith only [hc0, ht, hq, heps2, hsmall43, hαpos 3]
    have hb := hmod2D c q hdist
    have hb0 : dist (bracketD c q) c ≤ α 2 / 3 := hb.1 0
    have hc0 : dist c x ≤ 2 * α 3 / 3 := hc 0
    have hd : dist (bracketD c q) x ≤ εmod (α 1 / 3) := by
      have ht := dist_triangle (bracketD c q) c x
      linarith only [ht, hb0, hc0, hα23, heps1, hαpos 2]
    have ho := hmod1D (bracketD c q) x hd
    apply hsepDiagD
    · intro n
      exact (dist_triangle _ ((f.symm : X → X)^[n] (bracketD c q)) _).trans
        ((add_le_add (ho.1 n) (hb.1 n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
    · intro n
      exact (dist_triangle _ ((f : X → X)^[n] x) _).trans
        ((add_le_add (ho.2 n) (by simpa only [dist_comm] using hc n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
  have hsameUnstable (x p q : X) (hp : dist p x < 3 * α 4)
      (hq : dist q x < 3 * α 4) (hpq : p ∈ Ws γ q) (hd : dist p q ≤ α 3) :
      bracketD x p = bracketD x q := by
    have hbp := hmod2D x p (by rw [dist_comm]; linarith only [hp, heps2, hsmall43, hαpos 3])
    have hbq := hmod2D x q (by rw [dist_comm]; linarith only [hq, heps2, hsmall43, hαpos 3])
    apply hsepDiagD
    · intro n
      exact (dist_triangle _ ((f.symm : X → X)^[n] x) _).trans
        ((add_le_add (hbp.1 n) (by simpa only [dist_comm] using hbq.1 n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
    · intro n
      have h1 := dist_triangle ((f : X → X)^[n] (bracketD x p))
        ((f : X → X)^[n] p) ((f : X → X)^[n] (bracketD x q))
      have h2 := dist_triangle ((f : X → X)^[n] p)
        ((f : X → X)^[n] q) ((f : X → X)^[n] (bracketD x q))
      rw [dist_comm ((f : X → X)^[n] q) _] at h2
      linarith only [h1,h2,hbp.2 n,hbq.2 n,(hshrinkS p q hpq n).trans hd,hα1γ,hα12,hα23,hγ,hαpos 1,hαpos 2,hαpos 3]
  have hreconstructS (x p q : X) (hp : dist p x < 3 * α 4)
      (hq : dist q x < 3 * α 4) (hpq : p ∈ Ws γ q) (hd : dist p q ≤ α 3) :
      bracketD (bracketD p x) q = p := by
    have hbp := hmod2D p x (by linarith only [hp,heps2,hsmall43,hαpos 3])
    have hp0 : dist (bracketD p x) p ≤ α 2 / 3 := hbp.1 0
    have hdist : dist (bracketD p x) q ≤ εmod (α 1 / 3) := by
      have ht := dist_triangle (bracketD p x) p q
      linarith only [ht,hp0,hd,hα23,heps1,hαpos 2]
    have ho := hmod1D (bracketD p x) q hdist
    apply hsepDiagD
    · intro n
      exact (dist_triangle _ ((f.symm : X → X)^[n] (bracketD p x)) _).trans
        ((add_le_add (ho.1 n) (hbp.1 n)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
    · intro n
      exact (dist_triangle _ ((f : X → X)^[n] q) _).trans
        ((add_le_add (ho.2 n)
          (by simpa only [dist_comm] using (hshrinkS p q hpq n).trans hd)).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4]))
  have hfixSmallS (p q : X) (hpq : p ∈ Ws γ q) (hd : dist p q < α 4) :
      bracketD p q = p := by
    have hb := hmod2D p q (by linarith only [hd,hsmall43,heps2,hαpos 3])
    apply hsepDiagD
    · exact fun n ↦ (hb.1 n).trans (by linarith only [hα1γ, hα12, hα23, hsmall43, hαpos 1, hαpos 2, hαpos 3, hαpos 4])
    · intro n
      exact (dist_triangle _ ((f : X → X)^[n] q) _).trans
        ((add_le_add (hb.2 n)
          (by simpa only [dist_comm] using hshrinkS p q hpq n)).trans (by linarith only [hd,hsmall43,hα23,hα12,hα1γ,hγ,hαpos 1,hαpos 2,hαpos 3]))
  have hsliceSreg (z : X) (hz : z ∈ Z) :
      P z ∩ Ws γ z = closure (O z ∩ Ws γ z) := by
    apply Set.Subset.antisymm
    · intro p hp
      have hzd : z ∈ P z := subset_closure (hOneigh z hz).2
      have hdist (q : X) (hq : q ∈ P z) : dist q z < α 4 :=
        (Metric.dist_le_diam_of_mem (hPproper z hz).2.1.isBounded hq hzd).trans_lt (hPmesh z hz)
      have hc : ContinuousOn (fun q ↦ bracketD q z) (P z) :=
        (hchartsD (α 3 / 3) (by linarith only [hαpos 3]) (by linarith only [hα3γ])).comp
          (continuous_id.prodMk continuous_const).continuousOn
          (fun q hq ↦ by
            change dist q z ≤ εmod (α 3 / 3)
            have he : 3 * α 4 < εmod (α 3 / 3) := (hscale 3).2
            linarith only [hdist q hq,hαpos 4,he])
      have hm : Set.MapsTo (fun q ↦ bracketD q z) (O z) (O z ∩ Ws γ z) := by
        intro q hq
        refine ⟨hObracketD z hz q hq z (hOneigh z hz).2, ?_⟩
        have hb := hmod2D q z (by linarith only [hdist q (subset_closure hq),hαpos 3,hsmall43,heps2])
        exact fun n ↦ (hb.2 n).trans (by linarith only [hα2γ,hαpos 2])
      have he := hm.closure_of_continuousWithinAt (fun q hq ↦ (hc q hq).mono subset_closure) hp.1
      simpa only [hfixSmallS p z hp.2 (hdist p hp.1)] using he
    · exact closure_minimal (Set.inter_subset_inter_left _ subset_closure)
        (isClosed_closure.inter (hclosedWs γ z))
  have hriSliceS (i : Fin seeds.count) (z q : X)
      (hz : dist z (seeds.center i) < 3 * α 4)
      (hq : q ∈ plaqueInterior (Ws γ z) (productD (D i) {z})) :
      bracketD q (seeds.center i) ∈ plaqueInterior (Ws γ (seeds.center i)) (D i) := by
    obtain ⟨c,hc,d,hd,hcd⟩ := hriSub _ _ hq
    have he : d = z := hd
    subst d
    subst q
    have hcSmall : c ∈ Ws (2 * α 3 / 3) (seeds.center i) :=
      (hDsData i true).2.2 hc
    rw [hprojSliceS (seeds.center i) c z hcSmall hz]
    obtain ⟨U,hUγ,hUo,hUin,hUout⟩ := bowen_orbit_plaque_open_collar
      (f : X → X) hlam.le hlam1.le (by linarith only [hαpos 3] : 0 ≤ 2 * α 3 / 3)
      (by linarith only [hαpos 3,hα23] : 2 * α 3 / 3 < α 2) hα2γ.le hcontract_uD (seeds.center i)
    have hCU : D i ⊆ U := (hDsData i true).2.2.trans hUin
    have hrb := (Bowen.bowen_fact1_plaque_rebase_g6 fD lam γ ε hlam hlam1 hγ hε
      αshort εmod (fun δ hδ hδγ ↦ (hmodulusD δ hδ hδγ).1)
      hα0 (fun j ↦ hαpos _) (fun j ↦ hαscale ⟨j.val,by omega⟩)
      (fun j ↦ hαmapD ⟨j.val,by omega⟩) bracketD hcontract_sD hcontract_uD
      (fun x y hxy ↦ ⟨bracketD x y,(huniqueD x y hxy).1,(huniqueD x y hxy).2⟩)
      (fun x y hxy ↦ (huniqueD x y hxy).1) hcontinuousD
      (fun δ hδ hδγ ↦ (hmodulusD δ hδ hδγ).2)
      (seeds.center i) z (by
        change dist (seeds.center i) z ≤ α 3
        rw [dist_comm]
        linarith only [hz,hsmall43,hαpos 3])).1
      U hUout hUo
    change ((fun u ↦ bracketD u z) '' U ⊆ Ws γ z) ∧
      IsOpen ((Subtype.val : Ws γ z → X) ⁻¹' ((fun u ↦ bracketD u z) '' U)) ∧
      ∃ chart : {u : Ws γ (seeds.center i) // (u : X) ∈ U} ≃ₜ
        {w : Ws γ z // (w : X) ∈ (fun u ↦ bracketD u z) '' U},
        (∀ u, (chart u).val.val = bracketD u.val.val z) ∧
        (∀ w, (chart.symm w).val.val = bracketD w.val.val (seeds.center i)) at hrb
    obtain ⟨himg,hopen,chart,hchart,_⟩ := hrb
    have himage : (fun u ↦ bracketD u z) '' D i = productD (D i) {z} := by
      ext v
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact ⟨u,hu,z,rfl,rfl⟩
      · rintro ⟨u,hu,d,hd,he⟩
        have hdz : d = z := hd
        subst d
        exact ⟨u,hu,he⟩
    have hh := BowenRegularClosedPreparation.rebase_interior
      (Ws γ (seeds.center i)) (Ws γ z) U (D i) (fun u ↦ bracketD u z)
      hUγ hCU himg hUo hopen chart hchart c hc
    apply hh.mp
    change bracketD c z ∈ plaqueInterior (Ws γ z) ((fun u ↦ bracketD u z) '' D i)
    rwa [himage]
  have hStarget (z : X) (hz : z ∈ Z) (i : Fin seeds.count) (hi : i ∈ N z)
      (hpos : bracketD z (seeds.center i) ∈ D i) :
      ∀ v ∈ O z ∩ Ws γ z, v ∈ plaqueInterior (Ws γ z) (productD (D i) {z}) := by
    obtain ⟨a,ha,_⟩ := hchoice z hz i hi
    have hσ : a.2 = true := by
      cases he : a.2 with
      | false => exact (Set.disjoint_left.mp (hSsep i)
          (by simpa only [he] using (hQintD i a.2 a.1 z ha).1) hpos).elim
      | true => rfl
    have hsub : O z ∩ Ws γ z ⊆ productD (D i) {z} := by
      intro v hv
      have hvi := hOsub z i hi hv.1
      rw [hchosenEq z hz i hi a ha] at hvi
      have hcv := (hQintD i a.2 a.1 v hvi).1
      have hc : bracketD v (seeds.center i) ∈ D i := by
        have hh := hriSub _ _ hcv
        simpa only [hσ,Ds,Bool.true_eq,ite_true] using hh
      have hiv : i ∈ N v := (hprofile z hz v hv.1).2.symm ▸ hi
      have hvz : dist v z ≤ α 3 :=
        ((Metric.dist_le_diam_of_mem (hPproper z hz).2.1.isBounded
          (subset_closure hv.1) (subset_closure (hOneigh z hz).2)).trans_lt
            (hPmesh z hz)).le.trans (hαdescending 3).le
      exact ⟨_,hc,z,rfl,hreconstructS (seeds.center i) v z
        ((hVdist i v hiv).trans (by linarith only [hαpos 4]))
        ((hVdist i z hi).trans (by linarith only [hαpos 4])) hv.2 hvz⟩
    intro v hv
    refine ⟨⟨v,hv.2⟩,?_,rfl⟩
    apply interior_mono (show (Subtype.val : Ws γ z → X) ⁻¹' O z ⊆
      Subtype.val ⁻¹' productD (D i) {z} from fun q hq ↦ hsub ⟨hq,q.property⟩)
    rw [((hOneigh z hz).1.preimage continuous_subtype_val).interior_eq]
    exact hv.1
  have hnegSInt (i : Fin seeds.count) (c : X) (he : c ∈ Es i) (hc : c ∉ D i) :
      c ∈ plaqueInterior (Ws γ (seeds.center i)) (Ds i false) := by
    refine ⟨⟨c,hEsγ i he⟩,?_,rfl⟩
    change (⟨c,hEsγ i he⟩ : Ws γ (seeds.center i)) ∈ interior
      ((Subtype.val : Ws γ (seeds.center i) → X) ⁻¹'
        plaqueClosure (Ws γ (seeds.center i)) (Es i \ D i))
    simp only [plaqueClosure,Set.preimage_image_eq _ Subtype.val_injective]
    exact ((hEso i).sdiff ((hDdata i).1.isClosed.preimage continuous_subtype_val)).subset_interior_closure
      ⟨he,hc⟩
  have hrestoreS (i : Fin seeds.count) (a : Bool × Bool) (z q : X)
      (hz : z ∈ interior (QuadD i a.2 a.1))
      (hzd : dist z (seeds.center i) < 3 * α 4)
      (hqd : dist q (seeds.center i) < 3 * α 4)
      (hqz : q ∈ Ws γ z) (hd : dist q z ≤ α 3)
      (hu : bracketD q (seeds.center i) ∈ plaqueInterior (Ws γ (seeds.center i)) (Ds i a.2)) :
      q ∈ interior (QuadD i a.2 a.1) := by
    rw [hQintEqD i a.2 a.1]
    have hs : bracketD (seeds.center i) q ∈
        plaqueInterior (Wu γ (seeds.center i)) (Cu i a.1) := by
      rw [hsameUnstable (seeds.center i) q z hqd hzd hqz hd]
      exact (hQintD i a.2 a.1 z hz).2
    exact ⟨_,hu,_,hs,(hsmallProjD (seeds.center i) q hqd).2.2⟩
  have hcollarDual (i : Fin seeds.count) (q : X)
      (hd : dist q (seeds.center i) < 3 * α 4) (hc : bracketD q (seeds.center i) ∈ D i) :
      ∃ j ∈ N (hDmap q), hDmap q ∈ productD (D j) {hDmap q} ∧
        productD (D j) {hDmap q} ⊆ hDmap '' productD (D i) {q} ∧
        hDmap.symm '' plaqueInterior (Ws γ (hDmap q)) (productD (D j) {hDmap q}) ⊆
          plaqueInterior (Ws γ q) (productD (D i) {q}) := by
    simpa only [hflipProduct,hDmap,Homeomorph.symm_symm] using hcollarSLocal i q hd hc
  have hSslicePos (i : Fin seeds.count) (z : X)
      (hz : dist z (seeds.center i) < 3 * α 4) (hs : z ∈ productD (D i) {z}) :
      bracketD z (seeds.center i) ∈ D i := by
    obtain ⟨c,hc,d,hd,he⟩ := hs
    have hdz : d = z := hd
    subst d
    have hp := hprojSliceS (seeds.center i) c z ((hDsData i true).2.2 hc) hz
    rw [he] at hp
    rw [hp]
    exact hc
  have hSintReverse (z : X) (hz : z ∈ Z) (hhz : hDmap z ∈ Z) :
      hDmap ⁻¹' (O (hDmap z) ∩ Ws γ (hDmap z)) ⊆ O z ∩ Ws γ z := by
    intro q hv
    have hvO : hDmap q ∈ O (hDmap z) := hv.1
    have hvU : hDmap q ∈ Ws γ (hDmap z) := hv.2
    have hqz : q ∈ Ws γ z := by
      intro n
      have hh := hshift f γ (h.symm z) (h.symm q)
        (by simpa only [BowenRegularClosedPreparation.pow_apply_iterate,Ws,Set.mem_ofPred_eq,hDmap] using hvU) n
      change dist ((f ^ n) (h (h.symm q))) ((f ^ n) (h (h.symm z))) ≤ γ at hh
      simpa only [h.apply_symm_apply,BowenRegularClosedPreparation.pow_apply_iterate] using hh
    have hvd : dist (hDmap q) (hDmap z) < α 4 :=
      (Metric.dist_le_diam_of_mem (hPproper (hDmap z) hhz).2.1.isBounded
        (subset_closure hvO) (subset_closure (hOneigh (hDmap z) hhz).2)).trans_lt (hPmesh (hDmap z) hhz)
    have hqd : dist q z < α 4 := by
      have hh := hcontract_uD (hDmap z) (hDmap q) (hDmap z) m hvU (fun n ↦ by simpa using hγ.le)
      simp only [← BowenRegularClosedPreparation.pow_apply_iterate,hpowInvD,hDmap.symm_apply_apply] at hh
      exact (hh.trans (mul_le_of_le_one_left dist_nonneg hβ1.le)).trans_lt hvd
    refine ⟨?_,hqz⟩
    apply Set.mem_iInter₂.mpr
    intro i hi
    obtain ⟨a,ha,_⟩ := hchoice z hz i hi
    rw [hchosenEq z hz i hi a ha]
    have hzi : dist z (seeds.center i) < 3 * α 4 :=
      (hVdist i z hi).trans (by linarith only [hαpos 4])
    have hqi : dist q (seeds.center i) < 3 * α 4 := by
      have ht := dist_triangle q z (seeds.center i)
      linarith only [ht,hqd,hVdist i z hi]
    apply hrestoreS i a z q ha hzi hqi hqz (hqd.le.trans (hαdescending 3).le)
    cases hs : a.2 with
    | true =>
      have hsource : bracketD z (seeds.center i) ∈ D i := by
        have hh := hriSub _ _ (hQintD i a.2 a.1 z ha).1
        simpa only [hs,Ds,Bool.true_eq,ite_true] using hh
      obtain ⟨j,hj,hjmem,hjsub,hjint⟩ := hcollarDual i z hzi hsource
      have hjd : dist (hDmap z) (seeds.center j) < 3 * α 4 :=
        (hVdist j (hDmap z) hj).trans (by linarith only [hαpos 4])
      have htarget := hStarget (hDmap z) hhz j hj (hSslicePos j (hDmap z) hjd hjmem)
        (hDmap q) ⟨hvO,hvU⟩
      have hsourceInt : q ∈ plaqueInterior (Ws γ z) (productD (D i) {z}) :=
        hjint ⟨hDmap q,htarget,hDmap.symm_apply_apply q⟩
      have hh := hriSliceS i z q hzi hsourceInt
      simpa only [hs,Ds,Bool.true_eq,ite_true] using hh
    | false =>
      have hqe : bracketD q (seeds.center i) ∈ Es i :=
        hEsinner i (hsmallProjD (seeds.center i) q hqi).1
      have hnot : bracketD q (seeds.center i) ∉ D i := by
        intro hbad
        obtain ⟨j,hj,hjmem,hjsub,_⟩ := hcollarDual i q hqi hbad
        have hj' : j ∈ N (hDmap z) := (hprofile (hDmap z) hhz (hDmap q) hvO).2 ▸ hj
        have hvj : dist (hDmap q) (seeds.center j) < 3 * α 4 :=
          (hVdist j (hDmap q) hj).trans (by linarith only [hαpos 4])
        have hzj : dist (hDmap z) (seeds.center j) < 3 * α 4 :=
          (hVdist j (hDmap z) hj').trans (by linarith only [hαpos 4])
        have hvpos := hSslicePos j (hDmap q) hvj hjmem
        obtain ⟨b,hb,_⟩ := hchoice (hDmap z) hhz j hj'
        have hvb := hOsub (hDmap z) j hj' hvO
        rw [hchosenEq (hDmap z) hhz j hj' b hb] at hvb
        have hbtrue : b.2 = true := by
          cases hb1 : b.2 with
          | false => exact (Set.disjoint_left.mp (hSsep j)
              (by simpa only [hb1] using (hQintD j b.2 b.1 (hDmap q) hvb).1) hvpos).elim
          | true => rfl
        have hzpos : bracketD (hDmap z) (seeds.center j) ∈ D j := by
          have hh := hriSub _ _ (hQintD j b.2 b.1 (hDmap z) hb).1
          simpa only [hbtrue,Ds,Bool.true_eq,ite_true] using hh
        have hreverse : hDmap z ∈ Ws γ (hDmap q) := fun n ↦ by simpa only [dist_comm] using hvU n
        have hzslice : hDmap z ∈ productD (D j) {hDmap q} :=
          ⟨_,hzpos,hDmap q,rfl,hreconstructS (seeds.center j) (hDmap z) (hDmap q) hzj hvj hreverse
            (by rw [dist_comm]; exact hvd.le.trans (hαdescending 3).le)⟩
        obtain ⟨w,hw,he⟩ := hjsub hzslice
        have hwz : w = z := hDmap.injective he
        subst w
        obtain ⟨c,hc,d,hd,he⟩ := hw
        have hdq : d = q := hd
        subst d
        have hproj := hprojSliceS (seeds.center i) c q ((hDsData i true).2.2 hc) hqi
        rw [he] at hproj
        have hzpos : bracketD z (seeds.center i) ∈ D i := by rw [hproj]; exact hc
        exact Set.disjoint_left.mp (hSsep i)
          (by simpa only [hs] using (hQintD i a.2 a.1 z ha).1) hzpos
      have hh := hnegSInt i _ hqe hnot
      simpa only [hs] using hh
  have hSint (z : X) (hz : z ∈ Z) (hhz : h z ∈ Z) :
      h '' (O z ∩ Ws γ z) ⊆ O (h z) ∩ Ws γ (h z) := by
    rintro v ⟨q,hq,rfl⟩
    apply hSintReverse (h z) hhz (by simpa only [hDmap,h.symm_apply_apply] using hz)
    simpa only [Set.mem_preimage,hDmap,h.symm_apply_apply] using hq
  have hmarkov := Topology.manning_bowen_markov_closure_transport h Z
    (fun z ↦ P z ∩ Wu γ z) (fun z ↦ P z ∩ Ws γ z)
    (fun z ↦ O z ∩ Wu γ z) (fun z ↦ O z ∩ Ws γ z)
    hsliceUreg hsliceSreg hUint hSint
  have hfinalAtoms : IsOpen Z ∧ Dense Z ∧
      (∀ z ∈ Z, ∀ i ∈ N z, ∃! a : Bool × Bool, z ∈ interior (Quad i a.1 a.2)) ∧
      (P '' Z).Finite ∧ (⋃ z ∈ Z, P z) = Set.univ ∧
      (∀ z ∈ Z, proper (P z) ∧ interior (P z) = O z) ∧
      (∀ z ∈ Z, ∀ w ∈ Z, P z ≠ P w → Disjoint (interior (P z)) (interior (P w))) ∧
      (∀ z ∈ Z, h z ∈ Z → P (h z) ∩ Wu γ (h z) ⊆ h '' (P z ∩ Wu γ z) ∧
        h '' (P z ∩ Ws γ z) ⊆ P (h z) ∩ Ws γ (h z)) :=
    ⟨hZo,hZd,hchoice,hPfinite.subset (Set.image_subset_range P Z),hPcover,
      fun z hz ↦ ⟨hPproper z hz,hOregular z hz⟩,hPdisjoint,hmarkov⟩
  refine ⟨s,t,target,y,reverseTarget,reverseY,Cseq,Dseq,C,D,Eu,Es,?_,hseedCover,
    ?_,?_,?_,?_,?_,?_,?_,hstages,?_,?_,hAcover,?_,?_⟩
  · intro i
    exact ⟨seeds.unstableFactor_compact i,seeds.stableFactor_compact i,hCsub i,hDsub i,
      hCreg i,hDreg i,hCi i,hDi i,hseedProper i,
      by simpa only [hrect] using seeds.center_interior i,hseedDiam i⟩
  · intro q
    exact ⟨hFmem q,fun z hz ↦ hFs q z hz,fun z hz ↦ hFu q z hz⟩
  · intro i
    simp_rw [hwu,hws] at hy
    exact ⟨hy i,hys i⟩
  · intro i
    simp_rw [hwu,hws] at hyr
    exact ⟨hyr i,hyrs i⟩
  · rw [hCseqDef]
    rfl
  · rw [hDseqDef]
    rfl
  · intro n i
    rw [hCseqDef]
    rfl
  · intro n i
    rw [hDseqDef]
    ext q
    simp only [Bowen.stage,Homeomorph.symm_symm,Set.mem_iUnion,Set.mem_image,
      Bowen.bi,product,Set.mem_ofPred_eq]
    constructor <;> rintro ⟨j,v,⟨c,hc,d,hd,hb⟩,he⟩ <;>
      exact ⟨j,v,⟨d,hd,c,hc,hb⟩,he⟩
  · intro i
    exact ⟨congrFun hCDef i,congrFun hDDef i⟩
  · intro i
    exact ⟨(hCdata i).1,(hDdata i).1,hClimitReg i,hDlimitReg i,
      (hCdata i).2.1,(hDdata i).2.1,(hCdata i).2.2.1,(hDdata i).2.2.1,
      (hAproper i).1,hAcenter i,(hAproper i).2⟩
  · intro i
    exact ⟨hEuγ i,hEsγ i,hEuo i,hEso i,hEuinner i,hEuouter i,hEsinner i,hEsouter i⟩
  · exact hfinalAtoms

end HolomorphicAnosov
