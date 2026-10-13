import HolomorphicAnosov.Topology.CompactPairCoreUniformContinuity
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Logic.Function.Iterate

/-!
# Bowen's initial cover and uniform saturation

This module formalizes `topo.manning_bowen_initial_cover_uniform_saturation`.
Source: Rufus Bowen, *Markov Partitions for Axiom A Diffeomorphisms*,
American Journal of Mathematics 92 (1970), pp.725–747: Fact 1 and Lemma 2,
pp.726–727; Lemmas 5–7, pp.728–729; Lemma 10, p.730; the initial cover,
p.731; and Lemma 13, pp.731–732. The obtained primary text is
`literature/Markov Partitions for Axiom A Diffeomorphisms.txt` (with matching PDF).

The map throughout is the original homeomorphism, not a positive iterate.
The local product homeomorphisms below are exactly the quantified input
hypothesis, rather than an inferred product structure. The theorem supplies
one finite cover and one saturation radius for both directions and every
closed plaque point in the selected rectangles.
-/

namespace HolomorphicAnosov

open Set
open scoped Topology _root_.Topology

universe u

variable {X : Type u} [MetricSpace X]

/-- The full closed stable orbit plaque for the original homeomorphism;
Bowen (1970), Fact 1, pp.726–727. Natural time includes zero. -/
def manningBowenStablePlaque (T : X ≃ₜ X) (r : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ r}

/-- The full closed unstable orbit plaque, using genuine inverse iterates;
Bowen (1970), Fact 1, pp.726–727. -/
def manningBowenUnstablePlaque (T : X ≃ₜ X) (r : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ r}

/-- The actual open pair domain of the canonical bracket;
Bowen (1970), Fact 1, p.727. -/
def manningBowenPairDomain (ε : ℝ) : Set (X × X) :=
  {p | dist p.1 p.2 < ε}

/-- Every displayed bracket on these two factors is defined;
Bowen (1970), Lemmas 5–7, pp.728–729. -/
def manningBowenBracketDefined (ε : ℝ) (U V : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ V, dist x y < ε

/-- The literal image of a partial bracket on its actual pair domain;
Bowen (1970), notation `[U,V]`, pp.728–731. The first factor is unstable. -/
def manningBowenBracketImage {ε : ℝ}
    (bracket : manningBowenPairDomain (X := X) ε → X) (U V : Set X) : Set X :=
  {z | ∃ p : manningBowenPairDomain (X := X) ε,
    p.val.1 ∈ U ∧ p.val.2 ∈ V ∧ bracket p = z}

/-- Relative regular closedness in the full plaque's original subtype topology;
Bowen (1970), Lemma 10 and the initial factor choice, pp.730–731. -/
def manningBowenRelativeRegularClosed (P C : Set X) : Prop :=
  closure (interior (Subtype.val ⁻¹' C : Set P)) = (Subtype.val ⁻¹' C : Set P)

/-- Containment of a relative neighborhood of the marked center, expressed
using an actual ambient open set; Bowen (1970), the initial cover, p.731. -/
def manningBowenContainsRelativeNeighborhood (P C : Set X) (x : X) : Prop :=
  ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ P ∩ N ⊆ C

/-- The explicit canonical-coordinate hypotheses used for Bowen's initial cover.

Source: Bowen (1970), Fact 1, p.727, and Lemma 7, p.729. The partial bracket
is defined only on `dist < ε`; its singleton intersection law and continuity
are actual data. The final field supplies precisely the assumed local product
homeomorphism for relatively open subsets of the full γ-plaques inside the
r₀-plaques. Its value is the same partial bracket, not an unrelated product map.
No connectedness, smooth structure, or transitivity is required.
-/
structure ManningBowenCanonicalCoordinates (T : X ≃ₜ X) (γ rate ε : ℝ) where
  gamma_pos : 0 < γ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  epsilon_pos : 0 < ε
  stable_contraction : ∀ x : X, ∀ y ∈ manningBowenStablePlaque T γ x,
    ∀ z ∈ manningBowenStablePlaque T γ x, ∀ n : ℕ,
      dist ((T : X → X)^[n] y) ((T : X → X)^[n] z) ≤ rate ^ n * dist y z
  unstable_contraction : ∀ x : X, ∀ y ∈ manningBowenUnstablePlaque T γ x,
    ∀ z ∈ manningBowenUnstablePlaque T γ x, ∀ n : ℕ,
      dist ((T.symm : X → X)^[n] y) ((T.symm : X → X)^[n] z) ≤ rate ^ n * dist y z
  bracket : manningBowenPairDomain (X := X) ε → X
  bracket_continuous : Continuous bracket
  bracket_intersection : ∀ p : manningBowenPairDomain (X := X) ε,
    manningBowenStablePlaque T γ p.val.1 ∩ manningBowenUnstablePlaque T γ p.val.2 =
      {bracket p}
  productRadius : ℝ
  productRadius_pos : 0 < productRadius
  productRadius_lt_gamma : productRadius < γ
  productRadius_lt_epsilon : productRadius < ε / 3
  local_product : ∀ (x : X) (U V : Set X),
    U ⊆ manningBowenUnstablePlaque T γ x →
    V ⊆ manningBowenStablePlaque T γ x →
    IsOpen (Subtype.val ⁻¹' U : Set (manningBowenUnstablePlaque T γ x)) →
    IsOpen (Subtype.val ⁻¹' V : Set (manningBowenStablePlaque T γ x)) →
    U ⊆ manningBowenUnstablePlaque T productRadius x →
    V ⊆ manningBowenStablePlaque T productRadius x →
    IsOpen (manningBowenBracketImage bracket U V) ∧
      ∃ H : (U × V) ≃ₜ manningBowenBracketImage bracket U V,
        ∀ p : U × V, ∀ hp : dist (p.1 : X) (p.2 : X) < ε,
          (H p : X) = bracket ⟨((p.1 : X), (p.2 : X)), hp⟩

/-- Concrete finite initial-cover data with both uniform transverse margins and
full closed-plaque saturation; Bowen (1970), pp.730–732, especially Lemma 13.

The finite nonempty index set is `Fin count`, with `count > 0`. Each rectangle
is the literal bracket image of its original compact factors. The factors'
relative topology is that of the full γ-plaques, and saturation has no
relative-interior restriction on the tested points. No continuity of the
selection function is asserted.
-/
structure ManningBowenInitialCover (T : X ≃ₜ X) {γ rate ε : ℝ}
    (H : ManningBowenCanonicalCoordinates T γ rate ε) (δ α : ℝ) where
  count : ℕ
  count_pos : 0 < count
  center : Fin count → X
  unstableFactor : Fin count → Set X
  stableFactor : Fin count → Set X
  rectangle : Fin count → Set X
  saturationRadius : ℝ
  saturationRadius_pos : 0 < saturationRadius
  select : X → Fin count
  unstableFactor_nonempty : ∀ i, (unstableFactor i).Nonempty
  stableFactor_nonempty : ∀ i, (stableFactor i).Nonempty
  unstableFactor_compact : ∀ i, IsCompact (unstableFactor i)
  stableFactor_compact : ∀ i, IsCompact (stableFactor i)
  unstableFactor_subset : ∀ i,
    unstableFactor i ⊆ manningBowenUnstablePlaque T δ (center i)
  stableFactor_subset : ∀ i,
    stableFactor i ⊆ manningBowenStablePlaque T δ (center i)
  unstableFactor_regular : ∀ i, manningBowenRelativeRegularClosed
    (manningBowenUnstablePlaque T γ (center i)) (unstableFactor i)
  stableFactor_regular : ∀ i, manningBowenRelativeRegularClosed
    (manningBowenStablePlaque T γ (center i)) (stableFactor i)
  unstableFactor_neighborhood : ∀ i, manningBowenContainsRelativeNeighborhood
    (manningBowenUnstablePlaque T γ (center i)) (unstableFactor i) (center i)
  stableFactor_neighborhood : ∀ i, manningBowenContainsRelativeNeighborhood
    (manningBowenStablePlaque T γ (center i)) (stableFactor i) (center i)
  factor_brackets_defined : ∀ i,
    manningBowenBracketDefined ε (unstableFactor i) (stableFactor i)
  rectangle_eq : ∀ i,
    rectangle i = manningBowenBracketImage H.bracket (unstableFactor i) (stableFactor i)
  rectangle_nonempty : ∀ i, (rectangle i).Nonempty
  rectangle_compact : ∀ i, IsCompact (rectangle i)
  rectangle_regular : ∀ i, rectangle i = closure (interior (rectangle i))
  center_interior : ∀ i, center i ∈ interior (rectangle i)
  rectangle_diam : ∀ i, Metric.diam (rectangle i) < α / 2
  interior_cover : ∀ x : X, ∃ i, x ∈ interior (rectangle i)
  rectangle_brackets_defined : ∀ i,
    manningBowenBracketDefined ε (rectangle i) (rectangle i)
  rectangle_bracket_closed : ∀ i, ∀ p : manningBowenPairDomain (X := X) ε,
    p.val.1 ∈ rectangle i → p.val.2 ∈ rectangle i → H.bracket p ∈ rectangle i
  unstable_transverse_defined : ∀ i, ∀ y ∈ manningBowenStablePlaque T (2 * α) (center i),
    manningBowenBracketDefined ε (unstableFactor i) {y}
  unstable_transverse_margin : ∀ i, ∀ y ∈ manningBowenStablePlaque T (2 * α) (center i),
    manningBowenBracketImage H.bracket (unstableFactor i) {y} ⊆
      manningBowenUnstablePlaque T α y
  stable_transverse_defined : ∀ i, ∀ y ∈ manningBowenUnstablePlaque T (2 * α) (center i),
    manningBowenBracketDefined ε {y} (stableFactor i)
  stable_transverse_margin : ∀ i, ∀ y ∈ manningBowenUnstablePlaque T (2 * α) (center i),
    manningBowenBracketImage H.bracket {y} (stableFactor i) ⊆
      manningBowenStablePlaque T α y
  selected_membership : ∀ x : X, x ∈ rectangle (select x)
  selected_stable_saturation : ∀ x : X,
    ∀ z ∈ rectangle (select x) ∩ manningBowenUnstablePlaque T γ x,
      manningBowenStablePlaque T saturationRadius z ⊆ rectangle (select x)
  selected_unstable_saturation : ∀ x : X,
    ∀ y ∈ rectangle (select x) ∩ manningBowenStablePlaque T γ x,
      manningBowenUnstablePlaque T saturationRadius y ⊆ rectangle (select x)

/-- Bowen's initial cover with a single uniform full-plaque saturation margin.

Source: Bowen (1970), Fact 1 and Lemma 2, pp.726–727; Lemmas 5–7,
pp.728–729; Lemma 10, p.730; the initial cover, p.731; and Lemma 13,
pp.731–732. The simultaneous transverse margins are the compact-bracket
uniformity expansion of the source scale choices. The proof uses neither
transitivity nor a change from the original homeomorphism to an iterate.

Complete natural-language proof of the current DAG node:

B1. Every γ-plaque is closed: each orbit-distance inequality is a closed condition because T and
T⁻¹ and their finite iterates are continuous; take their countable intersection. Hence it is
compact. For either sign, if 0<r≤γ, W_r(x)=W_γ(x)∩closedBall(x,r): the forward/backward
contraction on the common γ-plaque containing x bounds every orbit distance by its time-zero
distance. Plaque symmetry and W_r(W_s(x))⊆W_(r+s)(x) follow directly from the definitions and the
triangle inequality at every iterate. These statements include r=γ and singleton plaques.

Source: Bowen Lemma2(a)–(c) p.727.

B2. Put κ=ε/2. The closed pair core K={(p,q):d(p,q)≤κ} is a closed subset of compact X×X, hence
compact, and lies strictly inside the bracket domain. Restrict bracket continuity to K and apply
Heine–Cantor. Since [x,x]=x by intersection uniqueness, for every e>0 there is s(e)>0, s(e)<κ,
such that d(p,q)≤s(e) implies d([p,q],p)<e and d([p,q],q)<e. Comparison with (p,p) and (q,q)
proves both bounds, with a halved modulus to handle ≤. For e≤γ, B1 turns the bounds into
[p,q]∈W^s_e(p)∩W^u_e(q). All uniform continuity in this proof is on K, not on the open whole
bracket domain.

Source: Bowen Lemma5 p.728; compact-core justification of its uniform-continuity sentence.

B3. Fix H=γ/4 and choose h>0 with h<min(γ/20,κ/20,r₀/4,s(H)/10). Choose t>0 with
t<min(h/10,s(h)/10). For any four base points w,x,y,z of mutual distance ≤3t, every direct bracket
moves each argument by <h. Each nested pair has distance at most 3t+2h<s(H), so its bracket is
defined and belongs to the H-plaques of its arguments. Thus [x,[y,z]] lies in W^s_H(x) and in
W^u_(H+h)(z)⊆W^u_γ(z), and uniqueness gives [x,[y,z]]=[x,z]. Similarly [[x,y],z]=[x,z]. Finally
[[x,w],[y,z]] lies in W^s_(H+h)(x)∩W^u_(H+h)(z), and again equals [x,z]. The reference
intersection W^s_γ(x)∩W^u_γ(z) is unique since d(x,z)≤3t<ε. This proves all absorption identities
with explicit domain and radius guards, using B1–B2; there is no hidden proper-rectangle premise.

Source: Bowen Lemma6(b) pp.728–729, its triangle/uniqueness proof written out.

B4. Choose 0<α<min(η,γ/4,ε/8,t/10,r₀/10). On K choose a uniform displacement modulus μ>0 for
bracket-output distance <α when one argument moves by at most μ, taking a half modulus. Choose
0<δ<min(α/16,μ/2,s(α/16)/3). For any x, c∈W^u_δ(x) and y∈W^s_(2α)(x), both (c,y) and (x,y) lie in
K because d(c,y)≤δ+2α<κ. Since [x,y]=y by uniqueness and d(c,x)≤δ<μ, d([c,y],y)<α. The bracket
already lies in W^u_γ(y), so B1 gives [c,y]∈W^u_α(y). Exchanging the coordinates gives
[y,d]∈W^s_α(y) for every d∈W^s_δ(x) and y∈W^u_(2α)(x). This δ is fixed before choosing any center
or seed, and includes all closed plaque points, including boundary points.

Source: Bowen Lemmas2(c),5 pp.727–728 and initial scale choice p.731; simultaneous transverse-modulus expansion.

B5. For each x let B^u_x=W^u_γ(x)∩ball(x,δ/2), and let C_x be its closure in W^u_γ(x); define
B^s_x,D_x dually. Relative closedness, closedness of the γ-plaques, and compactness of X make
C_x,D_x compact in X. They are nonempty, contain their marked relative open balls, and lie in
W^u_γ(x)∩closedBall(x,δ/2), respectively its stable analogue. B1 puts them inside the δ-plaques.
Because B^u_x,B^s_x are open in the full γ-plaques, closure_interior_idem proves the factors are
regular closed in exactly those topologies. No connectedness or positive plaque dimension is
needed.

Source: Bowen initial cover p.731 and relative regular-closed factor hypothesis in Lemma10 p.730.

B6. Let U_x=W^u_γ(x)∩ball(x,r₀), V_x=W^s_γ(x)∩ball(x,r₀). B1 and the assumed source
product-openness hypothesis give a homeomorphism H_x:U_x×V_x→O_x=[U_x,V_x], with O_x open in X.
Both compact factors lie inside these larger open factor neighborhoods. Their regular-closed
identities restrict to U_x,V_x because the factors are closed and contained in them. The product
closure/interior identities and homeomorphism transport show H_x(C_x×D_x) is the closure of its
interior in O_x. It is compact, by continuity on the compact product, hence closed in metric X; as
O_x is open, its ambient closure of interior equals itself as well. Its ambient interior contains
H_x(B^u_x×B^s_x), an open neighborhood of [x,x]=x. Write A_x=H_x(C_x×D_x). All c,d in the factors
are within δ/2 of x, so d(c,d)≤δ<s(α/16). B2 gives d([c,d],x)<α/16+δ/2<α/8. Thus A_x lies in the
closed α/8-ball and diam A_x≤α/4<α/2. The quartet law B3 applied to c,d,c′,d′ gives
[[c,d],[c′,d′]]=[c,d′]∈A_x, so A_x is bracket closed. This proves rectangle existence locally
rather than invoking a removed geometry node.

Source: Bowen Lemma10 p.730, following Lemma7 p.729 and Lemma6(a)–(b) p.728.

B7. The open family int_X A_x covers X because x∈int_X A_x. Apply the arbitrary-index
diameter-form Lebesgue theorem to obtain L>0. At ρ=L/4 use the compact finite open-ball cover to
select a finite set S⊆X. For each s∈S the nonempty closed ball closedBall(s,ρ) has diameter ≤2ρ<L,
so choose j(s) with that ball contained in int_X A_(j(s)). The finite image I={j(s):s∈S} is
nonempty since X is nonempty and the balls cover X. Its selected original interiors cover X.
Retain the original center x_i=i and original factors C_i=C_(x_i), D_i=D_(x_i); the ball-cover
centers need not be those marked centers. All B4–B6 properties, including both uniform margins
with the same α,δ, survive this selection. No factor is intersected, relabeled as a plaque at a
different center, or replaced.

Source: Bowen initial finite interior cover p.731; explicit compact finite-selection argument.

B8. For this finite interior cover obtain ℓ>0 from the same diameter-form Lebesgue theorem and put
b=ℓ/4. Every closed b-ball is nonempty and has diameter ≤2b<ℓ. Choose F(x)∈I with
closedBall(x,b)⊆int_X A_(F(x)); no continuity of F is asserted. On K choose a common uniform
bracket displacement modulus for output distance <b, and choose 0<a<min(γ,t/10,κ/10) smaller than
half that modulus. This fixes a and F for all x, both plaque directions, and all slices of the
original finite family.

Source: Bowen Lemma13 pp.731–732.

B9. Fix x and A=A_(F(x)). Then x∈A. Let z∈A∩W^u_γ(x) and w∈W^s_a(z). Since diam A<α/2 and
d(z,w)≤a, the triple x,z,w has mutual distances <α/2+a<3t, and both (x,z),(x,w) lie in K. Plaque
symmetry and uniqueness give [x,z]=x and [z,w]=w. Uniform continuity, moving only z to w, gives
d([x,w],x)=d([x,w],[x,z])<b. Hence [x,w] belongs to the selected closed b-ball and therefore A.
Bracket closure of A and the B3 absorption law imply w=[z,w]=[z,[x,w]]∈A. This proves W^s_a(z)⊆A
for every closed unstable slice point z, including z on any boundary.

Source: Bowen proof of Lemma13 p.732, with Lemma6(b) domain guards.

B10. Let y∈A∩W^s_γ(x) and v∈W^u_a(y). Now [y,x]=x, [v,y]=v, and (y,x),(v,x) lie in K by the same
α/2+a bound. Uniform continuity gives d([v,x],x)<b, so [v,x]∈A. The other absorption law gives
v=[v,y]=[[v,x],y]∈A. Thus W^u_a(y)⊆A using the same a,F and seeds. Every factor was nonempty in B5
and every finite index selection nonempty in B7. Singleton/zero-dimensional plaques satisfy the
same relative-open-ball construction. The conclusion does not assert plaque equality between T and
T^m: if a later proof changes the map, it must transport its orbit-plaque definitions explicitly.

Source: Bowen Lemma13 p.732, dual inclusion; the iterate is introduced immediately after this lemma.

-/
theorem manningBowenInitialCoverUniformSaturation
    [CompactSpace X] [Nonempty X] (T : X ≃ₜ X) (γ rate ε : ℝ)
    (H : ManningBowenCanonicalCoordinates T γ rate ε) (η : ℝ) (hη : 0 < η) :
    ∃ δ α : ℝ, 0 < δ ∧ δ < α ∧ α < η ∧ α < γ / 4 ∧ α < ε / 8 ∧
      Nonempty (ManningBowenInitialCover T H δ α) := by
  classical
  have hself (f : X ≃ₜ X) {r : ℝ} (hr : 0 ≤ r) (x : X) :
      x ∈ manningBowenStablePlaque f r x := by
    intro n
    simpa only [dist_self] using hr
  have hzero (f : X ≃ₜ X) {r : ℝ} {x y : X}
      (hy : y ∈ manningBowenStablePlaque f r x) : dist x y ≤ r := hy 0
  have hmono (f : X ≃ₜ X) {r s : ℝ} (hrs : r ≤ s) (x : X) :
      manningBowenStablePlaque f r x ⊆ manningBowenStablePlaque f s x :=
    fun _ hy n ↦ (hy n).trans hrs
  have hclosed (f : X ≃ₜ X) (r : ℝ) (x : X) :
      IsClosed (manningBowenStablePlaque f r x) := by
    change IsClosed {y | ∀ n : ℕ, dist ((f : X → X)^[n] x) ((f : X → X)^[n] y) ≤ r}
    simp only [ofPred_forall]
    exact isClosed_iInter fun n ↦
      isClosed_le (continuous_const.dist (f.continuous.iterate n)) continuous_const
  have hsmall (f : X ≃ₜ X)
      (hc : ∀ x : X, ∀ y ∈ manningBowenStablePlaque f γ x,
        ∀ z ∈ manningBowenStablePlaque f γ x, ∀ n : ℕ,
          dist ((f : X → X)^[n] y) ((f : X → X)^[n] z) ≤ rate ^ n * dist y z)
      {r : ℝ} {x y : X} (hy : y ∈ manningBowenStablePlaque f γ x)
      (hd : dist x y ≤ r) : y ∈ manningBowenStablePlaque f r x := by
    intro n
    exact (hc x x (hself f H.gamma_pos.le x) y hy n).trans
      ((mul_le_of_le_one_left dist_nonneg
        (pow_le_one₀ H.rate_pos.le H.rate_lt_one.le)).trans hd)
  have hmem (p : manningBowenPairDomain (X := X) ε) :
      H.bracket p ∈ manningBowenStablePlaque T γ p.val.1 ∩
        manningBowenUnstablePlaque T γ p.val.2 := by
    rw [H.bracket_intersection]
    exact mem_singleton _
  have hdiag (x : X) :
      H.bracket ⟨(x, x), by simpa [manningBowenPairDomain] using H.epsilon_pos⟩ = x := by
    symm
    apply mem_singleton_iff.mp
    rw [← H.bracket_intersection]
    exact ⟨hself T H.gamma_pos.le x, hself T.symm H.gamma_pos.le x⟩
  have hmod : ∀ e : ℝ, 0 < e → ∃ d : ℝ, 0 < d ∧ d < ε / 2 ∧
      ∀ (p q : manningBowenPairDomain (X := X) ε),
        dist p.val.1 p.val.2 ≤ ε / 2 → dist q.val.1 q.val.2 ≤ ε / 2 →
        dist p.val q.val ≤ d → dist (H.bracket p) (H.bracket q) < e := by
    intro e he
    exact compactPairCore_uniformModulus H.epsilon_pos H.bracket_continuous e he
  have hdisp : ∀ e : ℝ, 0 < e → ∃ d : ℝ, 0 < d ∧ d < ε / 2 ∧
      ∀ p : manningBowenPairDomain (X := X) ε, dist p.val.1 p.val.2 ≤ d →
        dist p.val.1 (H.bracket p) < e ∧ dist p.val.2 (H.bracket p) < e := by
    intro e he
    obtain ⟨d, hd, hdε, hdmod⟩ := hmod e he
    refine ⟨d, hd, hdε, ?_⟩
    intro p hp
    have hpp : dist p.val.1 p.val.2 ≤ ε / 2 := hp.trans hdε.le
    constructor
    · have h := hdmod p
        ⟨(p.val.1, p.val.1), by simpa [manningBowenPairDomain] using H.epsilon_pos⟩
        hpp (by simpa using (half_pos H.epsilon_pos).le) (by
          simpa [Prod.dist_eq, dist_comm] using hp)
      simpa only [hdiag, dist_comm] using h
    · have h := hdmod p
        ⟨(p.val.2, p.val.2), by simpa [manningBowenPairDomain] using H.epsilon_pos⟩
        hpp (by simpa using (half_pos H.epsilon_pos).le) (by
          simpa [Prod.dist_eq] using hp)
      simpa only [hdiag, dist_comm] using h
  have hsmallmod : ∀ e : ℝ, 0 < e → ∃ d : ℝ, 0 < d ∧ d < ε / 2 ∧
      ∀ p : manningBowenPairDomain (X := X) ε, dist p.val.1 p.val.2 ≤ d →
        H.bracket p ∈ manningBowenStablePlaque T e p.val.1 ∩
          manningBowenUnstablePlaque T e p.val.2 := by
    intro e he
    obtain ⟨d, hd, hdε, hdd⟩ := hdisp e he
    refine ⟨d, hd, hdε, ?_⟩
    intro p hp
    exact ⟨hsmall T H.stable_contraction (hmem p).1 (hdd p hp).1.le,
      hsmall T.symm H.unstable_contraction (hmem p).2 (hdd p hp).2.le⟩
  obtain ⟨σ, hσ, hσε, hσsmall⟩ := hsmallmod (γ / 4) (by linarith [H.gamma_pos])
  obtain ⟨α, hα, hαbound⟩ := exists_between
    (show (0 : ℝ) < min η (min (γ / 4) (min (ε / 8) σ)) by
      exact lt_min hη (lt_min (by linarith [H.gamma_pos])
        (lt_min (by linarith [H.epsilon_pos]) hσ)))
  have hαγ : α < γ / 4 := ((lt_min_iff.mp hαbound).2 |> lt_min_iff.mp).1
  have hαε : α < ε / 8 :=
    (lt_min_iff.mp ((lt_min_iff.mp hαbound).2 |> lt_min_iff.mp).2).1
  have hασ : α < σ :=
    (lt_min_iff.mp ((lt_min_iff.mp hαbound).2 |> lt_min_iff.mp).2).2
  obtain ⟨μ, hμ, hμε, hμmod⟩ := hmod α hα
  obtain ⟨ν, hν, hνε, hνdisp⟩ := hdisp (α / 8) (by linarith)
  obtain ⟨δ, hδ, hδbound⟩ := exists_between
    (lt_min (lt_min (by linarith : 0 < α / 16) hμ) (lt_min H.productRadius_pos (half_pos hν)))
  have hδα2 : δ < α / 16 := (lt_min_iff.mp (lt_min_iff.mp hδbound).1).1
  have hδα : δ < α := by linarith
  have hδμ : δ < μ := (lt_min_iff.mp (lt_min_iff.mp hδbound).1).2
  have hδr : δ < H.productRadius := (lt_min_iff.mp (lt_min_iff.mp hδbound).2).1
  have hδν : δ < ν / 2 := (lt_min_iff.mp (lt_min_iff.mp hδbound).2).2
  have htransverse_u (x c y : X)
      (hc : c ∈ manningBowenUnstablePlaque T δ x)
      (hy : y ∈ manningBowenStablePlaque T (2 * α) x) :
      ∃ hp : dist c y < ε,
        H.bracket ⟨(c, y), hp⟩ ∈ manningBowenUnstablePlaque T α y := by
    have hxc := hzero T.symm hc
    have hxy := hzero T hy
    have hcy : dist c y ≤ δ + 2 * α := by
      calc
        dist c y ≤ dist c x + dist x y := dist_triangle _ _ _
        _ ≤ δ + 2 * α := add_le_add (by simpa [dist_comm] using hxc) hxy
    have hpair : dist c y < ε := by linarith
    have hxyε : dist x y < ε := by linarith
    have hbase : H.bracket ⟨(x, y), hxyε⟩ = y := by
      symm
      apply mem_singleton_iff.mp
      rw [← H.bracket_intersection]
      exact ⟨hmono T (by linarith) x hy, hself T.symm H.gamma_pos.le y⟩
    refine ⟨hpair, hsmall T.symm H.unstable_contraction (hmem ⟨(c,y),hpair⟩).2 ?_⟩
    have hh := hμmod ⟨(c, y), hpair⟩ ⟨(x, y), hxyε⟩
      (by linarith) (by linarith) (by
        simpa [Prod.dist_eq, dist_comm] using hxc.trans hδμ.le)
    simpa only [hbase, dist_comm] using hh.le
  have htransverse_s (x y d : X)
      (hy : y ∈ manningBowenUnstablePlaque T (2 * α) x)
      (hd : d ∈ manningBowenStablePlaque T δ x) :
      ∃ hp : dist y d < ε,
        H.bracket ⟨(y, d), hp⟩ ∈ manningBowenStablePlaque T α y := by
    have hxd := hzero T hd
    have hxy := hzero T.symm hy
    have hyd : dist y d ≤ 2 * α + δ := by
      calc
        dist y d ≤ dist y x + dist x d := dist_triangle _ _ _
        _ ≤ 2 * α + δ := add_le_add (by simpa [dist_comm] using hxy) hxd
    have hpair : dist y d < ε := by linarith
    have hyxε : dist y x < ε := by rw [dist_comm]; linarith
    have hbase : H.bracket ⟨(y, x), hyxε⟩ = y := by
      symm
      apply mem_singleton_iff.mp
      rw [← H.bracket_intersection]
      exact ⟨hself T H.gamma_pos.le y, hmono T.symm (by linarith) x hy⟩
    refine ⟨hpair, hsmall T H.stable_contraction (hmem ⟨(y,d),hpair⟩).1 ?_⟩
    have hh := hμmod ⟨(y, d), hpair⟩ ⟨(y, x), hyxε⟩
      (by linarith) (by dsimp; rw [dist_comm]; linarith) (by
        simpa [Prod.dist_eq, dist_comm] using hxd.trans hδμ.le)
    simpa only [hbase, dist_comm] using hh.le
  have hseed (f : X ≃ₜ X)
      (hc : ∀ x : X, ∀ y ∈ manningBowenStablePlaque f γ x,
        ∀ z ∈ manningBowenStablePlaque f γ x, ∀ n : ℕ,
          dist ((f : X → X)^[n] y) ((f : X → X)^[n] z) ≤ rate ^ n * dist y z)
      (x : X) : ∃ C : Set X,
        C.Nonempty ∧ IsCompact C ∧ C ⊆ manningBowenStablePlaque f δ x ∧
        manningBowenRelativeRegularClosed (manningBowenStablePlaque f γ x) C ∧
        manningBowenContainsRelativeNeighborhood (manningBowenStablePlaque f γ x) C x := by
    let P := manningBowenStablePlaque f γ x
    let B : Set P := Subtype.val ⁻¹' Metric.ball x (δ / 2)
    let C : Set X := Subtype.val '' closure B
    have hP : IsClosed P := hclosed f γ x
    have : CompactSpace P := isCompact_iff_compactSpace.mp hP.isCompact
    have hB : IsOpen B := Metric.isOpen_ball.preimage continuous_subtype_val
    have hxB : (⟨x, hself f H.gamma_pos.le x⟩ : P) ∈ B := by
      simpa [B] using half_pos hδ
    have hCB : closure B ⊆
        (Subtype.val ⁻¹' Metric.closedBall x (δ / 2) : Set P) := by
      apply closure_minimal
      · exact preimage_mono Metric.ball_subset_closedBall
      · exact Metric.isClosed_closedBall.preimage continuous_subtype_val
    have hCpre : (Subtype.val ⁻¹' C : Set P) = closure B :=
      Subtype.val_injective.preimage_image _
    refine ⟨C, ⟨x, ⟨⟨x, hself f H.gamma_pos.le x⟩, subset_closure hxB, rfl⟩⟩,
      isClosed_closure.isCompact.image continuous_subtype_val, ?_, ?_, ?_⟩
    · rintro y ⟨q, hq, rfl⟩
      apply hsmall f hc q.property
      have hh := hCB hq
      exact (by simpa [Metric.mem_closedBall, dist_comm] using hh :
        dist x q.val ≤ δ / 2).trans (by linarith)
    · change closure (interior (Subtype.val ⁻¹' C : Set P)) = Subtype.val ⁻¹' C
      rw [hCpre]
      simpa only [hB.interior_eq] using (closure_interior_idem (s := B))
    · refine ⟨Metric.ball x (δ / 2), Metric.isOpen_ball,
        by simpa using half_pos hδ, ?_⟩
      intro y hy
      exact ⟨⟨y, hy.1⟩, subset_closure hy.2, rfl⟩
  choose C hCne hCcompact hCsmall hCreg hCnbhd using hseed T.symm H.unstable_contraction
  choose D hDne hDcompact hDsmall hDreg hDnbhd using hseed T H.stable_contraction
  let A (x : X) := manningBowenBracketImage H.bracket (C x) (D x)
  have hCγ (x : X) : C x ⊆ manningBowenUnstablePlaque T γ x :=
    (hCsmall x).trans (hmono T.symm (by linarith) x)
  have hDγ (x : X) : D x ⊆ manningBowenStablePlaque T γ x :=
    (hDsmall x).trans (hmono T (by linarith) x)
  have hpairs (x : X) (c : X) (hc : c ∈ C x) (d : X) (hd : d ∈ D x) :
      dist c d < ε := by
    have hxc := hzero T.symm (hCsmall x hc)
    have hxd := hzero T (hDsmall x hd)
    have hcd := dist_triangle c x d
    rw [dist_comm c x] at hcd
    linarith
  have hAnbhd (x : X) : x ∈ interior (A x) := by
    obtain ⟨U, hUopen, hxU, hUC⟩ := hCnbhd x
    obtain ⟨V, hVopen, hxV, hVD⟩ := hDnbhd x
    let Cu := manningBowenUnstablePlaque T γ x ∩ U
    let Dv := manningBowenStablePlaque T γ x ∩ V
    have hCu : Cu ⊆ C x := hUC
    have hDv : Dv ⊆ D x := hVD
    have hCuopen : IsOpen (Subtype.val ⁻¹' Cu : Set (manningBowenUnstablePlaque T γ x)) := by
      simpa [Cu] using hUopen.preimage
        (continuous_subtype_val : Continuous (Subtype.val : manningBowenUnstablePlaque T γ x → X))
    have hDvopen : IsOpen (Subtype.val ⁻¹' Dv : Set (manningBowenStablePlaque T γ x)) := by
      simpa [Dv] using hVopen.preimage
        (continuous_subtype_val : Continuous (Subtype.val : manningBowenStablePlaque T γ x → X))
    have hprod := H.local_product x Cu Dv inter_subset_left inter_subset_left hCuopen hDvopen
      (hCu.trans ((hCsmall x).trans (hmono T.symm hδr.le x)))
      (hDv.trans ((hDsmall x).trans (hmono T hδr.le x)))
    apply mem_interior.mpr
    refine ⟨manningBowenBracketImage H.bracket Cu Dv, ?_, hprod.1, ?_⟩
    · rintro z ⟨p, hpC, hpD, hpz⟩
      exact ⟨p, hCu hpC, hDv hpD, hpz⟩
    · exact ⟨⟨(x, x), by simpa [manningBowenPairDomain] using H.epsilon_pos⟩,
        ⟨hself T.symm H.gamma_pos.le x, hxU⟩,
        ⟨hself T H.gamma_pos.le x, hxV⟩, hdiag x⟩
  have hAcompact (x : X) : IsCompact (A x) := by
    let B : C x × D x → manningBowenPairDomain (X := X) ε := fun p ↦
      ⟨(p.1.val, p.2.val), hpairs x p.1.val p.1.property p.2.val p.2.property⟩
    have hB : Continuous B :=
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    have : CompactSpace (C x) := isCompact_iff_compactSpace.mp (hCcompact x)
    have : CompactSpace (D x) := isCompact_iff_compactSpace.mp (hDcompact x)
    have heq : A x = (H.bracket ∘ B) '' univ := by
      ext z
      constructor
      · rintro ⟨p, hpC, hpD, hpz⟩
        exact ⟨(⟨p.val.1, hpC⟩, ⟨p.val.2, hpD⟩), trivial, hpz⟩
      · rintro ⟨p, _, hpz⟩
        exact ⟨B p, p.1.property, p.2.property, hpz⟩
    rw [heq]
    exact isCompact_univ.image (H.bracket_continuous.comp hB)
  have hAdiam (x : X) : Metric.diam (A x) < α / 2 := by
    have hAball : A x ⊆ Metric.closedBall x (3 * α / 16) := by
      rintro z ⟨p, hpC, hpD, rfl⟩
      have hc := hzero T.symm (hCsmall x hpC)
      have hd := hzero T (hDsmall x hpD)
      have hdist : dist p.val.1 p.val.2 ≤ ν := by
        have hh := dist_triangle p.val.1 x p.val.2
        rw [dist_comm p.val.1 x] at hh
        linarith
      have hh := (hνdisp p hdist).1
      have hx := dist_triangle x p.val.1 (H.bracket p)
      rw [Metric.mem_closedBall, dist_comm]
      linarith
    exact (Metric.diam_le_of_subset_closedBall (by positivity) hAball).trans_lt (by linarith)
  have hAsmall (x : X) (p : manningBowenPairDomain (X := X) ε)
      (hc : p.val.1 ∈ C x) (hd : p.val.2 ∈ D x) :
      H.bracket p ∈ manningBowenStablePlaque T (α / 8) p.val.1 ∩
        manningBowenUnstablePlaque T (α / 8) p.val.2 := by
    have hxc := hzero T.symm (hCsmall x hc)
    have hxd := hzero T (hDsmall x hd)
    have hh := dist_triangle p.val.1 x p.val.2
    rw [dist_comm p.val.1 x] at hh
    have hνp : dist p.val.1 p.val.2 ≤ ν := by linarith
    exact ⟨hsmall T H.stable_contraction (hmem p).1 (hνdisp p hνp).1.le,
      hsmall T.symm H.unstable_contraction (hmem p).2 (hνdisp p hνp).2.le⟩
  have hAbracket (x : X) (p : manningBowenPairDomain (X := X) ε)
      (ha : p.val.1 ∈ A x) (hb : p.val.2 ∈ A x) : H.bracket p ∈ A x := by
    have hpdist : dist p.val.1 p.val.2 ≤ σ :=
      ((Metric.dist_le_diam_of_mem (hAcompact x).isBounded ha hb).trans
        (hAdiam x).le).trans (by linarith)
    have houter := hσsmall p hpdist
    obtain ⟨q, hqC, hqD, hqa⟩ := ha
    obtain ⟨r, hrC, hrD, hrb⟩ := hb
    let w : manningBowenPairDomain (X := X) ε :=
      ⟨(q.val.1, r.val.2), hpairs x q.val.1 hqC r.val.2 hrD⟩
    have hq := hAsmall x q hqC hqD
    have hr := hAsmall x r hrC hrD
    have hqw : H.bracket p ∈ manningBowenStablePlaque T γ q.val.1 := by
      intro n
      have h1 := hq.1 n
      have h2 := houter.1 n
      rw [hqa] at h1
      have hh := dist_triangle ((T : X → X)^[n] q.val.1)
        ((T : X → X)^[n] p.val.1) ((T : X → X)^[n] (H.bracket p))
      linarith
    have hrw : H.bracket p ∈ manningBowenUnstablePlaque T γ r.val.2 := by
      intro n
      have h1 := hr.2 n
      have h2 := houter.2 n
      rw [hrb] at h1
      have hh := dist_triangle ((T.symm : X → X)^[n] r.val.2)
        ((T.symm : X → X)^[n] p.val.2) ((T.symm : X → X)^[n] (H.bracket p))
      linarith
    have heq : H.bracket p = H.bracket w := by
      apply mem_singleton_iff.mp
      rw [← H.bracket_intersection]
      exact ⟨hqw, hrw⟩
    exact ⟨w, hqC, hrD, heq.symm⟩
  have hAregular (x : X) : A x = closure (interior (A x)) := by
    let P := manningBowenUnstablePlaque T γ x
    let Q := manningBowenStablePlaque T γ x
    let Cp : Set P := Subtype.val ⁻¹' C x
    let Dq : Set Q := Subtype.val ⁻¹' D x
    let U : Set X := Subtype.val '' interior Cp
    let V : Set X := Subtype.val '' interior Dq
    have hUC : U ⊆ C x := by
      rintro z ⟨p, hp, rfl⟩
      exact (show p ∈ Cp from interior_subset hp)
    have hVD : V ⊆ D x := by
      rintro z ⟨q, hq, rfl⟩
      exact (show q ∈ Dq from interior_subset hq)
    have hUγ : U ⊆ P := hUC.trans (hCγ x)
    have hVγ : V ⊆ Q := hVD.trans (hDγ x)
    have hUo : IsOpen (Subtype.val ⁻¹' U : Set P) := by
      dsimp [U]
      rw [Subtype.val_injective.preimage_image]
      exact isOpen_interior
    have hVo : IsOpen (Subtype.val ⁻¹' V : Set Q) := by
      dsimp [V]
      rw [Subtype.val_injective.preimage_image]
      exact isOpen_interior
    have hOpen := (H.local_product x U V hUγ hVγ hUo hVo
      (hUC.trans ((hCsmall x).trans (hmono T.symm hδr.le x)))
      (hVD.trans ((hDsmall x).trans (hmono T hδr.le x)))).1
    have hOsub : manningBowenBracketImage H.bracket U V ⊆ A x := by
      rintro z ⟨p, hp, hq, hz⟩
      exact ⟨p, hUC hp, hVD hq, hz⟩
    have hOint := interior_maximal hOsub hOpen
    let S : Set (P × Q) := Cp ×ˢ Dq
    let B : Set (P × Q) := interior Cp ×ˢ interior Dq
    have hBcl : closure B = S := by
      dsimp [B, S]
      rw [closure_prod_eq]
      exact congrArg₂ (· ×ˢ ·) (hCreg x) (hDreg x)
    let g : P × Q → X := fun p ↦
      if hp : dist p.1.val p.2.val < ε then H.bracket ⟨(p.1.val, p.2.val), hp⟩ else x
    have hgc : ContinuousOn g S := by
      rw [continuousOn_iff_continuous_domRestrict]
      let bmap : S → manningBowenPairDomain (X := X) ε := fun p ↦
        ⟨(p.val.1.val, p.val.2.val), hpairs x _ p.property.1 _ p.property.2⟩
      have hbmap : Continuous bmap :=
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
      apply (H.bracket_continuous.comp hbmap).congr
      intro p
      simp only [Function.comp_apply, domRestrict_apply, g,
        dite_eq_left (hpairs x _ p.property.1 _ p.property.2), bmap]
    have hgB : MapsTo g B (interior (A x)) := by
      intro p hp
      have hc : p.1.val ∈ C x := (show p.1 ∈ Cp from interior_subset hp.1)
      have hd : p.2.val ∈ D x := (show p.2 ∈ Dq from interior_subset hp.2)
      apply hOint
      refine ⟨⟨(p.1.val, p.2.val), hpairs x _ hc _ hd⟩,
        ⟨p.1, hp.1, rfl⟩, ⟨p.2, hp.2, rfl⟩, ?_⟩
      simp only [g, dite_eq_left (hpairs x _ hc _ hd)]
    have hgcl := hgB.closure_of_continuousOn (hBcl.symm ▸ hgc)
    apply Subset.antisymm
    · rintro z ⟨p, hc, hd, rfl⟩
      let q : P × Q := (⟨p.val.1, hCγ x hc⟩, ⟨p.val.2, hDγ x hd⟩)
      have hq : q ∈ closure B := by rw [hBcl]; exact ⟨hc, hd⟩
      have hpdist : dist p.val.1 p.val.2 < ε := p.property
      simpa only [g, q, dite_eq_left hpdist, Subtype.coe_eta, Prod.mk.eta] using hgcl hq
    · exact closure_minimal interior_subset (hAcompact x).isClosed
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ interior (A x))
    (fun _ ↦ isOpen_interior) (fun x _ ↦ mem_iUnion.mpr ⟨x, hAnbhd x⟩)
  have hIne : I.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y, hyI, _⟩ := mem_iUnion₂.mp (hI (mem_univ x))
    exact ⟨y, hyI⟩
  have hIcover : (⋃ i : I, interior (A i.val)) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y, hyI, hy⟩ := mem_iUnion₂.mp (hI (mem_univ x))
    exact mem_iUnion.mpr ⟨⟨y, hyI⟩, hy⟩
  obtain ⟨ell, hell, hLeb⟩ := CompactSpace.lebesgue_number_lemma
    (fun i : I ↦ interior (A i.val)) (fun _ ↦ isOpen_interior) hIcover
  let b : ℝ := ell / 4
  have hb : 0 < b := by dsimp [b]; linarith
  have hselection (x : X) : ∃ i : I, Metric.closedBall x b ⊆ interior (A i.val) := by
    apply hLeb
    · exact ⟨x, by simp [hb.le]⟩
    · exact (Metric.diam_le_of_subset_closedBall hb.le (Subset.refl _)).trans (by
        dsimp [b]; linarith)
  choose F hF using hselection
  have hselected (x : X) : x ∈ A (F x).val :=
    interior_subset (hF x (by simp [hb.le]))
  obtain ⟨τ, hτ, hτε, hτmod⟩ := hmod (min b (σ / 4))
    (lt_min hb (by linarith))
  obtain ⟨a, ha, habound⟩ := exists_between
    (lt_min hτ (lt_min (by linarith : 0 < γ / 4) (by linarith : 0 < σ / 4)))
  have haτ : a < τ := (lt_min_iff.mp habound).1
  have haγ : a < γ / 4 := (lt_min_iff.mp (lt_min_iff.mp habound).2).1
  have haσ : a < σ / 4 := (lt_min_iff.mp (lt_min_iff.mp habound).2).2
  have hsaturation (x z : X)
      (hz : z ∈ A (F x).val ∩ manningBowenUnstablePlaque T γ x) :
      manningBowenStablePlaque T a z ⊆ A (F x).val := by
    intro w hw
    have hxz : dist x z < α / 2 :=
      (Metric.dist_le_diam_of_mem (hAcompact (F x).val).isBounded
        (hselected x) hz.1).trans_lt (hAdiam (F x).val)
    have hzw : dist z w ≤ a := hzero T hw
    have hxw : dist x w < σ := by
      have hh := dist_triangle x z w
      linarith
    have hxzε : dist x z < ε := by linarith
    have hxwε : dist x w < ε := hxw.trans (hσε.trans (by linarith [H.epsilon_pos]))
    let q : manningBowenPairDomain (X := X) ε := ⟨(x, w), hxwε⟩
    have hbase : H.bracket ⟨(x, z), hxzε⟩ = x := by
      symm
      apply mem_singleton_iff.mp
      rw [← H.bracket_intersection]
      refine ⟨hself T H.gamma_pos.le x, ?_⟩
      intro n
      simpa only [dist_comm] using hz.2 n
    have hqx : dist (H.bracket q) x < min b (σ / 4) := by
      have hh := hτmod q ⟨(x, z), hxzε⟩
        (by dsimp [q]; linarith)
        (by dsimp; linarith)
        (by simpa [q, Prod.dist_eq, dist_comm] using hzw.trans haτ.le)
      simpa only [hbase] using hh
    have hqA : H.bracket q ∈ A (F x).val :=
      interior_subset (hF x ((hqx.trans_le (min_le_left _ _)).le))
    have hzq : dist z (H.bracket q) < σ := by
      have hh := dist_triangle z x (H.bracket q)
      rw [dist_comm z x, dist_comm x (H.bracket q)] at hh
      have hqσ := hqx.trans_le (min_le_right _ _)
      linarith
    let r : manningBowenPairDomain (X := X) ε :=
      ⟨(z, H.bracket q), hzq.trans (hσε.trans (by linarith [H.epsilon_pos]))⟩
    have hqsmall := hσsmall q hxw.le
    have hrsmall := hσsmall r hzq.le
    have hrw : H.bracket r = w := by
      have hzwε : dist z w < ε := by linarith
      have hww : H.bracket ⟨(z, w), hzwε⟩ = w := by
        symm
        apply mem_singleton_iff.mp
        rw [← H.bracket_intersection]
        exact ⟨hmono T (by linarith) z hw, hself T.symm H.gamma_pos.le w⟩
      rw [← hww]
      apply mem_singleton_iff.mp
      rw [← H.bracket_intersection]
      refine ⟨hmono T (by linarith [H.gamma_pos]) z hrsmall.1, ?_⟩
      intro n
      have h1 := hqsmall.2 n
      have h2 := hrsmall.2 n
      have hh := dist_triangle ((T.symm : X → X)^[n] w)
        ((T.symm : X → X)^[n] (H.bracket q))
        ((T.symm : X → X)^[n] (H.bracket r))
      dsimp [q, r] at h1 h2
      linarith [H.gamma_pos]
    rw [← hrw]
    exact hAbracket (F x).val r hz.1 hqA
  have husaturation (x y : X)
      (hy : y ∈ A (F x).val ∩ manningBowenStablePlaque T γ x) :
      manningBowenUnstablePlaque T a y ⊆ A (F x).val := by
    intro v hv
    have hxy : dist x y < α / 2 :=
      (Metric.dist_le_diam_of_mem (hAcompact (F x).val).isBounded
        (hselected x) hy.1).trans_lt (hAdiam (F x).val)
    have hyv : dist y v ≤ a := hzero T.symm hv
    have hvx : dist v x < σ := by
      have hh := dist_triangle x y v
      rw [dist_comm v x]
      linarith
    have hyxε : dist y x < ε := by rw [dist_comm]; linarith
    have hvxε : dist v x < ε := hvx.trans (hσε.trans (by linarith [H.epsilon_pos]))
    let q : manningBowenPairDomain (X := X) ε := ⟨(v, x), hvxε⟩
    have hbase : H.bracket ⟨(y, x), hyxε⟩ = x := by
      symm
      apply mem_singleton_iff.mp
      rw [← H.bracket_intersection]
      refine ⟨?_, hself T.symm H.gamma_pos.le x⟩
      intro n
      simpa only [dist_comm] using hy.2 n
    have hqx : dist (H.bracket q) x < min b (σ / 4) := by
      have hh := hτmod q ⟨(y, x), hyxε⟩
        (by dsimp [q]; linarith)
        (by dsimp; rw [dist_comm]; linarith)
        (by simpa [q, Prod.dist_eq, dist_comm] using hyv.trans haτ.le)
      simpa only [hbase] using hh
    have hqA : H.bracket q ∈ A (F x).val :=
      interior_subset (hF x ((hqx.trans_le (min_le_left _ _)).le))
    have hqy : dist (H.bracket q) y < σ := by
      have hh := dist_triangle (H.bracket q) x y
      have hqσ := hqx.trans_le (min_le_right _ _)
      linarith
    let r : manningBowenPairDomain (X := X) ε :=
      ⟨(H.bracket q, y), hqy.trans (hσε.trans (by linarith [H.epsilon_pos]))⟩
    have hqsmall := hσsmall q hvx.le
    have hrsmall := hσsmall r hqy.le
    have hrv : H.bracket r = v := by
      have hvyε : dist v y < ε := by rw [dist_comm]; linarith
      have hvv : H.bracket ⟨(v, y), hvyε⟩ = v := by
        symm
        apply mem_singleton_iff.mp
        rw [← H.bracket_intersection]
        exact ⟨hself T H.gamma_pos.le v, hmono T.symm (by linarith) y hv⟩
      rw [← hvv]
      apply mem_singleton_iff.mp
      rw [← H.bracket_intersection]
      refine ⟨?_, hmono T.symm (by linarith [H.gamma_pos]) y hrsmall.2⟩
      intro n
      have h1 := hqsmall.1 n
      have h2 := hrsmall.1 n
      have hh := dist_triangle ((T : X → X)^[n] v)
        ((T : X → X)^[n] (H.bracket q)) ((T : X → X)^[n] (H.bracket r))
      dsimp [q, r] at h1 h2
      linarith [H.gamma_pos]
    rw [← hrv]
    exact hAbracket (F x).val r hqA hy.1
  let E : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hcard : 0 < Fintype.card I := Fintype.card_pos_iff.mpr hIne.to_subtype
  refine ⟨δ, α, hδ, hδα, (lt_min_iff.mp hαbound).1, hαγ, hαε, ?_⟩
  refine ⟨{
    count := Fintype.card I
    count_pos := hcard
    center := fun i ↦ (E.symm i).val
    unstableFactor := fun i ↦ C (E.symm i).val
    stableFactor := fun i ↦ D (E.symm i).val
    rectangle := fun i ↦ A (E.symm i).val
    saturationRadius := a
    saturationRadius_pos := ha
    select := fun x ↦ E (F x)
    unstableFactor_nonempty := fun i ↦ hCne _
    stableFactor_nonempty := fun i ↦ hDne _
    unstableFactor_compact := fun i ↦ hCcompact _
    stableFactor_compact := fun i ↦ hDcompact _
    unstableFactor_subset := fun i ↦ by
      simpa [manningBowenStablePlaque, manningBowenUnstablePlaque, dist_comm] using
        hCsmall (E.symm i).val
    stableFactor_subset := fun i ↦ hDsmall _
    unstableFactor_regular := fun i ↦ hCreg _
    stableFactor_regular := fun i ↦ hDreg _
    unstableFactor_neighborhood := fun i ↦ hCnbhd _
    stableFactor_neighborhood := fun i ↦ hDnbhd _
    factor_brackets_defined := fun i c hc d hd ↦ hpairs _ c hc d hd
    rectangle_eq := fun i ↦ rfl
    rectangle_nonempty := fun i ↦ ⟨_, interior_subset (hAnbhd _)⟩
    rectangle_compact := fun i ↦ hAcompact _
    rectangle_regular := fun i ↦ hAregular _
    center_interior := fun i ↦ hAnbhd _
    rectangle_diam := fun i ↦ hAdiam _
    interior_cover := fun x ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hIcover ▸ mem_univ x)
      exact ⟨E i, by simpa using hi⟩
    rectangle_brackets_defined := fun i c hc d hd ↦
      (Metric.dist_le_diam_of_mem (hAcompact _).isBounded hc hd).trans_lt
        ((hAdiam _).trans (by linarith))
    rectangle_bracket_closed := fun i p hp hq ↦ hAbracket _ p hp hq
    unstable_transverse_defined := fun i y hy c hc d hd ↦ by
      have heq : d = y := mem_singleton_iff.mp hd
      subst d
      exact (htransverse_u (E.symm i).val c y (hCsmall _ hc) hy).choose
    unstable_transverse_margin := fun i y hy z hz ↦ by
      obtain ⟨p, hc, hd, rfl⟩ := hz
      have heq : p.val.2 = y := mem_singleton_iff.mp hd
      obtain ⟨hp, hpl⟩ := htransverse_u (E.symm i).val p.val.1 p.val.2
        (hCsmall _ hc) (heq.symm ▸ hy)
      simpa only [Prod.mk.eta, Subtype.coe_eta] using (heq ▸ hpl)
    stable_transverse_defined := fun i y hy d hd c hc ↦ by
      have heq : d = y := mem_singleton_iff.mp hd
      subst d
      exact (htransverse_s (E.symm i).val y c hy (hDsmall _ hc)).choose
    stable_transverse_margin := fun i y hy z hz ↦ by
      obtain ⟨p, hd, hc, rfl⟩ := hz
      have heq : p.val.1 = y := mem_singleton_iff.mp hd
      obtain ⟨hp, hpl⟩ := htransverse_s (E.symm i).val p.val.1 p.val.2
        (heq.symm ▸ hy) (hDsmall _ hc)
      simpa only [Prod.mk.eta, Subtype.coe_eta] using (heq ▸ hpl)
    selected_membership := fun x ↦ by simpa using hselected x
    selected_stable_saturation := fun x z hz ↦ by simpa using hsaturation x z (by simpa using hz)
    selected_unstable_saturation := fun x y hy ↦ by simpa using husaturation x y (by simpa using hy) }⟩


end HolomorphicAnosov
