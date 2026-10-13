import HolomorphicAnosov.Analysis.Complex.QCRegularToGeometricModulusDistortion
import HolomorphicAnosov.Analysis.Complex.QCGeometricModulusLimit
import HolomorphicAnosov.Analysis.Complex.QCGeometricOneConformal

/-!
# Holomorphic limits of asymptotically conformal C¹ planar diffeomorphisms

Node: `analysis.asymptotically_conformal_c1_homeomorphism_limit`.
Source: Ghys, *Holomorphic Anosov systems*, Proposition 2.2, printed p. 590;
Lehto–Virtanen, *Quasiconformal Mappings in the Plane*, second edition (1973),
Chapter I, Theorems 3.1 (pp. 18–19), 5.2 (p. 29), and 5.1 (pp. 28–29).

Open partial homeomorphisms encode homeomorphisms between open planar domains;
their values outside the source or target are irrelevant. The two `ContDiffOn`
hypotheses encode C¹ regularity of both original directions. The pointwise
continuous-linear equivalence is the real derivative, and its positive determinant
encodes sense preservation at every regular point (Lehto–Virtanen I.§1.6, p. 10).
The limit's orientation is topological: on each positively parametrized circle
whose closed disk lies in the source, the normalized image about the image of the
center has a continuous argument lift increasing by 2π between the endpoints.
This is positive boundary orientation in Lehto–Virtanen I.§1.4, p. 8. On a connected
plane domain it is equivalent to sense preservation by I.§1.5, p. 9; no derivative
of the limit is assumed. The complex exponential gives the literal positive
circle parametrization. All norms are the original Euclidean complex norm.
-/

namespace HolomorphicAnosov

open Set Filter _root_.Topology
open scoped ContDiff

/-- The locally uniform orientation-preserving homeomorphic limit of real C¹
planar diffeomorphisms whose Euclidean directional distortion tends to one is
holomorphic. Target domains may vary and no derivative convergence is assumed.

Natural-language statement: Let U⊂ℂ be a nonempty connected open set, and for n∈ℕ let g_n:U→V_n be an orientation-preserving real C¹ diffeomorphism onto a planar open set V_n, with invertible real derivative at every point. Let K_n≥1 tend to 1 and suppose ‖Dg_n(z)v‖≤K_n‖Dg_n(z)w‖ for every z∈U and every pair of Euclidean unit vectors v,w∈ℂ. If g_n converges locally uniformly on U to an orientation-preserving homeomorphism g:U→V onto an open set V, then g is holomorphic on U. The target sets V_n may vary with n; no uniform derivative convergence or common image domain is assumed.

Source: Ghys, Holomorphic Anosov systems (1995), Proposition2.2 printedp590, final quasiconformal-limit step; published justification: Olli Lehto and K.I.Virtanen, Quasiconformal Mappings in the Plane, second edition, Springer1973, ChapterI Theorem3.1 pp18–19 (regular derivative ratio implies geometric modulus distortion), Rengel inequality/equality pp22–23 and Lemma4.2p25, Lemma4.3p26 and Lemma4.4p27 (complete inside modulus continuity and analytic inside approximation), Theorem5.2p29 (locally uniform homeomorphic limit on arbitrary fixed source with varying images), and Theorem5.1pp28–29 (geometric1QC implies conformal). The boundary-touching subrectangle passage uses the same inside approximation argument of I.§5.3p30. Obtained original second-edition1973 PDF has276pages; printed18–19,22–23,25–30 are physical PDF30–31,34–35,37–42. Local original: literature/Quasiconformal mappings in the plane (Lehto, Olli, Virtanen, K. I., joint author) (z-library.sk, 1lib.sk, z-lib.sk).pdf; extracted text: literature/Lehto-Virtanen-Quasiconformal-Mappings-in-the-Plane-supplied.txt.

Complete natural-language proof:

1. Use the geometric convention of Lehto–Virtanen I.§§2.3,3.1–3.2: a quadrilateral P is a bounded
Jordan region with four distinct positively cyclic corner marks; the a-sides are the bottom/top
pair and the b-sides the right/left pair. The registered marked rectangle theorem supplies a
holomorphic bijection F:R_(a,b)→P and its same-map closed-rectangle extension with those side
labels. Its modulus M(P)=a/b is positive and independent of the chosen model. Normalize by a
positive similarity to R_M={0<x<M(P),0<y<1}. A positively marked homeomorphism carries those
labels to its image quadrilateral. Cyclically moving the first corner changes the modulus to its
reciprocal: rotating and rescaling a canonical rectangle gives the exchanged marked model, and
model uniqueness gives M(P with exchanged side pairs)=1/M(P). Conformal changes preserve marked
modulus by composing their actual same-map boundary extensions. In this proof a sense-preserving
homeomorphism f on an open domain is geometrically K-quasiconformal when M(f(P))≤K M(P) for every
such P with closure compactly contained in that domain. Applying the inequality to the cyclically
relabeled P also gives M(f(P))≥M(P)/K. This definition is used only inside the proof; it does not
replace the current analytic statement.

Source: LV1973 I.§2.3–2.4 pp.14–15; I.§3.1–3.2 pp.16–17

2. Follow Grötzsch’s inequality, I.Theorem3.1, for a C¹ diffeomorphism f with directional stretch
ratio at most K. For a quadrilateral P compactly inside its source, use its canonical model and
the model of f(P) to obtain W:R_M→R_Mprime, extending continuously with matched sides and corners.
The model maps and their inverses are holomorphic with nonzero interior complex derivatives; the
inverse theorem and derivative-closure theorem supply the interior differentiability and
continuous derivative needed for the real chain rule. Apply the registered
HasFDerivAt.restrictScalars in the direction complex→real to these complex derivatives on the SAME
complex normed spaces, and then HasFDerivAt.comp over ℝ twice for the canonical conjugation. A
complex derivative v↦c v restricts to that literal real-linear similarity; c≠0 follows from the
inverse theorem. The derivative used for W is exactly the resulting real composition, not a
reverse restriction-of-scalars inference. At each interior point their derivatives are real
similarities, so composition preserves the directional ratio. For any nonsingular real-linear
planar map T, write T(v)=a v+b conjugate(v). Maximum/minimum unit-vector stretches are L=|a|+|b|
and l=||a|−|b||; triangle inequalities and aligned/opposed phases give these extrema. Direct real-
coordinate determinant calculation gives |det T|=||a|²−|b|²|=L l. Thus L≤K l gives |det
DW|≥|W_x|²/K. This unsigned identity is sufficient for the area calculation; the given sense-
preserving hypothesis is used to carry the positive boundary marking. No Jacobian-sign or
differentiability assertion about the limit is made.

Source: LV1973 I.§3.3 p.17; I.Theorem3.1 and (3.3)–(3.4) pp.18–19

3. Apply the exact image-Jacobian lower-integral formula to the measurable OPEN rectangle R_M, the
injective W and its actual derivative at every interior point, with image density 1. This gives
∫_(R_M)|det DW|=area(R_Mprime)=Mprime, hence ∫_(R_M)|W_x|²≤K Mprime<∞. The continuous interior
derivative density is measurable on this open set by the registered continuous-on measurability
theorem; no boundary derivative is supplied. Transport complex volume to real product volume,
restrict to (0,M)×(0,1), then apply the registered measure-preserving swap from the product of
these two finite (hence s-finite) restricted Lebesgue measures to their REVERSED product. Apply
nonnegative Tonelli to the swapped density (y,x)↦|W_x(x+iy)|², so y is the outer variable and x
the inner variable. This explicitly matches the forward order of the named lintegral_prod theorem.
For almost every y∈(0,1), E(y)=∫_0^M|W_x(x+iy)|² dx is finite. Holder with exponents 2,2 against
the constant 1 gives L(y)=∫_0^M|W_x(x+iy)| dx finite and L(y)²≤M E(y). Extend the real speed
density by 0 at the two endpoints (and arbitrarily outside the interval); its actual finite
interior speed agrees with the derivative norm there. Holder supplied IntegrableOn on (0,M). The
registered intervalIntegrable_iff_integrableOn_Ioo_of_le converts this to IntervalIntegrable on
[0,M], because M>0, real Lebesgue singletons are null and the chosen real endpoint values are
finite. The actual horizontal function x↦W(x+iy) is continuous on [0,M] by the closure map and
differentiable on (0,M), with its derivative norm bounded by exactly this speed density. The
registered norm-sub integral theorem therefore gives |W(M+iy)−W(iy)|≤L(y), without endpoint
differentiability. The two endpoints lie on opposite vertical sides of R_Mprime, so Mprime≤L(y).
Integrating E(y)≥Mprime²/M over y∈(0,1) yields K Mprime≥Mprime²/M. Since M,Mprime>0, Mprime≤K M.
This is exactly the written proof of Theorem3.1, with its p.18 footnote implemented by Tonelli and
the open-interval derivative estimate, rather than by differentiating a boundary extension.

Source: LV1973 I.Theorem3.1 pp.18–19, including footnote5 p.18

4. Write out the Rengel estimate used by both closure and rigidity. For a bounded quadrilateral P
let s_a(P) and s_b(P) be the infimal Euclidean lengths of locally regular interior arcs joining
the a-sides and b-sides, respectively, with endpoints on those closed sides; a curve with infinite
length causes no problem. Let H:R_M→P be the inverse canonical map with its same-map closure
extension. The image-Jacobian formula and the complex derivative identity |det DH|=|Hprime|² give
area(P)=∫_(R_M)|Hprime|². Tonelli makes the vertical energy finite for almost every u∈(0,M). On
such a slice Holder gives square-integrable⇒IntegrableOn speed on (0,1). Extend the real speed by
finite endpoint values 0 and use the registered open-interval/interval-integrability equivalence
for Lebesgue measure to obtain IntervalIntegrable on [0,1], with no boundary derivative
assumption. On this slice the vertical image arc has Euclidean length at most
L(u)=∫_0^1|Hprime(u+iv)|dv, hence L(u)≥s_a(P); its endpoints are on the a-sides by the closure
map. Explicitly, apply the registered norm-sub integral estimate to each segment of any finite
partition on a compact interior subinterval and sum: every such polygonal chord sum is at most the
speed integral there. Taking the supremum over partitions and then over compact interior
subintervals gives full open-arc length at most L(u). This inequality suffices and requires no
boundary derivative or additional converse arclength formula. Thus
∫_0^1|Hprime(u+iv)|²dv≥L(u)²≥s_a(P)². Integration gives M(P) s_a(P)²≤area(P). Apply the identical
argument after exchanging marked side pairs to obtain s_b(P)²≤M(P) area(P). Whenever the displayed
denominators are positive, this is s_b(P)²/area(P)≤M(P)≤area(P)/s_a(P)². Only the canonical
analytic arcs are needed; the general extremal-length function classes in I.§4.2 are not assumed
as extra input.

Source: LV1973 I.§4.1–4.3 pp.20–23, especially Rengel’s inequality p.22 and its inverse-canonical-map calculation p.23

5. Keep the equality case of that source calculation explicit. If area(P)=M(P) s_a(P)², the two
nonnegative differences in the preceding integrated estimate vanish for almost every u.
Consequently E(u)=L(u)²=s_a(P)². Equality in this particular Cauchy–Schwarz estimate follows
directly from ∫_0^1(|Hprime(u+iv)|−L(u))²dv=E(u)−L(u)²=0: continuity inside the slice gives
|Hprime|=L(u) for every interior v on every such good slice. The second equality L(u)=s_a(P) makes
this norm the SAME constant across good u. Good u have full measure and hence are dense; interior
continuity extends |Hprime|=s_a(P) to all R_M. This constant is nonzero, since Hprime has no
zeros. Put h=Hprime, holomorphic by the derivative-closure theorem. Differentiate |h|² in the two
real coordinate directions: its constant value gives Re(hprime conjugate(h))=0 and Im(hprime
conjugate(h))=0. Therefore hprime=0. The registered zero-derivative constancy theorem, on the open
connected rectangle, makes h a nonzero constant c; apply the same theorem to H(z)−c z to obtain
H(z)=c z+d. Its image is a Euclidean rectangle, with the marked sides corresponding to that
similarity. Conversely a rectangle gives equality. The exchanged-side lower equality is the same
calculation with exchanged markings. This supplies the necessity part on source p.23 and does not
infer geometric 1-quasiconformal rigidity from a theorem already assuming holomorphicity.

Source: LV1973 I.§4.3 pp.22–23, written necessity proof for equality in Rengel’s inequality

6. For the finite two-piece case of source Lemma4.2, let P₁,P₂ have disjoint interiors inside the
canonical rectangle R_M, closures inside its closure and each of their two a-sides contained in
the corresponding horizontal side of R_M. Every joining arc has length at least 1, so s_a(P_i)≥1.
Rengel gives M(P_i)≤area(P_i), hence M(P₁)+M(P₂)≤area(P₁)+area(P₂)≤M. If the module sum equals M,
both inequalities for each P_i are equalities; the preceding equality argument makes each P_i a
Euclidean rectangle. Its a-sides lie on the two horizontal sides, so it is an axis-parallel full-
height rectangle. This is the exact superadditivity/equality calculation of I.Lemma4.2, restricted
to the finite case used below.

Source: LV1973 I.Lemma4.2 p.25

7. Follow I.Lemma4.3 to prove only the inside continuity needed here. Suppose P_j⊂P and every
point of each marked side of P_j eventually has distance <ε from the corresponding side of P, for
every ε>0. No nesting or reverse Hausdorff bound is required. Apply the canonical map of P,
including its continuous closed-domain extension. Uniform continuity on the compact closure,
applied as a globally continuous map on the closure SUBTYPE, sends the four labeled sides of the
images S_j into strips of width ε along the corresponding sides of R_M. All S_j lie in R_M and
have area at most M. For 0<ε<min(1/2,M/2), every a-side joining arc has length at least 1−2ε, and
every b-side joining arc at least M−2ε. The preceding Rengel inequalities imply
(M−2ε)²/M≤M(S_j)≤M/(1−2ε)². Conformal invariance gives M(S_j)=M(P_j); letting ε↓0 proves
M(P_j)→M(P). All regions in the application are bounded, so Euclidean and spherical side-distance
convergence agree. This is the full written squeeze (4.15); the generalized theorem in I.§4.9 and
its external Rado theorem are unnecessary.

Source: LV1973 I.Lemma4.3 p.26, (4.14)–(4.15)

8. Follow I.Lemma4.4 using an actual closed-disk map, not extra data silently attached to the
marked rectangle model. The Jordan-region theorem makes a quadrilateral P a bounded simply
connected nonempty open region. Its bounded Riemann map supplies φ:D→P, and the same-map
Caratheodory theorem extends precisely that φ to a homeomorphism Φ:closed D→closure P. Pull back
the four corner marks to distinct positively cyclic ζ₁,…,ζ₄∈S¹. For j≥2 set r_j=1−1/j and
P_j=φ({|z|<r_j}), with marked corners φ(r_j ζ_i) and the corresponding circular subarcs. Each
closed smaller disk lies compactly inside D; injectivity, holomorphicity and nonzero derivative
show its boundary image is analytic in the source’s sense. Its image closure lies compactly inside
P. Uniform continuity of Φ on closed D gives sup_|ζ|=1 |φ(r_j ζ)−Φ(ζ)|→0. Thus every point of each
labeled side of P_j is close to the corresponding side of P, so P_j→P from inside. This gives the
exact source approximation, including the harmless exclusion of the degenerate r₁=0 term.

Source: LV1973 I.Lemma4.4 p.27; boundary correspondence I.§2.2 p.14

9. Now apply the written closure proof I.Theorem5.2, first for any fixed L>1. Since K_n→1, choose
N with K_n≤L for n≥N; the regular-to-geometric calculation proves these g_n are geometrically
L-quasiconformal on U. Fix any quadrilateral P with closure compactly contained in U and choose
its analytic inside approximations P_j from the previous step. For each fixed j, g(closure P_j) is
compactly inside g(P). Its positive distance from the complement of g(P), together with uniform
convergence on closure P, ensures g_n(closure P_j)⊂g(P) for all sufficiently large n. Choose a
strictly increasing n_j≥max(N,j) with this containment and sup_(closure P)|g_nj−g|≤1/j. For any
point z on a labeled side of P_j, choose q on the corresponding side of P with |z−q| tending
uniformly to zero. Then |g_nj(z)−g(q)|≤1/j+|g(z)−g(q)|→0 by uniform continuity of g on closure P.
Therefore g_nj(P_j) converges to g(P) FROM INSIDE, with the labels carried by the given
orientation-preserving homeomorphisms. The inside continuity calculation gives M(P_j)→M(P) and
M(g_nj(P_j))→M(g(P)). Pass to the limit in M(g_nj(P_j))≤L M(P_j) to get M(g(P))≤L M(P). Since P
was arbitrary, g is geometrically L-quasiconformal. This is the source’s diagonal subsequence
proof; it uses neither a common V_n nor convergence of derivatives or inverse derivatives.

Source: LV1973 I.Theorem5.2 p.29; Lemmas4.3–4.4 pp.26–27

10. Take L=1+1/m for each positive integer m in the preceding fixed-constant closure argument. For
every positively marked quadrilateral P compactly inside U, M(g(P))≤(1+1/m)M(P) for all m, hence
M(g(P))≤M(P). The cyclically relabeled P gives the reverse bound, so M(g(P))=M(P). The assumed
orientation-preserving homeomorphism g is therefore geometrically 1-quasiconformal. This
elementary specialization of the published fixed-K theorem preserves every current hypothesis; it
introduces no new analytic closure estimate.

Source: LV1973 I.Theorem5.2 p.29 specialized to every fixed L>1; geometric definition I.§3.1–3.2 pp.16–17

11. Finish by the written rectangle partition proof I.Theorem5.1. Around any point of U choose a
nondegenerate quadrilateral P with closure compactly inside U. Normalize P and g(P) to the
congruent canonical rectangle R_M, since their moduli are equal. Their actual closure maps and g
give W:closure R_M→closure R_M preserving the four corners/sides, geometrically 1-quasiconformal
in the interior. The module equality also applies to a subquadrilateral A whose interior lies in
R_M but whose closure touches its boundary: approximate A from inside as above, apply equality to
its compact interior approximations, and use closure uniform continuity and inside modulus
continuity for W(A_j)→W(A). This is the inside-approximation argument of I.§5.3, and avoids
treating boundary-touching rectangles as compactly inside R_M. For z₀=x₀+i y₀∈R_M split R_M by the
vertical segment x=x₀ into the left and right rectangles. Their image quadrilaterals have modules
x₀ and M−x₀, disjoint interiors, and a-sides on the horizontal sides of R_M. Their module sum is
M, so the preceding Lemma4.2 equality argument makes them full-height axis-parallel rectangles.
The left image contains the corner 0 and has width x₀, hence its other vertical side is x=x₀. In
particular Re W(z₀)=x₀. Repeat with the horizontal split y=y₀, exchanging marked side pairs and
rotating/rescaling the entire rectangle as in step1; the same argument gives Im W(z₀)=y₀. Thus W
is the identity. Undoing the two holomorphic canonical maps expresses g on P as their holomorphic
composition. Every point lies in such a P, so g is holomorphic on U. This proves the exact current
conclusion by the source’s geometric1QC theorem, without assuming W or g differentiable to
establish rigidity.

Source: LV1973 I.Theorem5.1 pp.28–29; I.Lemma4.2 p.25; inside approximation argument I.§5.3 p.30

-/
theorem asymptotically_conformal_c1_homeomorphism_limit
    (U : Set ℂ) (hU : IsOpen U) (_hU_nonempty : U.Nonempty) (hU_connected : IsConnected U)
    (gSeq : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (hSeq_source : ∀ n, (gSeq n).source = U) (hg_source : g.source = U)
    (hSeq_c1 : ∀ n, ContDiffOn ℝ 1 (gSeq n) U)
    (_hSeq_inv_c1 : ∀ n, ContDiffOn ℝ 1 (gSeq n).symm (gSeq n).target)
    (hSeq_derivative : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (gSeq n) (A : ℂ →L[ℝ] ℂ) z ∧ 0 < (A : ℂ →L[ℝ] ℂ).det)
    (K : ℕ → ℝ) (_hK_ge_one : ∀ n, 1 ≤ K n) (hK_tendsto : Tendsto K atTop (𝓝 1))
    (hDistortion : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (gSeq n) z v‖ ≤ K n * ‖fderiv ℝ (gSeq n) z w‖)
    (hLocallyUniform : TendstoLocallyUniformlyOn (fun n z ↦ gSeq n z) g atTop U)
    (hg_positive : ∀ a : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall a r ⊆ U →
      ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
          Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) = (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
        θ 1 = θ 0 + 2 * Real.pi) :
    DifferentiableOn ℂ g U := by
  apply qc_geometric_one_conformal U hU hU_connected g hg_source hg_positive
  intro Q p m m' hQcompact hQinside hQmod hImageMod
  have hLimit : ∀ L : ℝ, 1 < L → m' ≤ L * m := by
    intro L hL
    apply qc_geometric_modulus_limit U hU hU_connected gSeq g hSeq_source hg_source
      hSeq_derivative hLocallyUniform hg_positive L hL.le ?_
      Q p m m' hQcompact hQinside hQmod hImageMod
    filter_upwards [(tendsto_order.1 hK_tendsto).2 L hL] with n hn
    intro P q a b hPcompact hPinside hPmod hImagePmod
    have hTarget : IsConnected (gSeq n).target := by
      rw [← (gSeq n).image_source_eq_target, hSeq_source n]
      exact hU_connected.image (gSeq n) (by simpa [hSeq_source n] using (gSeq n).continuousOn)
    have hab := Analysis.qc_regular_to_geometric_modulus_distortion
      U (gSeq n).target hU (gSeq n).open_target hU_connected hTarget
      (gSeq n) (hSeq_source n) rfl (hSeq_c1 n) (hSeq_derivative n)
      (K n) (hDistortion n) P q a b hPcompact hPinside hPmod hImagePmod
    have ha : 0 ≤ a := by
      obtain ⟨w, h, hw, hh, rfl, _⟩ := hPmod
      exact (div_pos hw hh).le
    exact hab.trans (mul_le_mul_of_nonneg_right hn.le ha)
  have hmul : Tendsto (fun L : ℝ ↦ L * m) (𝓝[>] 1) (𝓝 (1 * m)) :=
    (continuous_id.mul continuous_const).continuousWithinAt
  simpa only [one_mul] using ge_of_tendsto hmul
    (Filter.eventually_of_mem self_mem_nhdsWithin (fun L hL ↦ hLimit L hL))


end HolomorphicAnosov
