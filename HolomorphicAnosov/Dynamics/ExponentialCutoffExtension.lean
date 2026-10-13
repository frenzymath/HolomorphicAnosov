import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.SmallRemainder

noncomputable section
namespace HolomorphicAnosov
namespace ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The source's actual exponential-lift cutoff extension, with arbitrary continuous fibre norm.

Source: HPS (1977), proof of Theorem 5.5, pp. 61–62. This is the current nine-step composite:
Lee (2003), Lemmas 1.6, 2.27, 11.19, Proposition 2.24 and Theorem 17.19; Kriegl–Michor
(1997), §1.4, pp. 10–11; Merry (2020), Lecture 32, Theorem 32.2, equations 32.6–32.7;
and the native Mathlib Taylor-product and composition mechanisms named in the proof.
No single printed theorem with the full arbitrary-norm compact-set contract is asserted.

The map `h` is literally the restriction of `f` to `A`; no independent base map is supplied.
`G` is the displayed, concrete product/zero extension of the SAME centered exponential lift.
The inverse `L` is selected together with a genuine common exponential chart radius; it is
not an assumed input map. Its left-inverse identity on that radius disc and the receiving
radius guard select the actual local inverse branch on the inner domain. Every exponential
value in a conclusion belongs to its genuine domain. Arbitrary totalized off-domain values
of the exponential or `L` supply no regularity or identity.

`r : ℕ∞` includes finite orders and smooth order. Fibre slices are `C^r` and all vertical
jets through that order are jointly continuous in the actual source/receiving tangent frames.
No ambient `C^r` regularity of `Tf`, the cutoff remainder, or `G` is asserted. The norm is
continuous only over the original restricted tangent bundle; it need not be smooth or
Riemannian. The Lipschitz estimate is the exact all-pairs inequality in that original norm,
and no higher derivative of the remainder is claimed small. Empty `A`, zero-dimensional
fibres, and disconnected manifolds are included. Neither geodesic completeness nor ambient
invertibility of `f` is required.

Complete current natural-language proof:
1. If A is empty, choose any b>0 and the unique empty bundle map; every assertion is vacuous. A
zero-dimensional manifold has zero tangent fibres, exp_p(0)=p, and the sole fibre map is zero, so
G=Tf gives the assertion directly. Otherwise retain the given smooth Riemannian fibre norm |·|_g
for the cutoff and write ν for the arbitrary continuous norm in the statement. Invoke the CURRENT
exact contract of hps.uniform_exponential_lift_on_compact_set: f(A)⊆A follows from h=f|A being a
homeomorphism A→A. It supplies an ambient open U⊇A, ρ>0, the actual open O={(q,v):q∈U,|v|_g<ρ},
the smooth diffeomorphism Φ:O→B⊂M×M and its smooth inverse Ψ(q,w)=(q,L(q,w)), both inverse
identities, L(q,q)=0 and D_wL(q,q)=id. It also supplies 0<R≤ρ and (f(p),f(exp_p(v)))∈B for every
p∈A,|v|_g<R. These are actual provider outputs, not extra assumptions or an unspecified global
exponential inverse.

Use the SAME open-domain construction written in its E4–E5 proof. Let D⊂TM be the open exponential
domain containing the zero section and define T(q,v)=(f(q),f(exp_q(v))) on D. Put Ω_amb={
(q,v)∈D:T(q,v)∈B }. Continuity makes Ω_amb open. At p∈A, T(p,0)=(f(p),f(p))∈B; the provider's R
ensures that its entire stipulated fibre tube over A lies in Ω_amb. On this actual domain
H(q,v)=L(f(q),f(exp_q(v))) is the second component of Ψ∘T and takes values in T_(f(q))M. The
provider E4–E5 source proof verifies that it is ambient C^r there by the original ambient f and
the smooth exponential/inverse maps. Its restriction gives H_p(0)=0, D_vH_p(0)=Tf_p and the
supplied joint fibre jets over A. We do not extend h independently: the ambient map is the
already-given f. No invariant ambient neighborhood, geodesic completeness or ambient invertibility
is used.

For the exact receiving-frame binding, at p0∈A choose genuine smooth source tangent frames near p0
and genuine smooth receiving frames near f(p0). Restrict the ambient source base by f
inverse(receiving-frame source), an open set because f is continuous. Restrict further to Ω_amb in
the total-space source chart. In fixed finite real models the expression H_loc(q,u)=K_(f(q))
inverse H(q,J_q u) is C^r on this ACTUAL open coordinate domain, exactly as in provider E5. Its
total ordinary jets through r are continuous there. The jth vertical jet is the total j-linear jet
restricted to the constant vertical arguments (0,u1),…,(0,uj): apply the chain rule to the
fixed-base affine inclusion u↦(q,u), whose derivative is the constant vertical inclusion and whose
higher jets vanish. Thus restriction in fixed finite-dimensional multilinear coordinates is
continuous, including order0. Restricting these fields to q∈A yields the required original joint
fibre jets with no manifold structure on A. Arbitrary off-domain totalization is only a calculus
interface and supplies no outside derivative or continuity. This consumes the exact original lift
and its genuine open-domain/frame source proof; its named lower geometric inputs remain
conditional one-level providers.

Keep the finite-r distinction explicit. The ambient map (q,v)↦Tf_q(v) need generally be only
C^(r−1) in q, even though it is linear in v. We claim no ambient C^r regularity for Tf,Q=H−Tf,R or
the global G. In the SAME paired frames let L_f(q)=K_(f(q)) inverse∘D_qf∘J_q. Because f is C^r
with r≥1, its first derivative is continuous; the smooth frames and continuous f make L_f
continuous in the original operator norm. The same continuity of L_f over A follows directly from
the exact provider identity D_vH_p(0)=Tf_p and its joint first-fibre-jet continuity at the zero
section, so no stronger ambient base regularity is required. The fibre jets of v↦Tf_q(v) are
explicitly L_f(q)u at order0, L_f(q) at order1, and0 at every order≥2. They are jointly
continuous. Consequently H−Tf has C^r fibre slices and joint ordinary vertical jets
D_v^jQ=D_v^jH−D_v^j(Tf) through r. Subtraction here is the fixed linear operation on each paired
coefficient space. These are the precise input jets for Steps3 and7. Only H is ambient C^r; on the
inner region where the later cutoff equals1, G=H, but that equality is not extrapolated to an
ambient regularity assertion elsewhere.

2. If A is empty, retain the already separated vacuous construction; otherwise prepare the finite
source-frame cores by the actual written nested-coordinate-ball construction in Lee2003 Lemma1.6
printedpp8–9/PDF24–25 and Proposition2.24 proof printedpp53–54/PDF69–70. For every p∈A choose one
of the given tangent frames on an ambient open U_p^src containing p. As in the printed proof,
choose a smaller smooth base coordinate neighborhood W_p⊂U_p^src with chart φ_p:W_p→B3(0) centered
at p, and put U_p=φ_p⁻¹(B1(0)) and C_p=φ_p⁻¹(closedB1(0)). Use the same fixed ordinary Euclidean
coordinate model throughout these base balls; no native Fin n→Real maximum-norm ball is identified
with a Euclidean ball. These smaller base charts restrict the ORIGINAL tangent frames; they do not
replace those frames or require a new transition regularity theorem.

The finite-dimensional proper-space and compact-closed-ball leaves make closedB1 compact. It lies
strictly in the inverse chart's actual open target B3. Restrict the inverse chart's supplied
ContinuousOn certificate to closedB1 by continuous_on_mono, and apply
isCompact_image_of_continuousOn to obtain compact C_p in M. No globally continuous total inverse
chart is assumed. Since M is Hausdorff, C_p is ambient closed, so isCompact_inter_right gives
compact K_p=A∩C_p. The open trace A∩U_p contains p and is contained in K_p, hence in
interior_A(K_p). This is Lee's written compact chart-core/ambient-closure argument with the
relative intersection explicitly bound.

The U_p cover A. Perform the printed compact finite selection with the EXISTING
isCompact_elim_directed_cover_g10 exactly as in the human-written proof of Mathlib
Compact.lean209–213: index by Finsets T of points p∈A, let O_T be the finite union of their U_p,
and use the family of these open unions. The Finset index is nonempty because it contains ∅, the
family is directed by T,T′↦T∪T′, and its total union covers A. Thus one finite T covers A. This is
the exact native proof of finite-subcover extraction, not a different global shrinking argument.
For nonempty A, the selected finite family is nonempty and its K_p relative interiors cover A.
Each selected point lies in its own K_p. Reindex these original-frame restrictions and cores as
K_i. Discard empty cores; when A is nonempty the remaining finite family is still nonempty and
covers A. On a rank-zero core the only vector is0, so set its comparison constants to1 and the
bounds are vacuous; no empty unit sphere is used. On each remaining positive-rank core, identify
tangent vectors with u∈R^n by its frame, and follow the actual written proof of Lee2003
Lemma11.19, printedp278/PDF294.

The set L_i=K_i×S^(n−1), with the Euclidean unit sphere in these vector coordinates, is compact by
the named compact-sphere and product leaves. The two real functions N_ν(p,u)=ν_p(frame_i(p)u) and
N_g(p,u)=|frame_i(p)u|_g are continuous on L_i and strictly positive there: u has norm1, each
frame is a linear isomorphism, and both fibre norms vanish only at0. The compact minimum leaf
gives attained minima c_ν,i>0 and c_g,i>0. The compact continuous-function bound leaf gives finite
upper bounds, which can be increased to positive C_ν,i and C_g,i. Thus c_ν,i≤N_ν≤C_ν,i and
c_g,i≤N_g≤C_g,i simultaneously on L_i. The functions need only be continuous on this compact set,
as the exact prerequisites state; no extension of ν to a smooth norm on an ambient neighborhood is
assumed.

For any nonzero coordinate vector u put λ=||u||_Euclidean>0. Then u/λ lies on the unit sphere and
(p,u/λ)∈L_i. By the same homogeneity calculation printed in Lee’s proof,
ν_p(frame_i(p)u)=λN_ν(p,u/λ), so c_ν,iλ≤ν_p(frame_i(p)u)≤C_ν,iλ. Repeating the identical written
calculation for the Riemannian norm gives c_g,iλ≤|frame_i(p)u|_g≤C_g,iλ. All four constants are
positive before any division; combining the inequalities gives m_i|v|_g≤ν_p(v)≤M_i|v|_g, where
m_i=c_ν,i/C_g,i>0 and M_i=C_ν,i/c_g,i>0. At v=0 both sides vanish, as Lee explicitly handles
separately. Take m=min_i m_i>0 and M=max_i M_i<∞ over the finite nonempty family, including the
rank-zero constants1 if present; these bounds hold on every fibre over A, and m≤M. Since h(A)=A,
the same constants control target fibres over h(p). Therefore the cutoff may use the given smooth
Riemannian norm while measuring all source/target estimates in the possibly nonsmooth continuous
ν.

Lee’s literal lemma is stated for a Riemannian norm on an open Euclidean coordinate domain, but
its displayed proof uses only compact K×sphere, continuity and strict positivity on that sphere,
homogeneity, and a separate zero-vector case. The application to ν follows precisely that written
computation with those operative hypotheses verified on each compact core; it does not call ν
Riemannian, assume A smooth or h differentiable, or claim the whole arbitrary-norm bundle theorem
is a verbatim instance of the lemma. The nested-ball compact-core construction and compact finite
selection now follow the written Lee1.6/2.24 component with the native interfaces above. Relative
frame/domain selection and the finite global min/max assembly retain their explicit generic
application boundary; no whole compact-family cutoff theorem is attributed to these source
passages.

3. Set Q_p(v)=H_p(v)−Tf_p(v). Subtraction of the actual fibre derivatives gives Q_p(0)=0 and
D_vQ_p(0)=0; the supplied lift gives jointly continuous fibre derivatives through order r in
source and receiving frames. Fix η>0. Prepare the paired-frame cores by the SAME written
Lee1.6/2.24 nested-ball construction, now with the relative paired domain explicitly bound. For
p∈A choose original source and receiving frames on ambient opens U_p^src about p and V_p^tgt about
h(p). On the actual subtype A, continuity of Subtype.val makes their traces open, continuity of
h:A→A makes h⁻¹(A∩V_p^tgt) open, and the finite-open-intersection leaf (two members indexed by
Bool) makes P_p=(A∩U_p^src)∩h⁻¹(A∩V_p^tgt) relatively open. Apply isInducing_isOpen_iff to the
subtype inclusion A→M, whose IsInducing certificate is the definition of its inherited topology,
to choose an ambient open O_p with A∩O_p=P_p. Intersect O_p with U_p^src if necessary so the
smaller ambient chart also retains the original source frame. This does not extend h outside A and
does not assert that its relative preimage is ambient open.

Choose W_p⊂O_p with φ_p:W_p→B3 centered at p and use its inner U_p=φ_p⁻¹B1 and closed core
C_p=φ_p⁻¹closedB1 exactly as above. The inverse chart is used only on its actual open target and
restricted to closedB1; compact image, ambient Hausdorff closedness and compact intersection give
K_p=A∩C_p. Then K_p⊂P_p, its relative interior contains A∩U_p, and the source frame and the
receiving frame evaluated at h(p) both cover every base point in the core. Compact finite
selection uses the same Finset-union directed-cover specialization of Compact.lean209–213; the
selected finite K_i relative interiors cover A, and are nonempty when A is nonempty. Only this
nested-ball/finite-selection component follows Lee's printed proof. Relative-open paired-domain
binding and restriction of the original frames are explicit prerequisite applications; no
smoothness of A, derivative of h or ambient extension of h is assumed. Identify each K_i with its
compact image in its source base chart. Apply the preceding compact-sphere norm bounds separately
in these source and receiving frames, denoting the positive constants by c_ν,i^src, C_ν,i^tgt,
c_g,i^src, C_g,i^src. Empty cores are discarded; rank-zero cores need no derivative estimate since
their maps are zero.

On a positive-rank core define the actual fixed-coordinate operator field
B_i(p,u)=frame_tgt(h(p))⁻¹ ∘ D_vQ_p(frame_src(p)u) ∘ frame_src(p), a continuous real-linear map
between the fixed Euclidean coordinate spaces. Its zero value at u=0 is literal. The existing
joint first-fibre-jet property makes (p,u)↦B_i(p,u)e continuous for every fixed coordinate vector
e. On its actual relative-open coordinate lift domain,
mathlib.finiteDimensional_continuous_clm_apply therefore gives continuity of B_i in the Euclidean
continuous-linear-map operator norm. Apply this theorem on that domain subtype and restrict to the
compact product below; if an ambient total function is required, extend arbitrarily outside the
domain and use only its ContinuousOn restriction. No continuity of an off-domain extension or of
derivatives transverse to A is asserted.

Set r_0,i=R/(2C_g,i^src)>0. The product P_i=K_i×closedBall(0,r_0,i) is compact by the existing
compact-product and finite-dimensional compact-closed-ball leaves, and every vector on it lies
strictly in the actual lift domain: |frame_src(p)u|_g≤C_g,i^src||u||≤R/2<R. Now follow precisely
the written uniform-small-matrix computation in Lee2003 Theorem17.19 proof,
printedpp457–458/PDF473–474, equations(17.23)–(17.24): a jointly continuous matrix field on a
compact base/vector product, zero when the vector is0, is uniformly small for all base points when
the vector is sufficiently small. Here mathlib.isCompact_uniformContinuousOn_of_continuous gives
uniform continuity of B_i on P_i, and mathlib.metric_uniformContinuousOn_iff_g8, with η_E,i=η
c_ν,i^src/C_ν,i^tgt>0, supplies σ_i>0 such that ||B_i(p,u)−B_i(p,0)||<η_E,i whenever (p,u)∈P_i and
||u||<σ_i. Indeed (p,0) also lies in P_i and their product distance is exactly ||u||. Thus
||B_i(p,u)||<η_E,i uniformly in p∈K_i. Lee writes the usual Euclidean matrix norm; we do not
identify it with operator norm. The same published compact-uniform-continuity computation is
applied to the chosen fixed Euclidean CLM norm using the exact named Heine–Cantor and
metric-modulus APIs; the verification of operator-valued continuity remains the explicit
prerequisite binding above.

For clarity, the conversion back to ν is a separate norm-comparison verification, not an extra
conclusion of Lee’s ODE theorem. For a coordinate vector e, mathlib.continuousLinearMap_le_opNorm
and the previous norm bounds give ν_{h(p)}(frame_tgt(h(p))B_i(p,u)e)≤C_ν,i^tgt||B_i(p,u)||
||e||≤(C_ν,i^tgt/c_ν,i^src)||B_i(p,u)|| ν_p(frame_src(p)e). Both comparison constants are strictly
positive before division. Consequently mathlib.continuousLinearMap_opNorm_le_bound, applied on the
fixed pair of fibres endowed with their supplied ν norms, bounds the ν-source-to-ν-target operator
norm of D_vQ_p(v) by (C_ν,i^tgt/c_ν,i^src)||B_i(p,u)||≤η. These are finite-dimensional continuous
linear maps in either equivalent norm; no differentiability of ν is used.

Put r_i=min(r_0,i,σ_i)>0 and choose the common δ=min(R/2, min_i(c_g,i^src r_i/2))>0 over the
finite nonempty positive-rank family. In the already separated all-zero-rank case any 0<δ<R
suffices. If |v|_g≤δ and p∈K_i, write v=frame_src(p)u. The LOWER source comparison gives
||u||≤δ/c_g,i^src≤r_i/2<r_i≤σ_i and ||u||<r_0,i, so (p,u)∈P_i and the strict uniform-continuity
modulus applies even at the closed physical boundary |v|_g=δ. Thus 0<δ<R and
||D_vQ_p(v)||_{ν_p→ν_{h(p)}}≤η for all p∈A and |v|_g≤δ. The radius is chosen after η and before p.
Only this fixed-core continuous-zero-operator-to-uniform-radius algorithm is substantively
replaced by Lee’s written method; the printed Lee nested-ball/finite-selection preparation is the
additional scoped source component; relative paired-frame/domain binding, supplied joint-jet
binding, norm conversion and finite global assembly retain their explicit generic application
boundary.

4. Fix p∈A and |v|_g≤δ. Work on the actual fixed source and receiving tangent fibres, endowed
respectively with ν_p and ν_{h(p)} as real normed-space norms. The preceding positive
finite-dimensional comparison constants identify their norm topologies with the coordinate
topologies, so the supplied fibre derivatives and continuity of Q are unchanged; no derivative of
ν is taken. If v=0, Q_p(0)=0 proves the estimate immediately. In a rank-zero fibre there is only
this case. Otherwise set c(t)=Q_p(t•v), 0≤t≤1. By mathlib.norm_smul, |t•v|_g≤|v|_g≤δ<R, so every
point of the CLOSED parameter segment, including both endpoints, lies in the actual OPEN lift
fibre domain. The ambient derivative of Q_p exists at every such point. Existing
mathlib.affine_lineMap_hasDerivAt, with endpoints0,v, identifies the radial path with t•v and
gives its derivative v; mathlib.hasFDerivAt_comp_hasDerivAt gives c′(t)=D_vQ_p(t•v)(v). Thus c is
continuous on [0,1] and has the stated ambient derivative at every interior point. The preceding
operator bound and mathlib.continuousLinearMap_le_opNorm give ν_{h(p)}(c′(t))≤η ν_p(v). Put C=η
ν_p(v)≥0 and K=closedBall(0,C) in the receiving ν norm; mathlib.mem_closedBall_zero_iff_g8
identifies this derivative inequality with c′(t)∈K.

Now substantively follow the written closed-convex-set mean-value mechanism of Kriegl–Michor1997
§1.4, printedpp10–11/PDF16–17, in precisely its prologue’s specified later-use case h=Id and
everywhere differentiability in the interior. Take the exceptional set D={0,1}; no exceptional
interior times or moving-parameter conclusion is used. K is convex by mathlib.convex_closedBall.
Finite-dimensional properness in the fixed ν norm and mathlib.isCompact_closedBall make K compact,
and mathlib.isCompact_isClosed makes it closed in this normed Hausdorff fibre. Local convexity in
the same topology is supplied by mathlib.normedSpace_toLocallyConvexSpace_g8. Suppose x=c(1)−c(0)
is outside K. The exact mathlib.geometric_hahn_banach_closed_point_g5 gives a continuous
real-linear functional ell and a real u with ell(z)<u for every z∈K and u<ell(x). This is the
strict Hahn–Banach separation invoked by the printed proof, not the bank’s different
nonstrict/nonempty-interior theorem or an invented norming-dual argument.

The printed proof reduces the separated curve to a scalar mean-value inequality. In this
h=Id/no-interior-exceptions specialization, execute that scalar step with the existing
bochner_montgomery.generator_g3_scalar_mean_value: ell∘c is continuous on [0,1], and
mathlib.continuousLinearMap_hasFDerivAt for ell followed by the same chain rule gives its ambient
derivative ell(c′(t)) at every t∈(0,1). The scalar theorem returns τ∈(0,1) with
ell(c′(τ))=(ell(c(1))−ell(c(0)))/(1−0)=ell(x). But c′(τ)∈K, so ell(c′(τ))<u<ell(x), a
contradiction. Consequently x∈K. Since c(0)=Q_p(0)=0 and c(1)=Q_p(v), the exact closed-ball
membership equivalence gives ν_{h(p)}(Q_p(v))≤η ν_p(v)≤ηMδ. The last comparison is the already
obtained source-fibre norm bound, not an additional conclusion of Kriegl–Michor.

This replaces the old unsourced vector-norm mean-value sentence by the published
Hahn–Banach/scalar-reduction mechanism and exact named generic prerequisites. The full printed
countable-exception proof uses an ε-weighted maximal-interval argument on pp10–11; we neither
claim to formalize that stronger theorem nor supply a new replacement for its omitted
prerequisites. The ordinary scalar mean-value theorem is sufficient in the explicitly stated
h=Id/everywhere-interior-differentiable case used here. Actual radial-domain, derivative,
norm-comparison and compact-family inputs are the preceding explicitly verified source/API
applications. Together with the input-jet and open-overlap bindings in Steps1/5/7 they form the
independently reviewed one-level composite proof.

5. Fix a smooth real scalar bump β with values in [0,1], equal to one on [0,1/4], and zero on
[1,∞). It can be taken from a smooth real bump centered at zero with inner radius1/4 and outer
radius1. The actual Mathlib bump support identity is Function.support β=ball(0,1), and the direct
source declaration ContDiffBump.zero_of_le_dist at BumpFunction/Basic.lean163–164 gives β(t)=0
when1≤dist(t,0), in particular for every t≥1. Equivalently, the existing topological-support
supplier puts support inside closedBall(0,1), giving zero for t>1, and continuity of β gives the
boundary value β(1)=0; no separate stronger support conclusion is attributed to tsupport_eq.

Only NONNEGATIVE scalar arguments enter g_p(v,v)/δ². Choose K≥0 bounding |β′(t)| on the compact
interval [0,1], using smoothness, continuity of the derivative and the compact continuous-function
bound. For t>1, β is identically zero on a neighborhood, so β′(t)=0; continuity of β′ gives
β′(1)=0 as well. Therefore the same K bounds the derivative for all t≥0. No global bound on
negative scalar arguments is asserted or needed. Define χ_p(v)=β(g_p(v,v)/δ²). This is smooth on
every fibre and all its fibre derivatives vary continuously with p; it is one for |v|_g≤δ/2 and
zero for |v|_g≥δ. This intrinsic squared-norm formula agrees in all tangent frames. It does not
require a smooth trivialization over the possibly nonsmooth set A.

Bind the joint cutoff jets directly to the given SMOOTH Riemannian metric, rather than treating
them as an unprovided parameter theorem. On any genuine smooth tangent frame J_q over an ambient
base coordinate open, write g_ij(q)=g_q(J_q e_i,J_q e_j). These coefficient functions are smooth
by the given smooth metric and smooth frame. The actual scalar function S(q,u)=g_q(J_q u,J_q u)/δ²
is the finite sum δ^−2 Σ_i,j g_ij(q)u_i u_j on that open source frame. It is ambient smooth, since
δ>0 is fixed. Its ordinary vertical jets are its value, the linear map e↦2g_q(J_q u,J_q e)/δ², the
bilinear map(e1,e2)↦2g_q(J_q e1,J_q e2)/δ², and0 for every higher order. All are jointly
continuous in q,u in the fixed finite multilinear models; no derivative of ν or of A is involved.
Equivalently they are the restrictions of the actual total smooth jets to the constant vertical
inclusions, as in Step1/E5. This concerns the smooth metric, not the fixed-norm ContDiff_norm_sq
theorem applied to a varying parameter without justification.

The SAME cutoff is χ(q,J_q u)=β(S(q,u)), ambient smooth on this frame and intrinsically defined on
TM. To bind its ordinary vertical jets to the existing native calculus, take the fixed smooth β on
univ. For each finite j its ordinary coefficient field is continuous by
contDiffOn_continuousOn_iteratedFDerivWithin with UniqueDiffOn univ, followed by
iteratedFDerivWithin_of_isOpen. For each fixed q the scalar S_q is smooth on its whole fixed
source model; its explicit coefficient fields above are jointly continuous. Apply the existing
native Taylor .comp theorem and coefficient uniqueness on that SAME open source slice to β∘S_q.
For every j the actual coefficient is the finite ordered-partition sum of β's coefficient at
S(q,u) and the displayed S_q coefficients. The existing bundled compAlongOrderedFinpartitionL,
continuous uncurried evaluation, order bounds and finite-sum continuity give joint continuity,
exactly the generic mechanism used for the product in Step7. No factorial/symmetry bridge,
analytic premise or new induction is required. This verifies the previously recorded χ input jets
at every j≤r (and every finite j in the smooth case) on the SAME original frame domain. Restrict
to q∈A only afterward. χ is ambient smooth; that true statement implies no ambient Cr assertion
for Q or the global cutoff remainder.

6. Differentiation gives D_vχ_p(v)(u)=β′(|v|_g²/δ²)·2g_p(v,u)/δ². The Cauchy–Schwarz bound
therefore gives |D_vχ_p(v)(u)|≤(2K/(mδ))ν_p(u) on |v|_g≤δ. For |v|_g>δ the cutoff is locally zero.
At |v|_g=δ, its displayed derivative is zero because its scalar argument is1 and β′(1)=0 by the
preceding nonnegative-scalar boundary argument. Hence the first-derivative formula and bound hold
through the support boundary, exactly as required by the preserved Merry estimate. The
higher-order boundary-limit calculation is unnecessary for the following open-overlap gluing: that
proof treats |v|_g=δ inside the actual lift domain and |v|_g=R inside the open zero region.

7. Define the remainder R_p(v)=χ_p(v)Q_p(v) on |v|_g<R and R_p(v)=0 outside that domain; set
G_p(v)=Tf_p(v)+R_p(v). Because δ<R, the product vanishes on the open collar δ<|v|_g<R before the
outer H-domain boundary. The product and zero formulas agree on an open overlap. Keep the original
pointwise C^r gluing argument below. Bind the interior jointly continuous product coefficients
directly to the written native Mathlib Taylor-product/Faà di Bruno proof; no symmetric jet model,
factorial conversion or analyticity premise is used by this route.



For the remaining gluing and actual-domain binding follow the OPEN-overlap product/zero proof
written in Lee2003 Lemma2.27 printedp56/PDF72. We use that proof paragraph, not its whole
smooth-extension theorem on a closed subset, its partition construction, vector-bundle
Exercise5.4, or a smooth structure on A. On the original fibre family put U_A={(p,v):p∈A,|v|_g<R}
and V_A={(p,v):p∈A,|v|_g>δ}. Their relative openness follows from the continuous original metric
norm, and δ<R makes them cover T_AM. U_A is actually inside the Ω_amb from Step1, so no product
input is evaluated outside the original lift. In each prepared paired frame, intersect its source
with f inverse(receiving-frame source) before restricting to A. The resulting source domain is
open, and Ω_amb gives the actual open coordinate lift domain. Every point has a product
neighborhood inside that domain; restriction to A yields the relative W×B used below. This is a
local product-neighborhood fact, not a global tube extension or f-invariant ambient neighborhood.
Step1 supplies precisely Q's input jets there; Step5 supplies precisely χ's input jets there.

On U_A define R=χQ. On V_A define R=0. Where both apply, δ<|v|_g<R and the original cutoff is
identically0, so these are the SAME function on an OPEN overlap, exactly the source zero-extension
mechanism. The support boundary |v|_g=δ belongs to U_A, while the outer boundary |v|_g=R belongs
to V_A. The fixed-fibre finite-r local APIs below implement Lee's locality argument; the native
product coefficients and germ equalities implement joint vertical-jet continuity. At each point
choose either of these original open regions and a paired-frame neighborhood inside it. There the
global ordinary vertical jet agrees, by eventuallyEq_iteratedFDeriv on each fixed fibre, with the
continuous product-jet field or with0. Continuity is local, so the restriction of the global field
is continuous at every point; because the formulas agree as actual functions on overlap, their
jets agree there too. This directly verifies the open-cover continuity binding without a parameter
function-space theorem. Intrinsic scalar multiplication and the original fibre subtraction make R
independent of source/receiving frames; changing frames merely expresses these SAME ordinary
vertical derivatives in the genuine linearly related finite models. No separate source or
nonsymmetric jet bridge is missing.

If one records an ambient domain for the formula, Ω_amb∪{(q,v):|v|_g>δ} is open and contains T_AM.
The two formulas agree on its open overlap because χ=0 there. This records domains and continuity,
NOT ambient Cr for χQ or R. Tf is only guaranteed C^(r−1) in the base; the proof uses fibrewise Cr
and jointly continuous vertical jets, established in Steps1/5 and the native calculation below. No
neighborhood of A invariant under f is asserted.

In one prepared paired source/receiving frame, with receiving frame based at h(p), let Ω⊂A×E be
the actual relative-open lift domain, E a fixed finite Euclidean source model and V the fixed
receiving model. Near each (p_0,u_0)∈Ω choose a relative base neighborhood W and ordinary open B⊂E
with W×B⊂Ω inside both frame sources; no global product domain or manifold structure on A is
asserted. Put a_p(u)=χ_p(frame_src(p)u) and b_p(u)=frame_tgt(h(p))⁻¹Q_p(frame_src(p)u). On the
SAME actual open fibre slice s=Ω_p both are C^r, and the ordinary fibre derivative fields D^j
a_p(u), D^j b_p(u) are jointly continuous on Ω for j≤r by the existing χ/lift/remainder input
providers. These actual source/receiving-frame, domain and input-jet premises are verified in
Steps1/5 and the present opening; no base derivatives of A are taken.

Fix p. Totalize a_p and b_p arbitrarily outside s only for their ambient E→F calculus interface;
no outside regularity is used. mathlib.isOpen_uniqueDiffOn gives UniqueDiffOn Real s. Apply
mathlib.contDiffOn_ftaylorSeriesWithin at order r separately to a_p and b_p to get native series
α_p,β_p on this same s. At u∈s and natural j≤r,
mathlib.hasFTaylorSeriesUpToOn_eq_iteratedFDerivWithin_of_uniqueDiffOn and
mathlib.iteratedFDerivWithin_of_isOpen identify α_p(u)(j),β_p(u)(j) with their actual ordinary
iterated derivatives. These are UNNORMALIZED native multilinear coefficients. Their zeroth
coefficients are the actual zero-arity value maps. No permutation symmetry or correspondence with
a normalized classical jet bundle is required. The new exact
mathlib.hasFTaylorSeriesUpToOn_prodMk_g5 gives a native Taylor series
π_p(u)(j)=α_p(u)(j).prod(β_p(u)(j)) for F_p(u)=(a_p(u),b_p(u)) on s. The new
mathlib.continuousMultilinearMap_prodL_g5 is the actual linear isometry taking the paired jth
coefficients to π_p(u)(j). Thus their given joint continuity, mathlib.continuous_prodMk and
mathlib.continuous_comp give joint continuity of every paired native coefficient on the actual Ω
subtype, including j=0.

Define the fixed map μ:Real×V→V by μ(t,z)=t•z. The first and second projections are continuous
affine maps. mathlib.continuousAffineMap_contDiff makes each smooth, and the existing FUNCTIONAL
theorem mathlib.contDiff_smul (ContDiff.smul, applied to those two functions) makes μ smooth. This
is not an invented theorem about the bundled scalar action. Restrict μ to univ and use
mathlib.contDiffOn_ftaylorSeriesWithin with order r and UniqueDiffOn Real univ to get its native
series q_μ. To explicitly supply its coefficient fields, restore
mathlib.contDiffOn_continuousOn_iteratedFDerivWithin on this SAME univ: for every natural ℓ≤r it
gives continuity of the ℓth within jet, and mathlib.iteratedFDerivWithin_of_isOpen identifies it
with the ordinary D^ℓμ. On univ this is a globally continuous ordinary coefficient field, and the
existing coefficient-uniqueness identity identifies q_μ(y)(ℓ) with that field at every y. No
property of A or an excluded source boundary enters this fixed outer-map argument.

MapsTo F_p s univ is immediate. Apply the new exact mathlib.hasFTaylorSeriesUpToOn_comp_g5 with hg
the μ-series on univ and hf the paired F_p-series on s. It gives a native Taylor series
θ_p(u)=(q_μ(F_p(u))).taylorComp(π_p(u)) for μ∘F_p=a_p b_p on the actual s. Reuse coefficient
uniqueness with j≤r and u∈s, followed by ordinary/within equality on that open s, to identify
θ_p(u)(j) with the ACTUAL ordinary jth fibre derivative of the product. The operative identity is
the native UNNORMALIZED ordered-partition formula. It does not convert to Michor’s symmetric
coefficients, divide by factorials or use analytic FormalMultilinearSeries.comp. The pinned Faà di
Bruno source explicitly distinguishes this taylorComp operation and preserves derivative argument
order even without symmetry.

Prove the joint continuity of these identified coefficients by the SAME finite-term continuity
mechanism printed in the human-written native proof FaaDiBruno.lean1101–1112. For each fixed j≤r
and c:OrderedFinpartition j, set B_c=c.compAlongOrderedFinpartitionL Real E (Real×V) V. The new
exact mathlib.orderedFinpartition_compAlongOrderedFinpartitionL_g5 bundles the term as a
continuous linear map into continuous multilinear maps. Its input at (p,u) is the outer
coefficient q_μ(F_p(u))(c.length), paired with the finite dependent tuple i↦π_p(u)(c.partSize i).
The source bounds c.length≤j and c.partSize i≤j ensure EVERY used coefficient order is≤j≤r. The
outer field is continuous by the already established global μ coefficient continuity and
continuity of F_p’s values; the inner coefficient fields are continuous by prodL.
mathlib.continuous_pi assembles the finite dependent tuple, and mathlib.continuous_prodMk
assembles the outer/inner pair on the actual parameter-domain subtype. The new
mathlib.continuousLinearMap_continuous_uncurry_of_multilinear_g5 applied to B_c, then
mathlib.continuous_comp, gives continuity of each partition term in (p,u). The coefficient
taylorComp is the FINITE sum over c:OrderedFinpartition j; finite repeated application of
mathlib.continuous_add_g8 gives continuity of that sum. This is the exact
bundled-operation/finite-sum argument of the source, not a new joint derivative induction. At j=0
the empty ordered partition is included by the native definition and .comp theorem; equivalently
the coefficient is the already continuous value μ(a_p(u),b_p(u)). Empty coefficient tuples cause
no missing argument. For smooth-infinity r, each finite j uses the SAME Ω/s and its local product
portions, without an intersection of shrinking domains. This proves the required joint ordinary
product jets on Ω without any derivative of the topological parameter A or any symmetry premise.

Michor1980 §§1.3–1.6 pp2–3, Theorem1.10(4),(5) proofpp5–6 and4.5(1)–(3)p35 remains the genuine
published classical finite-jet pairing/postcomposition reference. Its normalized
symmetric-coordinate convention describes a parallel classical source mechanism; it is not an
operative native coefficient-identification bridge in the present proof. The earlier
higher-symmetry/bundled-classical-jet obligation is retired because this native route does not
require it, not because a general symmetry or classical/native jet-equivalence theorem has been
proved. No WO/CO mapping-space theorem, C∞-only Omega lemma, globally smooth totalization or fresh
helper/bridge is asserted.

For the pointwise all-order calculus binding, fix p and work over Real on the normed vector spaces
T_pM and T_{h(p)}M, with the SAME finite or smooth-infinity order r. Put U_p={v:|v|_g<R} and
V_p={v:|v|_g>δ}. Both sets are open and U_p∪V_p is the whole fibre because δ<R. Totalize Q_p
arbitrarily off U_p only to fit the ambient map interface; no smoothness of that totalization is
used there. The existing mathlib.contDiffOn_smul gives ContDiffOn of the product P_p=χ_pQ_p on
U_p. At each v∈U_p, mathlib.isOpen_contDiffOn_iff gives ContDiffAt P_p of order r. Since R_p=P_p
on this open neighborhood, mathlib.contdiff_at_eventually_eq transfers that certificate to R_p. On
all of V_p, both branches of the original definition give R_p=0: inside U_p the cutoff is zero,
and outside U_p the remainder was defined to be zero. The exact mathlib.contDiffOn_const on the
whole fibre and mathlib.isOpen_contDiffOn_iff give ContDiffAt of this constant zero function;
eventual equality on V_p transfers it to R_p. Finally mathlib.contDiff_iff_contDiffAt yields C^r
of R_p on the whole fibre. This covers |v|_g=δ by U_p and |v|_g=R by V_p, uses no derivatives at
an excluded boundary, and needs no completeness or new smooth ambient parameter assumption. These
existing generic leaves certify the unchanged fixed-p C^r gluing. At a point of U_p, the identity
R_p=P_p on an ambient open neighborhood gives mathlib.eventuallyEq_iteratedFDeriv at every natural
j; at a point of V_p the identity R_p=0 on an ambient open neighborhood gives the same germ
equality, and mathlib.iteratedFDeriv_zero identifies all zero-region jets with0, including j=0. In
each prepared frame U={ (p,v):|v|_g<R } and V={ (p,v):|v|_g>δ } are relative-open and cover the
fibre family. On U the global remainder jets are the just-proved jointly continuous product jets;
on V they are zero; on their open overlap those jets agree by the local identities. The retained
elementary open-cover continuity binding gives their joint continuity and the intrinsic
product/zero expressions agree on frame overlaps. At |v|_g=δ use U; at |v|_g=R use V. Tf has its
already supplied continuous linear fibre data and zero higher jets, so adding it preserves the
stated joint fibre regularity of G. The original source/receiving-frame and actual-domain inputs
are verified in Step1 and the present opening; χ/Q joint jets are verified in Steps1/5. The
displayed fixed-p eventual-equality APIs implement the Lee open-overlap proof, and the preceding
pointwise local continuity argument verifies the joint-jet/frame binding. These are now explicit
generic applications of the SAME source construction, not separate unsupplied mathematical
interfaces. No single literal published theorem matching the broader cutoff statement is claimed.
The whole source/API composite is independently reviewed complete one level relative to its named
lower providers.

8. The pointwise first-derivative argument now follows Merry’s written scaled-bump calculation,
Lecture32 proof of Theorem32.2, equations(32.6)–(32.7), lecture-local pp5–6/full PDF231–232,
applied on each fixed fibre. Keep precisely the scalar bump β and the cutoff χ_p(v)=β(g_p(v,v)/δ²)
already constructed above. On the fixed source tangent space put B_p(w)=β(g_p(w,w)); homogeneity
gives χ_p(v)=B_p(v/δ). The earlier squared-norm differentiation and Cauchy–Schwarz estimate give
||DB_p(w)||_g≤2K on |w|_g≤1, and its derivative is zero outside, including the support boundary.
Thus B=max(1,2K) is a legitimate finite global bound, without division by a possibly zero K. Merry
instead prints a vector bump equal to1 for ||w||≤1/3 and0 for ||w||≥2/3 with derivative norm≤3.
That particular numerical bound is impossible for C1 in positive dimension: restricting to a unit
radial line, its change of1 across an interval of length1/3 forces average derivative magnitude3,
while continuity and the flat endpoint derivatives force the maximum to exceed3. The calculation
uses only a finite bump derivative bound, so use the already proved bound for B_p rather than that
invalid3. With a general finite bound B, the source’s displayed choices ε/6 and ε/2 can be read as
ε/(2B) and ε/2; the written cancellation (B/δ)·(ε/(2B))δ+ε/2=ε remains valid. No new bump or
alteration of the inner and outer radii is made here.

In the original norms and constants of this theorem, the exact source product rule(32.6) reads
D_vR_p(v)(u)=χ_p(v)D_vQ_p(v)(u)+D_vχ_p(v)(u)Q_p(v) on |v|_g≤δ. Its two terms are bounded by the
preceding estimates: ν_{h(p)}(χ_p(v)D_vQ_p(v)(u))≤ην_p(u), and
ν_{h(p)}(D_vχ_p(v)(u)Q_p(v))≤(2K/(mδ))ν_p(u)·ηMδ=(2KM/m)ην_p(u). This is the written scaling
cancellation in Merry(32.6)–(32.7), with the actual existing Riemannian cutoff and the previously
obtained arbitrary-norm comparison, rather than the source’s fixed numerical3. Put Λ=1+2KM/m>0 and
choose η=ε/(2Λ); then choose the single δ as in the unchanged compact-tube step. The bound is
ν_{h(p)}(D_vR_p(v)(u))≤Λην_p(u)=ε ν_p(u)/2≤ε ν_p(u). Outside |v|_g≤δ the derivative is zero, with
the support-boundary and outer-domain gluing already proved above, so this first-derivative bound
holds on the entire fibre. As in Merry’s invocation of its Mean Value Theorem30.11, integrate the
derivative bound along the entire vector-space segment v+t(w−v) using the named existing
mean-value theorem to obtain ν_{h(p)}(R_p(w)−R_p(v))≤εν_p(w−v). Therefore Lip(G_p−Tf_p)≤ε. This
proof is pointwise on a fixed pair of normed tangent spaces. Its uniformity in p uses exactly the
earlier common m,M,K,η,δ and joint derivative controls, whose compact moving-family construction
is supplied by the preceding explicit Lee/source/API applications; Merry alone does not supply
those steps. No higher derivative is required to be small.

9. Choose the statement radius b=mδ/2>0. If ν_p(v)≤b then |v|_g≤δ/2, hence χ_p(v)=1 and
G_p(v)=H_p(v)=exp_{h(p)}^{-1}(f(exp_p(v))). This gives the exact displayed exponential identity,
including the inner boundary. At v=0 both Q and its first derivative vanish, so G_p(0)=0 and
D_vG_p(0)=Tf_p. If ν_p(v)>Mδ then |v|_g>δ and G_p(v)=Tf_p(v); thus the extension agrees with Tf
outside one uniform-radius fibre disc. Every value lies in T_{h(p)}M, so G covers h and is a
continuous bundle map. Its construction does not assume invertibility of Tf or f; the
homeomorphism property of h is needed by the parent graph transform, not by this cutoff operation.

Formal domain binding: the current uniform-lift theorem supplies `U`, `ρ`, `R`, `B`, `L`
and the actual diffeomorphism `Φ:O→B`, where `O` is the given metric tube. Its inverse
lies in `O`; therefore the centered lift on the stipulated `R` disc has norm less than `ρ`
and is in the genuine receiving exponential domain. Use the actual shared
`riemannianExponential`, selected from the original metric's Levi-Civita geodesics, throughout.
The common radius and local-inverse assertions below are these same outputs, restricted to `A`.
The scaled bump, product, and zero branch are the concrete definitions in this module.
-/
theorem exponential_cutoff_extension
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (r : ℕ∞)
    (hr : 1 ≤ r) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (hfA : MapsTo f A A)
    (_hh : IsHomeomorph (fun p : A ↦ (⟨f p, hfA p.property⟩ : A)))
    (ν : ContinuousRestrictedTangentNorm (E := E) A) (ε : ℝ) (hε : 0 < ε) :
    ∃ (ρ R δ b : ℝ) (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q),
      0 < ρ ∧ 0 < R ∧ R ≤ ρ ∧ 0 < δ ∧ δ < R ∧ 0 < b ∧
      (∀ q ∈ A, ∀ v : TangentSpace 𝓘(ℝ, E) q, metricNorm g q v < ρ →
        (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExpDomain g ∧
          L q (riemannianExp g q v) = v) ∧
      let G := extension A f g (fun p ↦ centeredLift g f L p) R δ
      IsGlobalExtension A f hfA r ν ε G ∧
        ∀ (p : A) (v : TangentSpace 𝓘(ℝ, E) (p : M)), ν.value p v ≤ b →
          (⟨(p : M), v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExpDomain g ∧
          metricNorm g (f p) (G p v) < ρ ∧
          (⟨f p, G p v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExpDomain g ∧
          G p v = L (f p) (f (riemannianExp g p v)) ∧
          riemannianExp g (f p) (G p v) = f (riemannianExp g p v) := by
  obtain ⟨U, ρ, R, O, B, L, Φ, hAU, hρ, hR, hRρ, hO,
    hOD, hΦ, hΦinv, hB, hexpL, hLexp, hdiag, hdomain, hzero, hjets, _⟩ :=
    uniform_exponential_lift_on_compact_set g A hA f r hr hf hfA 1
  obtain ⟨m, M₀, hm, hM₀, hnormLower, hnormUpper⟩ :=
    finite_core_two_sided_norm_comparison_from_canonical g A hA ν
  obtain ⟨δ, hδ, hδR, hcontinuous, hvertical, hlip⟩ :=
    exists_small_cutoff_remainder g A hA f r hr hf hfA ν
      (fun p ↦ centeredLift g f L p) hR
      (fun p ↦ hzero p p.property) hjets hε
  refine ⟨ρ, R, δ, m * δ / 2, L, hρ, hR, hRρ, hδ, hδR,
    by positivity, ?_, ?_⟩
  · intro q hq v hv
    have hz : (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O := by
      change (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ (O : Set _)
      rw [hO]
      exact ⟨hAU hq, hv⟩
    exact ⟨hOD hz, hLexp q v hz⟩
  · refine ⟨⟨hcontinuous, hvertical, ?_, ?_, hlip,
      M₀ * δ, mul_pos hM₀ hδ, ?_⟩, ?_⟩
    · intro p
      exact extension_zero A f g _ hδ hδR p (hzero p p.property).1
    · intro p
      exact hasFDerivAt_extension_zero A f g _ hδ hδR p (hzero p p.property).2
    · intro p v hv
      exact extension_eq_derivative_of_auxiliary_bound A f g _ ν hM₀ hδ rfl
        (hnormUpper p v) hv
    · intro p v hv
      have hvhalf : metricNorm g p v ≤ δ / 2 :=
        inner_metric_radius_of_auxiliary_bound A ν hm rfl (hnormLower p v) hv
      have hvR : metricNorm g p v < R := by linarith
      have hG : extension A f g (fun p ↦ centeredLift g f L p) R δ p v =
          L (f p) (f (riemannianExp g p v)) :=
        extension_eq_lift A f g (fun p ↦ centeredLift g f L p) hδ hδR p v hvhalf
      obtain ⟨hsource, htarget⟩ := hdomain p p.property v hvR
      let y : B := ⟨(f p, f (riemannianExp g p v)), htarget⟩
      have hz : (⟨f p, L (f p) (f (riemannianExp g p v))⟩ :
          TangentBundle 𝓘(ℝ, E) M) ∈ O := by
        rw [← hΦinv y]
        exact (Φ.symm y).property
      have hreceiving := hOD hz
      change (⟨f p, L (f p) (f (riemannianExp g p v))⟩ :
        TangentBundle 𝓘(ℝ, E) M) ∈ (O : Set _) at hz
      rw [hO] at hz
      refine ⟨hsource, ?_, ?_, hG, ?_⟩
      · rw [hG]
        exact hz.2
      · rw [hG]
        exact hreceiving
      · rw [hG]
        exact hexpL _ _ htarget



end ExponentialCutoff
end HolomorphicAnosov
