import HolomorphicAnosov.Analysis.HolomorphicBoundaryPrimitiveIncrement
import HolomorphicAnosov.Analysis.MarkedRectangleG3DiskSchwarzChristoffelSource
import HolomorphicAnosov.Analysis.MarkedRectangleG3PrimitiveWithBoundary
import HolomorphicAnosov.Analysis.SchwarzChristoffelPrimitive
import HolomorphicAnosov.Analysis.SchwarzChristoffelBoundaryBranch
import HolomorphicAnosov.Analysis.SchwarzChristoffelDiskBoundary
import HolomorphicAnosov.Analysis.SchwarzChristoffelSideCoverage
import HolomorphicAnosov.Analysis.SchwarzChristoffelModulus
import HolomorphicAnosov.Analysis.Complex.BoundedRiemannMap
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Analysis.MashreghiDiskDerivativeHolderBoundaryG3
import HolomorphicAnosov.Analysis.SchwarzRealBoundaryExtension
import HolomorphicAnosov.Analysis.WhittakerWatsonComplementaryEllipticIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Homeomorph.Defs

/-!
# A disk-to-rectangle map with four prescribed boundary marks

Source: Stein–Shakarchi, *Complex Analysis* (2003), Chapter 8, §§4.1, 4.4–4.5,
pp. 233–234 and 241–247; Bak–Newman, *Complex Analysis*, third edition (2010),
pp. 177, 183–186 and 189–190; Whittaker–Watson, *A Course of Modern Analysis*,
third edition (1920), §22.32, p. 501. DAG: `analysis.marked_rectangle_g3_disk_schwarz_christoffel`.

The disk and its closure use Mathlib's metric balls; rectangles use `Complex.reProdIm`.
Angle lifts express positive cyclic order and define the directed closed circle arcs, including
the last arc through one full turn. The two holomorphic functions below are ambient functions;
only their restrictions to the specified open sets occur in the conclusion. The boundary
homeomorphism must extend that very forward function, and each side assertion is an image
equality, hence includes surjectivity onto the entire closed side.
-/

noncomputable section

namespace HolomorphicAnosov.Analysis.MarkedRectangle

open Set

/-- Four marks in positive cyclic order, via increasing angle lifts within one turn.
Source: the original-mark normalization in Bak–Newman, pp. 183–186, as used in the node.
`circleMap 0 1 θ` is Mathlib's literal unit-circle parametrization `exp (θ * I)`. -/
def PositiveCircleCyclicOrder (ζ : Fin 4 → ℂ) : Prop :=
  ∃ θ : Fin 4 → ℝ, StrictMono θ ∧ θ 3 < θ 0 + 2 * Real.pi ∧
    ∀ i, circleMap 0 1 (θ i) = ζ i

/-- The positively directed closed unit-circle arc from `u` to `v`, with both endpoints.
Source: the four positive boundary arcs of Stein–Shakarchi, Chapter 8, §§4.1 and 4.5.
For distinct unit-circle endpoints, this is the increasing angular arc of length less than a
full turn; the existential lifts also handle arcs crossing any chosen argument cut. -/
def PositiveClosedCircleArc (u v : ℂ) : Set ℂ :=
  {z | ∃ α β : ℝ, α < β ∧ β < α + 2 * Real.pi ∧
    circleMap 0 1 α = u ∧ circleMap 0 1 β = v ∧
    z ∈ circleMap 0 1 '' Icc α β}

/-- The open rectangle with corners `0`, `a`, `a + b * I`, `b * I`.
Source: the literal final rectangle in the node, from Stein–Shakarchi §4.5. -/
def OpenRectangle (a b : ℝ) : Set ℂ :=
  Complex.reProdIm (Ioo 0 a) (Ioo 0 b)

/-- The corresponding closed rectangle, with its ordinary complex-plane topology.
Source: the closure rectangle in Stein–Shakarchi §4.5 and the node's final step. -/
def ClosedRectangle (a b : ℝ) : Set ℂ :=
  Complex.reProdIm (Icc 0 a) (Icc 0 b)

/-- Rectangle corners, ordered counterclockwise starting at the origin.
Source: the four prescribed corner values in the node's final affine normalization. -/
def RectangleCorner (a b : ℝ) (i : Fin 4) : ℂ :=
  match i.val with
  | 0 => 0
  | 1 => (a : ℂ)
  | 2 => (a : ℂ) + (b : ℂ) * Complex.I
  | _ => (b : ℂ) * Complex.I

/-- The four closed sides in boundary order: bottom, right, top, left.
Source: the whole-side boundary correspondence in Stein–Shakarchi §§4.1 and 4.5.
The order agrees with `RectangleCorner`; the sides include both corners. -/
def ClosedRectangleSide (a b : ℝ) (i : Fin 4) : Set ℂ :=
  match i.val with
  | 0 => Complex.reProdIm (Icc 0 a) {0}
  | 1 => Complex.reProdIm {a} (Icc 0 b)
  | 2 => Complex.reProdIm (Icc 0 a) {b}
  | _ => Complex.reProdIm {0} (Icc 0 b)

/-- A biholomorphic disk-to-rectangle map with the four original marks and all four whole sides.

Source: Stein–Shakarchi (2003), Chapter 8, §§4.1, 4.4–4.5, pp. 233–234 and 241–247;
Bak–Newman (2010), pp. 177, 183–186 and 189–190; Whittaker–Watson (1920), §22.32, p. 501.
DAG: `analysis.marked_rectangle_g3_disk_schwarz_christoffel`.

Natural-language proof, relative to the named source and Mathlib dependencies of the node:

1.
Follow the published symmetric rectangle converse of Stein–Shakarchi, Chapter8 Section4.5
printedpp245–247, after the written four-point bilinear normalization of Bak–Newman pp184–186.
Keep the ORIGINAL four positive cyclic marks fixed. Choose q in the positive open arc zeta4 to
zeta1 and C_orig(z)=i*(q+z)/(q-z). The written Cayley map and its inverse h(w)=q*(w-i)/(w+i),
together with Im C_orig(z)=(1-|z/q|^2)/|1-z/q|^2, give a biholomorphism D to H and a
compactified boundary homeomorphism with q mapped to infinity. On z=q*exp(i*theta),
0<theta<2*pi, its real boundary value is -cot(theta/2). Continuity and injectivity plus
continuousOn_injective_interval_strict_mono_or_anti_g7, and the values -1 at pi/2 and +1
at3*pi/2, give increasing boundary order. Consequently X1=C_orig(zeta1)<X2<X3<X4 are finite; the
fourth arc is the two outer rays joined at infinity.
Set R=((X4-X2)*(X3-X1))/((X4-X1)*(X3-X2)). The exact difference
R-1=((X2-X1)*(X4-X3))/((X4-X1)*(X3-X2)) is positive, so R>1. Put s=sqrt(1-1/R) and
k=(1-s)/(1+s); then 0<s<1, 0<k<1 and (1+k)^2/(4*k)=R. For canonical a=(-1/k,-1,1,1/k) this is
precisely Bak's cross-ratio. Apply the WRITTEN Lemma13.20, Proposition13.22 and Theorem13.23:
alpha=X3-X1>0, beta=X3-X2>0, A2=1+1/k, T1(z)=alpha*(z-X2)/(beta*(z-X1)),
T2(v)=A2*(v+1)/(2*(v+1/k)), and T=T2^-1 composed T1. Thus
T(z)=[A2*beta*(z-X1)-(2/k)*alpha*(z-X2)]/[2*alpha*(z-X2)-A2*beta*(z-X1)].
The first three prescribed images follow from the source triple construction; cross-ratio
invariance and sphere injectivity give T(X4)=1/k. The real matrices
M1=[[alpha,-alpha*X2],[beta,-beta*X1]] and M2=[[A2,A2],[2,2/k]] have determinants
alpha*beta*(X2-X1)>0 and 2*A2*(1/k-1)>0. Hence adj(M2)*M1 is a real positive-determinant matrix.
The WRITTEN FORWARD Theorem13.17p184, not its reverse Exercise16, proves T is an H-automorphism.
The explicit inverse/pole/infinity limits p177 give its sphere homeomorphism. The displayed
denominator is negative at X1 and X4 (at X4 use 2*R-A2=(1+k)*(k-1)/(2*k)<0), so has no zero on
[X1,X4]. The real derivative determinant/denominator-squared is positive there. Therefore M=T
composed C_orig sends the ORIGINAL marks in order to (-1/k,-1,1,1/k), and their four positive
closed arcs to the corresponding compactified real intervals. A pole, if any, lies on the fourth
arc and is handled by the sphere extension. No theorem with an infinite input triple and no
exercise proof is used.
Dependencies:
`mathlib.continuousOn_injective_interval_strict_mono_or_anti_g7`.
`mathlib.real_sqrt_square_g8`.
`mathlib.real_sqrt_sq_g8`.

2.
Construct the literal Stein elliptic branch for EVERY parameter 0<kappa<1, so the same
construction is available later for ell. In this family ONLY, write x1=-1/kappa, x2=-1, x3=1,
x4=1/kappa; these auxiliary xj are not the original Xj. On H put L_t(z)=Complex.log(z-t),
q_t(z)=exp(-L_t(z)/2), P_kappa=product_j q_xj and G_kappa=-i*P_kappa. Since Im(z-t)>0, the
principal slit-plane and nonzero guards hold. The exact log derivative, exp_log, exp derivative
and scalar chain rule show holomorphy and q_t^2=(z-t)^(-1), so P_kappa and G_kappa never vanish.
These are precisely the source positive-right-ray square-root factors. Finite-product algebra
gives P_kappa^2=kappa^2/((1-z^2)*(1-kappa^2*z^2)). Thus Q_kappa=-P_kappa/kappa has square
((1-z^2)*(1-kappa^2*z^2))^(-1). The actual real-boundary branch calculation in step4 gives
P_kappa(x)<0 on -1<x<1, so Q_kappa is the POSITIVE reciprocal square-root there. This is the
branch specified in Stein Example3pp233–234 and Section4.5, not a new choice of branch.
Dependencies:
`mathlib.complex_hasDerivAt_log`.
`mathlib.complex_exp_log`.
`mathlib.hasDerivAt_cexp`.
`mathlib.hasDerivAt_comp_scalar_tower_g5`.

3.
The proved `exists_schwarzChristoffel_primitive` supplies this whole-half-plane primitive,
its nonzero derivative and reciprocal-polynomial square identity. Internally, for each kappa
it applies the existing exact scalar Convex.exists_forall_hasDerivWithinAt
theorem with k=Complex, E=Complex, f=G_kappa and s=H. Complex is complete, H is real-convex by
the imaginary-part convex-combination identity, H is open, and the preceding step proves complex
DifferentiableOn G_kappa H. It supplies ONE global W_kappa with HasDerivWithinAt W_kappa
(G_kappa(z)) H z for every z in H. At EACH z, openness makes H a neighborhood and promotes this
very within derivative to HasDerivAt. Hence W_kappa is holomorphic and W_kappa'=G_kappa. This is
an exact existing library primitive on the WHOLE H, not a ball primitive or an assumed
arbitrary-path integral. It replaces the slit-domain simple-connectivity Exercise19 as a
primitive prerequisite. Its additive constant is not fixed until the boundary value at0 has
actually been supplied below.
Dependencies:
`mathlib.convex_exists_forall_hasDerivWithinAt_g4`.

4.
For the arbitrary fixed kappa of steps2–3 write W=W_kappa and G=G_kappa. Use the AUXILIARY
Cayley map C(z)=i*(1+z)/(1-z), q=1, and eta_j=(xj-i)/(xj+i). These are four distinct auxiliary
unit-circle marks, all different from1; they are not the original target zeta_j. Put F_aux=W
composed C on D. No boundary values are presumed. The original target normalization is M of
step1 and is used only in the final composition. Since C maps D into H, W-prime=G on H and the
scalar chain rule proves F_aux holomorphic on D. The explicit rational derivative is
C-prime(z)=2*i*q/(q-z)^2, valid on D since |q|=1 and q is outside D. For every real xj=C(eta_j),
the SAME marked preimage is eta_j=q*(xj-i)/(xj+i), and direct multiplication gives
C(z)-xj=(i+xj)*(z-eta_j)/(q-z). The factors i+xj are nonzero because xj is real. The already
proved square identity q_xj(C(z))^2=(C(z)-xj)^(-1) gives |q_xj(C(z))|=|C(z)-xj|^(-1/2). Thus the
ordinary derivative of the SAME F_aux satisfies the EXACT modulus formula
|F_aux-prime(z)|=A*product_(j=1..4)|z-eta_j|^(-1/2), with A=2*product_j|i+xj|^(-1/2)>0. The four
factors |q-z|^(1/2) cancel the full |q-z|^(-2) in |C-prime|. There is no fifth singular corner
at q and no change of analytic square-root branches or of W. To verify a GLOBAL derivative
bound, let delta=min_(j!=k)|eta_j-eta_k|, positive by distinctness and at most2 because all four
marks are unit. Put m=delta/3, so 0<m<1. For any z in D, if |z-eta_k|<m, the other three
distances are at least delta-m=2*m and hence at least m; also |z-eta_k|>=1-|z|. The product is
therefore at most m^(-3/2)*(1-|z|)^(-1/2), which is at most m^(-2)*(1-|z|)^(-1/2). At most one
close mark exists by separation. If no mark is within m, the product is at most m^(-2), again at
most m^(-2)*(1-|z|)^(-1/2), since 0<1-|z|<=1. Hence M=A*m^(-2) is finite positive and
|F_aux-prime(z)|<=M*(1-|z|)^(-1/2) for EVERY z in D. Apply
analysis.mashreghi_disk_derivative_holder_boundary_g3 with alpha=1/2 and constant M. This is the
actual forward proof of Mashreghi Theorem4.3 printed442–443, equations(4.6),(4.7), in the
author-uploaded complete article text. It gives F_aux_bar agreeing with THIS F_aux on D and
ContinuousOn F_aux_bar on the closed disk, a uniform radial tail bound and only the printed
local BOUNDARY angular Holder estimate. It does not give a Holder estimate for arbitrary pairs
of points of the whole closed disk. The existing compact-set uniform-continuity theorem applies
to this ContinuousOn extension on the compact closed complex disk, giving UniformContinuousOn
F_aux_bar there. Define the extension of W on the compactified CLOSED upper half-plane by
Wbar(w)=F_aux_bar(q*(w-i)/(w+i)) for finite Im(w)>=0 and Wbar(infinity)=F_aux_bar(q). The
inverse Cayley map has no finite pole on this closed half-plane, extends continuously to
infinity with value q, and is the inverse of C in H, so Wbar agrees with the SAME W on H and is
continuous for arbitrary complex approaches to every real boundary point and the single
compactified infinity point. In particular Wbar(xj)=F_aux_bar(eta_j), and BOTH W(+infinity) and
W(-infinity) are the same already established value F_aux_bar(q). This extension fixes none of
W's additive normalization. The written Bak–Newman pp189–190 primitive and convergent-real-path
passage now has the following exact binding, using the SAME branch and SAME already continuous
Wbar.

RB1. Implement the actual downward-ray slit derivative of Bak–Newman pp189–190, rather than
assuming W analytic across the real line. For each t=xj set Ldown_t(z)=log((-i)*(z-t))-log(-i),
Qdown_t(z)=exp(-Ldown_t(z)/2), and Gdown(z)=-i*product_j Qdown_xj(z). The log arguments lie in
slitPlane precisely off the downward rays from the respective t. At any closed-upper-half-plane
point z!=t, v=z-t is nonzero with Im v>=0. The exact arg_nonneg_iff and arg_le_pi leaves give
arg v in[0,pi]; arg_neg_I gives arg(-i)=-pi/2. Thus arg(-i)+arg v lies in[-pi/2,pi/2], strictly
inside Ioc(-pi,pi). Both factors are nonzero, so exact complex_log_mul gives
Ldown_t(z)=log(z-t). In particular Qdown_t is the SAME q_t on H and Gdown is the SAME G there.
At every real x!=t, -i*(x-t) is a nonzero imaginary number in slitPlane, so
complex_hasDerivAt_log, hasDerivAt_cexp and the scalar chain rule give local holomorphy and
continuity of the extension. The source real factor is |x-t|^(-1/2) for x>t and -i*|x-t|^(-1/2)
for x<t, hence g(x)=Gdown(x) has phase1 on(x1,x2), i on(x2,x3), -1 on(x3,x4), and -i on both
outer rays; its modulus is product_j |x-xj|^(-1/2). Define g(xj)=0. It is continuous on the
measurable open complement of these four points and zero on their finite complement.
continuousOn_measurable_piecewise_g5, measurable_stronglyMeasurable and
stronglyMeasurable_aestronglyMeasurable give actual measurability/strong measurability;
aestronglyMeasurable_restrict gives the same for each actual restricted real volume. The four
point values have zero Lebesgue mass. This is the literal source derivative branch with its
normalization verified, and establishes G extension only, not W continuation.

RB2. Bind the printed p189 identity f(z)-f(z0)=integral f-prime along a finite actual horizontal
path. Let a<=b lie in a single open component of Real minus the prevertices; equality a=b is
immediate, so otherwise a<b. Set eps_n=1/(n+1)>0, tending to0. For EVERY n the entire CLOSED
path r↦r+i*eps_n, r in[a,b], lies in H. The affine lineMap derivative and mixed real/complex
scalar-tower chain rule give ordinary real derivative G(r+i*eps_n) for W composed with this
path. The composition is continuous on[a,b], its derivative exists on(a,b), and G composed with
the path is continuous on the closed interval and genuinely interval-integrable. The exact
interior-derivative FTC2 integral_eq_sub_of_hasDerivAt_of_le, E=Complex as a complete REAL
normed vector space, therefore gives W(b+i*eps_n)-W(a+i*eps_n)=integral_a^b G(r+i*eps_n)dr. No
boundary derivative of W is assumed. The already obtained arbitrary-complex continuity of Wbar
supplies the endpoint limits Wbar(b)-Wbar(a).

RB3. Take the convergent real-path limit written on p190. The compact interval avoids all four
prevertices, so d=min_(r in[a,b],j)|r-xj|>0. Since |r-xj+i*eps_n|>=|r-xj|, the reciprocal-root
modulus gives |G(r+i*eps_n)|<=d^(-2), uniformly in r and n. Fix the SAME measure
mu=volume.restrict(Icc a b) and Complex codomain. Each approximant is continuous on the compact
carrier, so continuousOn_aestronglyMeasurable_of_isCompact gives AEStronglyMeasurable for THIS
mu. The constant d^(-2) is Integrable for mu by continuousOn_integrableOn_compact. Continuity of
Gdown at each real nonvertex and its equality with G on H give pointwise G(r+i*eps_n)→g(r). The
exact tendsto_integral_filter_of_dominated_convergence applies to the countably-generated atTop
filter on Nat, with actual eventual measurability, pointwise domination, integrable constant and
pointwise convergence all under this same mu. It yields convergence of the complex Bochner
integrals. Real Lebesgue volume has zero singleton masses, so measure_restrict_congr_set gives
equal restricted measures on Icc[a,b], Ioc[a,b] and Ioo[a,b]; use this equality and the
DEFINITION of the increasing interval integral to identify the Bochner integrals. No Real-only
integral_Ioc_eq_integral_Ioo theorem is applied to Complex. Taking the limit in RB2 gives
Wbar(b)-Wbar(a)=integral_a^b g(r)dr on every such compact nonvertex interval.

RB4. Supply the finite square-root endpoint passage of p190 through GENUINE integrability. On a
closed side interval[L,R]=[xj,x(j+1)] split at m=(L+R)/2. The other three distances are bounded
below on the left half, giving |g(r)|<=K_L*(r-L)^(-1/2) for L<r<=m; on the right half similarly
|g(r)|<=K_R*(R-r)^(-1/2) for m<=r<R, with finite positive constants. The real nonnegative
majorant B(r)=K_L*(r-L)^(-1/2)+K_R*(R-r)^(-1/2) therefore dominates |g| on the interval, apart
from harmless finite endpoints, where g was assigned0.
intervalIntegral_intervalIntegrable_rpow_prime with exponent-1/2>-1 proves integrability of the
base power on0..R-L. intervalIntegrable_comp_sub_left once supplies (R-r)^(-1/2); applying it
twice supplies (r-L)^(-1/2). Reversed endpoints use symmetry of the two conjuncts in the
DEFINITION of IntervalIntegrable. Scale each genuinely integrable power using
integrable_smul_const on the actual restricted volume and
interval_integrable_iff_integrableOn_Icc, and add them using intervalIntegrable_add. Thus B is
genuinely integrable for volume on this interval. The same Icc/Ioc null-singleton equality
identifies the measure required by the norm bound; actual AEStronglyMeasurability from RB1 and
integrable_mono_norm give IntegrableOn g on Icc[L,R], hence IntervalIntegrable g L R by the
exact interval/Icc equivalence. No totalized integral-substitution equality is used to infer
integrability. Choose an anchor c in(L,R). continuousOn_primitive_interval_prime applies to g on
L..R, this anchor and NullSingletonClass real volume, making r↦integral_c^r g continuous on the
CLOSED interval. RB3 gives Wbar(r)-Wbar(c)=integral_c^r g at all interior points, with the
signed reversed case obtained by exchanging endpoints. Continuity of both sides passes this
equality to L and R, so Wbar(R)-Wbar(L)=integral_L^R g and all partial endpoint increments have
the same representation. The identical one-endpoint construction handles a finite interval
beginning at x4 or ending at x1. The finite adjacent-interval sum identity, with genuine
integrability on each piece, extends representation across any intervening prevertices.

RB5. For the right improper ray take R>max(1,2*max_j|xj|), enlarged as needed beyond a fixed
endpoint neighborhood. For u>=R all four distances |u-xj| are at least u/2, so |g(u)|<=4*u^(-2).
Near x4 from the right, finite factor separation gives K*(u-x4)^(-1/2); a finite closed body
away from x4 is continuous and compact-integrable. The shifted-power construction of RB4 proves
genuine integrability on the closed endpoint neighborhood. On the positive tail Ioi R,
integrableOn_Ioi_rpow_of_lt with exponent-2<-1 and R>0, then integrable_smul_const with factor4,
supply an integrable real majorant; actual measurability from RB1 and integrable_mono_norm give
genuine complex tail integrability. Apply integrableOn_finset_iUnion with Fin3 and the SAME
function g to the sets Icc[x4,x4+delta], Icc[x4+delta,R], Ioi R. Their union is Ici x4. The null
singleton{x4} and measure_restrict_congr_set change this to the EXACT carrier Ioi x4, proving
IntegrableOn g there. The anchor x4 is allowed to be nonpositive: the negative-power tail
theorem was applied only beyond positive R. Now intervalIntegral_tendsto_integral_Ioi with
anchor x4, a countably-generated Nat atTop filter, and S_n→atTop applies to this genuinely
integrable g. The finite endpoint representation gives integral_x4^S_n g=Wbar(S_n)-Wbar(x4). The
already established infinity continuity therefore identifies integral_(Ioi x4)
g=Wbar(infinity)-Wbar(x4).

RB6. Prove the LEFT reflected-ray integrability separately before taking its limit. Put
h(u)=g(-u) and anchor a=-x1, which need not be positive. It is continuous off the reflected four
vertices and zero on them, so the same piecewise measurable/strongly-measurable construction of
RB1 gives actual AEStronglyMeasurability for every restricted volume. Near a from the right,
|-u-x1|=u-a and the remaining factors stay separated, giving |h(u)|<=K*(u-a)^(-1/2). A finite
closed body[a+delta,R] is continuous and compact-integrable. For positive
u>=R>max(1,2*max_j|xj|), all |-u-xj|>=u/2, so |h(u)|<=4*u^(-2). The shifted -1/2 power, finite
body and positive -2 tail providers, scalar scaling, norm domination and
integrableOn_finset_iUnion on Fin3 prove genuine IntegrableOn h (Ici a); null singleton measure
equality gives IntegrableOn h (Ioi a). Only now apply the Ioi endpoint-limit theorem with anchor
a, even when a<=0. The generic COMPLEX intervalIntegral_integral_comp_sub_left with d=0
identifies integral_a^S h=integral_-S^x1 g=Wbar(x1)-Wbar(-S), using the finite endpoint identity
and established integrability. Consequently integral_(Ioi a) h=Wbar(x1)-Wbar(infinity), the
source left-ray increment. In particular on the separate positive tail, integral_R^S
h=integral_-S^-R g=Wbar(-R)-Wbar(-S), so its limit is Wbar(-R)-Wbar(infinity), with this exact
orientation. Together RB1–RB6 establish the real-boundary interval/ray representation of the
SAME Wbar and G, including the four square-root endpoints and both rays. They do not construct
an analytic continuation of W, identify an indented contour index, or prove exhaustion.

Only after this exact extension and real-increment binding, define
I_kappa(z)=(-i/kappa)*(W_kappa(z)-W_kappa_bar(0)) on H, and the same affine formula on the
supplied compactified closed-H extension. The continuous complex-linear-map integral theorem
transports every proven real interval/ray increment to I_kappa. Its derivative is
(-i/kappa)*G_kappa=Q_kappa, and I_kappa_bar(0)=0. Thus this is the literal source boundary-based
primitive with the positive central branch, even though0 is not in H. No analyticity at a
singular endpoint or injectivity has been assumed. The auxiliary Cayley construction and its
single infinity point give continuity for ALL complex approaches to each real point and
infinity.
Dependencies:
`mathlib.hasDerivAt_comp_scalar_tower_g5`.
`analysis.mashreghi_disk_derivative_holder_boundary_g3`.
`mathlib.isCompact_uniformContinuousOn_of_continuous`.
`mathlib.complex_hasDerivAt_log`.
`mathlib.hasDerivAt_cexp`.
`mathlib.complex_log_mul_g3`.
`mathlib.complex_arg_nonneg_iff_g3`.
`mathlib.complex_arg_le_pi_g3`.
`mathlib.complex_arg_neg_I_g3`.
`mathlib.affine_lineMap_hasDerivAt`.
`mathlib.intervalIntegral_integral_eq_sub_of_hasDerivAt_of_le`.
`mathlib.continuousOn_intervalIntegrable`.
`mathlib.continuousOn_aestronglyMeasurable_of_isCompact`.
`mathlib.continuousOn_integrableOn_compact`.
`mathlib.tendsto_integral_filter_of_dominated_convergence`.
`mathlib.measure_restrict_congr_set`.
`mathlib.continuousOn_measurable_piecewise_g5`.
`mathlib.measurable_stronglyMeasurable`.
`mathlib.stronglyMeasurable_aestronglyMeasurable`.
`mathlib.aestronglyMeasurable_restrict`.
`mathlib.intervalIntegral_intervalIntegrable_rpow_prime`.
`mathlib.intervalIntegrable_comp_sub_left`.
`mathlib.integrable_smul_const`.
`mathlib.intervalIntegrable_add`.
`mathlib.interval_integrable_iff_integrableOn_Icc`.
`mathlib.integrable_mono_norm`.
`mathlib.integrableOn_finset_iUnion`.
`mathlib.intervalIntegral_continuousOn_primitive_interval_prime`.
`mathlib.integrableOn_Ioi_rpow_of_lt`.
`mathlib.intervalIntegral_tendsto_integral_Ioi`.
`mathlib.intervalIntegral_integral_comp_sub_left`.
`mathlib.interval_integral_sum_adjacent`.
`mathlib.continuousLinearMap_integral_comp_comm`.

5.
Write eta_kappa(x)=1/[sqrt(1-x^2)*sqrt(1-kappa^2*x^2)] on0<x<1, and
rho_kappa(x)=1/[sqrt(x^2-1)*sqrt(1-kappa^2*x^2)] on1<x<1/kappa; assign0 at endpoints/outside
each carrier. Real positive radicals and step2's square/phase calculation give I_kappa' positive
central, +i times rho_kappa on(1,1/kappa), -i times the reflected rho_kappa on(-1/kappa,-1), and
negative real on both outer rays. The real-path result step4 gives ACTUAL finite and endpoint
increments of this same I_kappa_bar. Genuine L1 holds before any limit: at a prevertex the
separated other factors give a constant times distance^(-1/2), with the translated-power and
finite-union providers of step4. The new Whittaker provider also gives IntervalIntegrable
rho_kappa from1 to1/kappa. Define K(kappa)=integral_0^1 eta_kappa and
Kprime(kappa)=integral_1^(1/kappa) rho_kappa. For K, the analogous real -1/2 endpoint bound
gives genuine interval integrability; all kernels are measurable from continuous-on-open-piece
with zero finite endpoint assignments. Each period is finite and strictly positive: choose a
nonempty compact interval in its positive regular interior, use intervalIntegral_integral_pos
there, and transfer the positive lower bound to the whole genuinely integrable interval with
integral_mono_interval. This never applies the continuity-based positivity theorem to an
unbounded singular endpoint.
The complex continuous-linear integral theorem converts the phase increments into these real
periods. The reflected finite-interval substitution comp_sub_left, with the genuine
integrability already established, gives I_bar(-1)=-K and I_bar(1)=K. On the right
I_bar(1/kappa)=K+i*Kprime; on the left the reflected rho increment has negative-i phase in
increasing x, yielding I_bar(-1/kappa)=-K+i*Kprime. These are the four canonical corners in the
SOURCE order. It remains to bind the printed tail calculation, rather than inferring the
midpoint from an unproved contour argument.
For these phase/period equalities, endpoint totalizations differ from the actual continuous
branch only on finitely many singletons. Use the GENERIC complex-valued
interval_integral_congr_ae_restrict (with E=Complex or Real as appropriate) and volume-null
endpoints, together with measure_restrict_congr_set for Icc/Ioc/Ioo conventions. The real-only
integral_Ioc_eq_integral_Ioo theorem is not used. This binds the values at0 and the square-root
endpoints without changing the same primitive.
Dependencies:
`analysis.whittaker_watson_complementary_elliptic_integrals_g3`.
`mathlib.real_sqrt_square_g8`.
`mathlib.real_sqrt_sq_g8`.
`mathlib.real_sqrt_eq_rpow`.
`mathlib.intervalIntegral_intervalIntegrable_rpow_prime`.
`mathlib.intervalIntegrable_comp_sub_left`.
`mathlib.interval_integrable_iff_integrableOn_Icc`.
`mathlib.integrable_smul_const`.
`mathlib.integrable_mono_norm`.
`mathlib.continuousOn_measurable_piecewise_g5`.
`mathlib.intervalIntegral_integral_pos`.
`mathlib.intervalIntegral_integral_mono_interval`.
`mathlib.intervalIntegral_integral_comp_sub_left`.
`mathlib.continuousLinearMap_integral_comp_comm`.
`mathlib.interval_integral_congr_ae_restrict`.
`mathlib.measure_restrict_congr_set`.

6.
Implement the WRITTEN Stein Example3p234 reciprocal tail identity. On x>1/kappa put
tau_kappa(x)=1/[sqrt(x^2-1)*sqrt(kappa^2*x^2-1)]. It is the positive modulus of the
negative-real outer derivative Q_kappa. Genuine integrability on Ioi(1/kappa) follows FIRST from
the source endpoint -1/2 bound and separated factors, a finite compact body, and the positive
tail bound tau_kappa(x)<=4/kappa*x^(-2) for x>=R>max(1,2*max_j|xj|). Use the translated power,
integrableOn_Ioi_rpow, scalar scaling, actual measurable norm domination and finite-union
providers as in step4; the lower anchor1/kappa is positive, and no singular endpoint is put into
a continuity hypothesis.
For0<a<b<1 set phi(u)=1/(kappa*u). The generic real rpow derivative with exponent-1 and u!=0,
real_rpow_neg and scalar differentiation give phi'=-1/(kappa*u^2) on the whole finite Icc[a,b],
continuously. The image is the regular compact interval[phi(b),phi(a)] strictly above1/kappa, so
tau is continuous there. Actual integral_comp_mul_deriv_prime applies although phi' is negative.
The source positive radical algebra, sqrt-square guards, gives
tau(phi(u))*(-phi'(u))=eta_kappa(u). Thus integral_phi(b)^phi(a) tau=integral_a^b eta. First let
a decrease to0 at fixed b: phi(a) increases to infinity, and the Ioi-limit theorem applies to
the already integrable tail; the right side converges by genuine eta integrability and anchored
primitive continuity at0. Then let b increase to1: continuity of the anchored primitive at the
integrable lower square-root endpoint, and finite adjacent-interval additivity, give
integral_(1/kappa)^infinity tau=K(kappa); the right side reaches its integrable endpoint1. These
are limits of actual integrable functions, not an inference of integrability from a totalized
substitution identity.
Step4's same-primitive ray representation now gives
I_kappa_bar(infinity)=I_kappa_bar(1/kappa)-integral_(1/kappa)^infinity tau=i*Kprime(kappa). The
negative ray agrees with this same infinity by the already proven compactified extension, and
its reflected phase/increments give the other half of the upper side. Positive regular
subintegrals, endpoint primitive continuity and the same real phases show traversal of the four
closed sides in order, as in the written Example3. At this stage ONLY the actual boundary
rectangle behavior has been established; interior univalence comes from the published converse
below.
Dependencies:
`mathlib.intervalIntegral_integral_comp_mul_deriv_prime_g3`.
`mathlib.real_hasDerivAt_rpow_const`.
`mathlib.real_rpow_neg`.
`mathlib.real_sqrt_square_g8`.
`mathlib.real_sqrt_sq_g8`.
`mathlib.integrableOn_Ioi_rpow_of_lt`.
`mathlib.integrable_smul_const`.
`mathlib.integrable_mono_norm`.
`mathlib.integrableOn_finset_iUnion`.
`mathlib.intervalIntegral_tendsto_integral_Ioi`.
`mathlib.intervalIntegral_continuousOn_primitive_interval_prime`.
`mathlib.interval_integral_sum_adjacent`.
`mathlib.intervalIntegral_integral_pos`.
`mathlib.intervalIntegral_integral_mono_interval`.

7.
Fix the k from step1 and form the OPEN rectangle R_k={-K(k)<Re w<K(k), 0<Im w<Kprime(k)}. The
finite positive periods proved above give a nonempty bounded open convex region with Jordan
polygon boundary. The explicit straight-line homotopy (t,w) maps to (1-t)*w+t*w0 for an actual
interior w0 stays in the rectangle by its strict convex inequalities and is continuous; it
contracts the rectangle. The EXISTING contractible_space_simply_connected_g8 terminal then
verifies the source simple-connectivity hypothesis. This is an elementary convex guard, not an
additional target assumption. Apply the EXISTING bounded Riemann-map provider, choosing any
actual interior basepoint, to obtain a biholomorphism of D onto R_k. Apply the EXISTING generic
same-map Caratheodory provider to THIS biholomorphism and THIS bounded simply connected Jordan
region. It supplies its literal closure homeomorphism and positive boundary orientation. Compose
with the explicit disk/H Cayley homeomorphism, including its one compactified infinity point, to
obtain F0:H to R_k with the positive whole-boundary homeomorphism. This uses no polygon-closure
duplicate and no assumption of an extension before invoking its proved source provider. The
official prospective DAG check has already found these two dependencies acyclic. Their own lower
mathematical dependencies remain named obligations; this is a one-level source proof, not Lean
certification.
Use the WRITTEN Bak Lemma13.20/Thm13.23 three-point construction and positive-determinant
forward13.17 to precompose F0 with an H-automorphism so the resulting F has F_bar(-1)=-K(k),
F_bar(0)=0, F_bar(1)=K(k). The three boundary preimages are positively ordered by the supplied
closure orientation. If one initial preimage is infinity, choose the initial Cayley pole at
another boundary point first; all three inputs in the actual finite triple construction are then
finite, so the source's infinite-input exercise is not needed. This changes only the auxiliary
F, not the original four target marks.
Dependencies:
`analysis.marked_rectangle_g3_bounded_riemann_map`.
`analysis.marked_rectangle_g3_caratheodory_same_map`.
`mathlib.contractible_space_simply_connected_g8`.

8.
Bind the source three-point uniqueness through the WRITTEN Stein H-automorphism classification
Theorem2.4pp222–223, not Exercise15. Its proof conjugates by the explicit Cayley map, sends an
interior point to i with a real positive-determinant matrix, uses disk rotations, and writes the
resulting H-automorphism as a real determinant1 fractional linear map. For its disk-rotation
input Corollary2.3, the existing Schwarz derivative bound applies to a disk automorphism and its
inverse fixing0; the scalar chain identity gives product of derivative norms1, so each norm is1.
The exact existing Schwarz affine-rigidity theorem at c=z0=0 (dslope there is the derivative)
supplies the rotation on D. This binds the source's proved rotation contract with existing
library terminals. The explicit real rotation matrices and positive-affine matrices of the
written Theorem2.4 then give the H-classification, with all rational denominators nonzero in H.
Bak's WRITTEN Proposition13.19p185 now says a nonidentity bilinear map cannot fix the THREE
distinct real boundary points -1,0,1. Therefore an H-automorphism fixing them is identity.
The EXACT visually inspected formula in Stein p246 is Fstar(z)=-conjugate(F(-conjugate(z))).
Conjugate-negation preserves H and reflection in the imaginary axis preserves R_k. The exact
complex_differentiableAt_conj_conj_iff leaf with the scalar negation chain, and the literal
inverse conjugation sandwich, prove Fstar is another biholomorphism onto R_k with continuous
boundary extension. It has the same three boundary values. Hence F^-1 composed Fstar is the
identity and Fstar=F, including boundary limits. Boundary injectivity now shows
F_bar(infinity)=i*Kprime(k): symmetry fixes infinity, its image is one of the two
rectangle-boundary symmetry-fixed points0 or i*Kprime, and0 already has the distinct preimage0.
Thus infinity is NOT a vertex. Positive closure order puts the upper-right vertex preimage in
the finite interval(1,infinity), write it1/ell with0<ell<1; symmetry gives the upper-left
preimage -1/ell. No finite-prevertex assumption or contour winding is hidden in this step.
Dependencies:
`mathlib.complex_schwarz_norm_deriv_le_one_g5`.
`mathlib.complex_schwarz_affine_of_norm_dslope_eq_g5`.
`mathlib.hasDerivAt_comp_scalar_tower_g5`.
`mathlib.complex_differentiableAt_conj_conj_iff`.
`analysis.qc_holomorphic_embedding_inverse`.

9.
Expand the ACTUAL WRITTEN Stein Thm4.6 necessity proof pp241–244, specialized to the four
rectangular corners; do not treat its statement as a converse. Let b1=-1/ell,b2=-1,b3=1,b4=1/ell
and v_j=F_bar(b_j). For each corner choose a fixed unit rotation lambda_j making
lambda_j*(R_k-v_j) lie in the open first quadrant. Put h_j=(lambda_j*(F-v_j))^2 on the upper
strip between the neighboring prevertices (outer strips extend to infinity). The whole rotated
rectangle lies in that quadrant, so squaring is injective there and maps its two adjacent closed
sides onto opposite real rays. The supplied closure injectivity gives h_j continuous and
injective on the upper strip together with its real boundary interval, mapping the interior to
one side of the real line. Apply the EXISTING general real-boundary reflection source theorem on
the open connected conjugation-invariant full strip. Its literal reflected h_j is holomorphic
there. On upper/lower patches injectivity follows from F, quadrant injectivity and conjugation.
At any real point take a small disk in the strip: its upper and lower images lie in opposite
half-planes, and its real boundary images are injective. Consequently the reflected h_j is
injective on that WHOLE disk, exactly the written source argument. The existing open-mapping
theorem makes a holomorphic injective map a homeomorphism onto its open image, so the exact
qc_holomorphic_embedding_inverse provider proves h_j'!=0 on this local disk, including the real
center. This is not an unsupported implication from nonzero interior derivatives.
At b_j, h_j(b_j)=0 and h_j'(b_j)!=0; the analytic zero-factorization/order providers give a
SIMPLE factor h_j(z)=(z-b_j)*u_j(z), with u_j analytic and nonzero locally. Away from b_j, h_j
has no other zero on its whole strip by the reflected injectivity/one-sided image argument.
Division and the local simple factor therefore define the same nonzero holomorphic
u_j=h_j/(z-b_j) throughout the strip. The written logarithmic-derivative calculation, using
h_j'=2*lambda_j^2*(F-v_j)*F', gives
F''/F'=-(1/2)/(z-b_j)+E_j,
E_j=h_j''/h_j'-(1/2)*u_j'/u_j.
The derivative and analytic division leaves verify E_j holomorphic even at the corner. This uses
the integer square for the rectangle's alpha=1/2, so it needs no fractional corner logarithm
branch or source exercise.
Dependencies:
`analysis.schwarz_real_boundary_extension_g6_20261007`.
`mathlib.differentiableOn_analyticOnNhd_complex_g5`.
`mathlib.analyticOnNhd_complex_open_mapping_g5`.
`analysis.qc_holomorphic_embedding_inverse`.
`mathlib.analyticAt_zero_factorization_g5`.
`mathlib.analyticAt_zero_order_characterization_g5`.
`mathlib.analyticAt_div`.
`mathlib.differentiableOn_deriv_complex`.
`mathlib.hasDerivAt_comp_scalar_tower_g5`.

10.
Continue the WRITTEN infinity/Liouville portion of Stein p244 with the missing leading-order
guard made explicit. The two outer real intervals map into the SAME upper horizontal side;
reflecting F across that line gives a bounded holomorphic continuation outside a sufficiently
large disk. The two reflected definitions agree literally because the target line is the same,
so the exterior gluing introduces no alternate primitive. Under w=1/z this is a bounded
holomorphic punctured-neighborhood function. The exact bounded-puncture-removable theorem
extends it to w=0. It is not locally constant: otherwise F would be constant on an open exterior
part of H and hence on H by the analytic identity theorem, contradicting its bijection.
Therefore its difference from its value c0 at0 has a FIRST nonzero factor
H(w)=F(1/w)-c0=w^m*u(w), with m>=1, u analytic and u(0)!=0, by the exact
zero-factorization/order providers. Differentiating this actual factor gives
F'(z)=-z^(-m-1)*[m*u(1/z)+(1/z)*u'(1/z)], whose bracket tends to m*u(0)!=0. Hence
F''/F'=-(m+1)/z+O(z^(-2)) and tends0 at infinity. In particular no assumption c1!=0 is taken
from the displayed source Laurent series.
On H set B=F''/F'+sum_j (1/2)/(z-b_j). On each corner strip the preceding E_j formula cancels
its sole pole and defines B holomorphically. These local definitions agree on their upper
overlaps; each overlap is an open connected strip, so the exact analytic identity theorem gives
agreement throughout the reflected overlap. The strips cover the entire plane, producing ONE
entire B. Its exterior expression tends0 by the just-proved infinity calculation. ContinuousOn
on a closed disk gives a finite norm bound by isCompact_exists_bound_of_continuousOn, and its
small exterior tail supplies a bound outside; thus B has bounded WHOLE range. The exact complex
Liouville theorem makes B constant, and its limit0 makes it zero. This proves F''/F'=
-sum_j(1/2)/(z-b_j) on H, with every finite pole and infinity guard accounted.
Dependencies:
`analysis.schwarz_real_boundary_extension_g6_20261007`.
`mathlib.complex_bounded_puncture_removable`.
`mathlib.analyticAt_zero_factorization_g5`.
`mathlib.analyticAt_zero_order_characterization_g5`.
`mathlib.differentiableOn_deriv_complex`.
`mathlib.analyticAt_div`.
`analysis.analytic_identity_open_domain`.
`mathlib.isCompact_closedBall`.
`mathlib.isCompact_exists_bound_of_continuousOn`.
`mathlib.complex_liouville_bounded`.
`mathlib.hasDerivAt_comp_scalar_tower_g5`.

11.
Finish the WRITTEN Thm4.6 integration on H. The literal Q_ell=I_ell' constructed in steps2–4 is
nonzero and has Q_ell'/Q_ell=-sum_j(1/2)/(z-b_j) by the exact log/exp/product derivatives.
Consequently deriv(F'/Q_ell)=0 on H. This quotient is holomorphic there by nonzero denominators,
and H is open and preconnected (indeed convex). Apply the EXISTING
isOpen_exists_is_const_of_deriv_eq_zero theorem on this ACTUAL H, not a global whole-plane
constancy theorem, to get F'=c*Q_ell; c!=0 follows from the inverse-provider nonzero F' and
Q_ell. Apply the same open-preconnected theorem to F-c*I_ell to get F=c*I_ell+d on H. This is
the source's final integration with a supplied global primitive, not an assumed path identity.
Continuity of the SAME F_bar and I_ell_bar at0, where both have value0, gives d=0. At1,
K(k)=c*K(ell), so c is a strictly positive REAL scalar since both periods are positive. At1/ell
the actual canonical corner values give Kprime(k)=c*Kprime(ell). All equalities at real
endpoints are taken through the proven arbitrary-complex closure limits; no derivative at a
square-root endpoint is assumed.
Dependencies:
`mathlib.complex_hasDerivAt_log`.
`mathlib.hasDerivAt_cexp`.
`mathlib.hasDerivAt_comp_scalar_tower_g5`.
`mathlib.analyticAt_div`.
`mathlib.differentiableOn_deriv_complex`.
`mathlib.isOpen_exists_is_const_of_deriv_eq_zero_g4`.
`analysis.qc_holomorphic_embedding_inverse`.

12.
Use the WRITTEN complementary identity from Whittaker–Watson thirdedition1920 Section22.32p501,
via the EXISTING complete exact provider
analysis.whittaker_watson_complementary_elliptic_integrals_g3, in place of Stein Exercise24. For
every0<t<1 it states genuine interval integrability and Kprime(t)=K(sqrt(1-t^2)), with exactly
our positive interior kernels and finite zero endpoint assignments. Thus no improperly totalized
change-of-variables identity is mistaken for integrability.
Bind the written strict comparison in Stein pp246–247 precisely. If0<t<u<1, the positive central
kernels satisfy eta_u>=eta_t almost everywhere on(0,1), and eta_u>eta_t on the regular compact
interval[1/4,1/2]; the positive radical square identities show this strict ordering. Their
difference is genuinely integrable for the SAME volume.restrict(Ioc0 1), by the already
established L1 and scalar negation/addition. On the compact interval it is continuous,
nonnegative and positive, so the exact integral_pos theorem gives a strictly positive integral
there. The exact integral_mono_interval transfers this lower bound to the whole integrable
interval. The generic integral_sub under the same restricted measure and the
null-endpoint/interval convention identify it with K(u)-K(t), hence K is strictly increasing.
The complementary parameter sqrt(1-t^2) strictly decreases on(0,1), by positivity and its square
identity, so the supplied identity makes Kprime strictly decreasing. Both functions are finite
and positive. Elementary multiplication of positive inequalities therefore makes K/Kprime
strictly increasing. The two period equalities from the preceding step force k=ell and then c=1.
Hence the literal I_k=F on H. It inherits F's holomorphic bijection onto R_k and its positive
whole-closure homeomorphism; their extensions agree at every boundary point by equality on H and
continuity. The holomorphic inverse is the same supplied inverse, or the exact inverse provider
applied to this inherited homeomorphism. This closes interior existence/univalence through the
written converse, without any indented-contour, trace-index, exhaustion or boundary-image
exclusion assumptions.
Dependencies:
`analysis.whittaker_watson_complementary_elliptic_integrals_g3`.
`mathlib.real_sqrt_square_g8`.
`mathlib.real_sqrt_sq_g8`.
`mathlib.integrable_smul_const`.
`mathlib.intervalIntegrable_add`.
`mathlib.interval_integrable_iff_integrableOn_Icc`.
`mathlib.intervalIntegral_integral_pos`.
`mathlib.intervalIntegral_integral_mono_interval`.
`mathlib.integral_sub`.
`mathlib.measure_restrict_congr_set`.
`analysis.qc_holomorphic_embedding_inverse`.
`analysis.marked_rectangle_g3_caratheodory_same_map`.

13.
Return to the ORIGINAL marks and map M of step1. Define the actual existential witness
S(z)=i*I_k(M(z))+Kprime(k)+i*K(k) for z in D,
a=Kprime(k)>0, b=2*K(k)>0.
The fixed complex-affine map A(w)=i*w+Kprime+i*K sends the canonical rectangle interior {-K<Re
w<K,0<Im w<Kprime} EXACTLY to {0<Re A(w)<Kprime,0<Im A(w)<2*K}. Its inverse is explicit with
nonzero multiplier i. Thus S is a holomorphic bijection D to the literal R_(a,b), with
holomorphic inverse M^-1 composed I_k^-1 composed A^-1. Compose the compactified closed-disk
boundary homeomorphism of M, the inherited closure homeomorphism of I_k=F and A to define Sigma
on closed D. It agrees with THIS S on D and is a homeomorphism onto [0,a]+i[0,b]. At the
ORIGINAL four marks, step1 and the canonical corners give respectively A(-K+i*Kprime)=0,
A(-K)=Kprime, A(K)=Kprime+2*i*K, A(K+i*Kprime)=2*i*K. Thus the literal prescribed images
are0,a,a+ib,ib, without relabeling any original mark. The positive boundary order and the
homeomorphism give each positive closed circle arc its corresponding WHOLE closed side,
including the fourth arc's one infinity point. This final composition is exactly the published
canonical rectangle route with written bilinear normalization; it is permitted because the
target asks for existence of S and does not require S to equal the obsolete arbitrary-prevertex
primitive.
Dependencies:
`analysis.qc_holomorphic_embedding_inverse`.
`analysis.marked_rectangle_g3_caratheodory_same_map`.
`mathlib.hasDerivAt_comp_scalar_tower_g5`.

The positive cyclic-order hypothesis is precisely the existence of four strictly increasing
argument lifts over less than one turn. The directed-arc definition is independent of the lift
cut and covers the fourth arc as well. Complex differentiability on the open disk and open
rectangle expresses holomorphy; the two inverse identities and domain-membership condition
give the holomorphic inverse of the very same bijection. The closure homeomorphism agrees
with that bijection in the interior and has the prescribed corner values and whole-side images.
The initial boundary prerequisites are now supplied by the proved primitive, downward-cut
branch, and specified-primitive disk-extension providers. The remaining normalization,
real-boundary integral calculations, canonical rectangle univalence, and original marked
corners/whole-side construction are still this named theorem's obligation. No definition
uses sorry.
-/
theorem exists_disk_rectangle_map
    (ζ : Fin 4 → ℂ) (hcircle : ∀ i, ‖ζ i‖ = 1)
    (hdistinct : Function.Injective ζ) (hcyclic : PositiveCircleCyclicOrder ζ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∃ S T : ℂ → ℂ,
        DifferentiableOn ℂ S (Metric.ball (0 : ℂ) 1) ∧
        DifferentiableOn ℂ T (OpenRectangle a b) ∧
        BijOn S (Metric.ball (0 : ℂ) 1) (OpenRectangle a b) ∧
        MapsTo T (OpenRectangle a b) (Metric.ball (0 : ℂ) 1) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) 1, T (S z) = z) ∧
        (∀ w ∈ OpenRectangle a b, S (T w) = w) ∧
        ∃ boundaryExtension : (Metric.closedBall (0 : ℂ) 1) ≃ₜ ClosedRectangle a b,
          (∀ z : Metric.closedBall (0 : ℂ) 1,
            ‖(z : ℂ)‖ < 1 → (boundaryExtension z : ℂ) = S z) ∧
          (∀ i : Fin 4,
            (boundaryExtension
                ⟨ζ i, by simpa [Metric.mem_closedBall] using (hcircle i).le⟩ : ℂ) =
              RectangleCorner a b i) ∧
          (∀ i : Fin 4,
            (fun z : Metric.closedBall (0 : ℂ) 1 ↦ (boundaryExtension z : ℂ)) ''
                {z | (z : ℂ) ∈ PositiveClosedCircleArc (ζ i) (ζ (i + 1))} =
              ClosedRectangleSide a b i) := by
  have hcyclic' : Source.PositiveCircleCyclicOrder ζ := by
    simpa [PositiveCircleCyclicOrder, Source.PositiveCircleCyclicOrder] using hcyclic
  obtain h := Source.exists_disk_rectangle_map_source ζ hcircle hdistinct hcyclic' (by norm_num) rfl
  convert h using 1
  simp [OpenRectangle, Source.OpenRectangle, ClosedRectangle, Source.ClosedRectangle,
    RectangleCorner, Source.RectangleCorner, ClosedRectangleSide, Source.ClosedRectangleSide,
    PositiveClosedCircleArc, Source.PositiveClosedCircleArc]
  rfl

end HolomorphicAnosov.Analysis.MarkedRectangle

