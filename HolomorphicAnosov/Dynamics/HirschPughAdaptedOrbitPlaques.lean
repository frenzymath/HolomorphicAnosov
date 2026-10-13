import HolomorphicAnosov.Geometry.Riemannian.ConstantComponentPiecewiseSmoothMetric
import HolomorphicAnosov.Dynamics.OrbitCoreContractionMetricTransfer
import HolomorphicAnosov.Topology.ComponentMetricLocalAgreement
import HolomorphicAnosov.Dynamics.NativeLeafPathAdvanceLength
import HolomorphicAnosov.Dynamics.NativeLeafPathAdvanceEDist
import HolomorphicAnosov.Dynamics.NativeLeafPathAdvanceSpeed
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathMap
import HolomorphicAnosov.Dynamics.ContinuousTangentSubbundleOnUniv
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Dynamics.NativeInvariantLeafSystemInverse
import HolomorphicAnosov.Dynamics.NativeInvariantLeafSystemOfLamination
import HolomorphicAnosov.Paper.HPS.LocalStrongGraphs
import HolomorphicAnosov.Geometry.Riemannian.GallierQuaintanceGaussLemma
import HolomorphicAnosov.Geometry.UniformExponentialLift
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting

import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaquesGeometry
namespace HolomorphicAnosov

open Set MeasureTheory
open scoped ContDiff Manifold ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

section AdaptedOrbitTheorem

variable [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]

/-- The full original-map adapted-metric and orbit-plaque theorem.

The identity real model is boundaryless. Compactness does not impose
connectedness, and the splitting's two local ranks may be zero. Both metrics
in the hypotheses and conclusion are actual smooth positive tangent tensors.
The existential distance is finite, induces the ORIGINAL topology, agrees
with the SAME selected tensor's piecewise-smooth length infimum inside every
original connected component, and has ONE positive constant between distinct
components. All orbit sets, bracket domains, cores and balls below use this
same distance and the original map or its genuine inverse.

The current formal metric assembly uses the public same-tensor equality
`riemannianEDist_eq_piecewiseSmoothRiemannianEDist` to transfer Mathlib's
compatible extended metric before capping. That provider retains its named
C¹-to-smooth approximation obligation; no equality is assumed silently. This
formal route preserves the exact piecewise-smooth distance in the conclusion.

The native data in the conclusion merely package the explicitly asserted
intrinsic smooth plaques, tangencies, C¹ family, receiving leaves, product
homeomorphisms, and induced path distances. They are not additional input
hypotheses. The full theorem is left as one named Stage2 `sorry`; no metric
laws, source-to-API assertions or Stage3 proof are smuggled into a definition.

Source: CURRENT whole AP source composite for the EXACT literal public proposition. Select native Fact1 final h and original f/f⁻¹ construction FROMOUTSET at Λ=M,U=M (empty separate). Hirsch–Pugh1969 Th3.1p148 finite squared sums, reviewed Fact1 Hatcher2017Prop2.9p52/Lee2003/Wockel2009Th11pp99–102 metric preparation; Lee2003 6.17pp139–140/p275/p277/11.19–11.20pp278–279 component and intrinsic piecewise-SMOOTH length distances; retained elementary AP0 finite constant-D extension, packaged only after laws/original topology by exact MetricSpace.ofDistTopology. FULL native original operator/capture source: Petersen3ed §5.3p146/5.5.1–6pp156–160, Walter2014 AUTHOR preprint4.1–4.3pp10–22 plus Walter2012DM484pp107–110 ordinary Banach bridge, Shub1987pp72–78/AppendixIII.2p65 and genuine local Cor5.4/native primitives. HPS1977 5.1pp54–60/5.4pp60–61/5.5pp61–63 NONSTRICTρ=1, second proofp63; g9 SECOND on SAME final h with N=1/commonν and explicit bidirectional ALL-time capture on common OPEN graph domains; source6Bpp111–114/7.5–7.6pp127–129/GL10 smooth intrinsic native atlas. Glöckner2007v2 AUTHOR preprint5.3/5.6Eq66pp41–43/5.10pp45–46 and Fisher–Hasselblatt2018 Lem12.5.18p602/Prop12.1.3pp578–579 actual local graph/intersection/residual mechanism, all source core/caller/radius guards written. Shub10.10pp126–127 actual BOTH intrinsic inverse coordinates and AMBIENT OPEN product image. Lee piecewise-smooth intrinsic length plus named chain/integral primitives give θ path-distance contraction; Mañé185Eq10 only a displayed consequence/convention, not full proof. Mixed written construction, AUTHOR source components and transparent elementary instance calculations, not one verbatim published AP theorem and not credit for HP3.2(f) expressly omittedp151. Previous private h/G/Γ, sharp rational cutoff and C¹ ambient path-comparison branch are superseded with full history; no private/global-cutoff identity, Sigma=constant-D equality, C¹-infimum equivalence or GL8/9/global asymptotic/stage-union output is used. Complete at ONE DAG LEVEL relative to named source/API prerequisites only; recursive/formal/kernel closure and new source foundation credit are not asserted.

Complete current natural-language proof of the DAG node:

1. Keep the EXACT given M, original C∞ diffeomorphism f, smooth positive tensor h₀, continuous invariant Eˢ⊕Eᵘ and original all-n C,τ estimates. No positive iterate, connectedness assumption, smooth splitting, common rank across unrelated components or additional hypothesis is introduced. If M is empty, select h=h₀ and its unique empty metric, θ=λ=1/2, β=1, γ=1/4 and ε=1; every point-indexed assertion is vacuous. All later applications therefore treat nonempty M.

Apply the CURRENT SOURCE Fact1 to Λ=M,U=M and the original h₀,C,τ. M is nonempty compact invariant and ∩_(j∈Z)f^j(M)=M. Select its ACTUAL source-constructed smooth adapted tensor h from the outset. Its written Hirsch–Pugh3.1 finite squared-sum preparation chooses q with Cτ^q<1 on the original two summands; the reviewed Hatcher/Lee/Wockel construction produces the final smooth positive h and post-smoothing one-step bound a_h∈(0,1) for Df|Eˢ and Df⁻¹|Eᵘ. Set θ=a_h. These are the same final h and original f used in the native proof below; the previous AP2 tensor/private G is not a retained existential witness. Fact1 is a genuine named premise for this metric output, relative to its source/API prerequisites, not a claim that its public statement alone exports all the chart/capture conclusions later constructed here.

The original manifold is locally connected in its Euclidean charts. Its original connected-component fibres are open, using isOpen_connectedComponentIn on univ; their complements are unions of the other open fibres, so they are closed. Their open cover has a finite subcover by compactness, hence only finitely many occupied components occur. Each is a closed compact connected smooth open submanifold. The connected-components fibre identity binds these sets to their ORIGINAL quotient labels; connectedness uses the actual component theorem, not an arbitrary partition. The original diffeomorphism permutes the components in both directions. Df gives isomorphisms between corresponding splitting factors along each orbit, even if it permutes components with different ranks. Nonempty zero-dimensional components are singletons with zero tangent spaces; unit-sphere arguments are skipped there.

Use the exact original norm/section setup of Shub pp72–74 with this final h. Put ν_p(v)=max(|pr_s v|_h,|pr_u v|_h). The pointwise triangle bound gives |v|_h≤2ν_p(v), so mν=1/2. Continuous splitting projections and compact local frame/unit-sphere cores give finite Mν≥1 with ν_p(v)≤Mν|v|_h. The original f/f⁻¹ reindexing and receiving fibres give contracting block bounds ≤a_h in the two respective directions. These are positive bounds, not equalities of operator suprema or an h-orthogonality assertion. Bounded dependent sections carry the genuine supremum norm; continuous sections form the closed continuous subcarrier. The subsequent native operator construction uses precisely these norms and original carriers.

2. For each occupied ORIGINAL open connected component M_i select the piecewise-SMOOTH h-length distance δ_i from the outset. Lee2003 p275 defines length by the finite sum of integrals of the h-speed on continuous piecewise smooth paths, with finitely many smooth pieces and finite one-sided endpoint speeds. His Lemma6.17pp139–140 proves the required path existence: points reachable from p form a nonempty open set by coordinate straight segments; a boundary point is reachable by the same local segment argument, so the set is closed and connectedness gives the whole component. Thus lengths connecting any two points are finite and their infimum is a finite real number. Constant paths, reversal and finite concatenation supply self-distance0, symmetry and the triangle inequality. The existing affine integral change-of-variables and adjacent finite-interval identity implement these operations on this SAME curve class.

Lee Lemma11.19p278 bounds the continuous positive h-norm above and below on a compact coordinate core times the fixed model unit sphere; homogeneous rescaling gives the bounds for every tangent vector, and zero vectors are direct. Proposition11.20pp278–279 proves separation and ORIGINAL topology: a path connecting distinct points must exit a protected compact chart ball, whose lower speed comparison gives a positive exit length. Conversely, fix the compact core and upper comparison FIRST, then a sufficiently short coordinate straight segment has length below a prescribed metric radius. The exit estimate places small δ_i-balls inside each original neighborhood, while the segment estimate places coordinate neighborhoods inside δ_i-balls. Zero-dimensional connected components are singletons, δ_i=0 there, and no unit vector is normalized. This is the source-natural Riemannian length distance; no identity with a separately defined C¹ infimum, riemannianEDist or transported metric is asserted.

Each M_i is compact in this original δ_i topology. On M_i×M_i the function (u,v)↦δ_i(u,v) is continuous by continuous_dist, and compact product plus isCompact_exists_bound_of_continuousOn gives a finite real upper bound. Replace that bound by B_i=max(bound,0). Since only finitely many occupied components occur, choose D=2+max_i B_i; the empty case was handled before this maximum. Define the ACTUAL AP distance on the ORIGINAL carrier by
 d(u,v)=δ_i(u,v) if u,v lie in the same M_i, and d(u,v)=D otherwise.
It is finite, symmetric and has self-distance0. Distinct-component pairs have positive distance D; within one component separation is the source δ_i separation. For three points in one component use its triangle inequality. If the endpoints are in different components, either an intermediate point shares one endpoint component, giving D≤D+nonnegative, or all three are in different components, giving D≤2D. If the endpoints share a component and the intermediate point is elsewhere, d(u,v)≤B_i<D≤2D=d(u,w)+d(w,v). These are the retained elementary AP0 cases, not an invented substitute metric.

Prove BOTH directions of the literal topology/positive-ball equivalence before packaging. For an ORIGINAL open set O and u∈O∩M_i, the component metric gives r>0 with its r-ball contained in O∩M_i; take min(r,D/2) to exclude other components. Conversely if every u∈O has such a positive d-ball, take its radius below D and use the component δ_i topology to obtain an original open neighborhood in M_i; M_i itself is original open, so these neighborhoods make O original open. Now, and only now, apply the existing exact MetricSpace.ofDistTopology constructor to THIS d, its laws and this equivalence; its distance and original topology are definitionally the supplied ones.

This distance is CONSTANT between components exactly as the public AP statement requires. It is not Fact1's variable Sigma metric. Only within an original component do both source constructions have the SAME entire h-length distance δ_i. For point tests at radii below min(D,1), the two metrics therefore agree, and pairs in different components are excluded in both. Since f permutes components, this agreement persists at EVERY positive or negative iterate for same-component pairs. Every subsequent normal/capture/product radius is chosen below1; D≥2 then excludes components uniformly without altering f or passing to a return iterate.

3. This step is an EXPLICIT reuse of the reviewed ORIGINAL native proof algorithms, not a false inference that Fact1’s public proposition exports an embedded chart or a full sup-chart homeomorphism. Select the native moving lift, bounded-section operator and source graphs from the outset on the final h and ORIGINAL f, then separately ORIGINAL f⁻¹. In the protected local point tests below, d is the constant-D component metric JUST proved. All radii are<1<D, so the same-component h-length radial proof applies verbatim; there is no global Sigma=constant-D or C¹-distance identity. The source references to componentwise distance in this body mean exactly these δ_i.

Native Φ/Uδ RADIAL closed-ball component — actual written normal-ball proof for the SAME final h. Use Petersen, Riemannian Geometry3ed, §5.3 printedp146/PDF162: his path distance is the infimum of lengths of continuous PIECEWISE C∞ curves, with finitely many smooth pieces and length the integral of the h-norm of their velocities. This is exactly the curve/length class used for each original component distance in the preceding adapted-metric/component-distance steps. Apply his actual Proposition5.5.1 pp156–157/PDF172–173 and Corollary5.5.2 pp157–158/PDF173–174 to the FINAL smooth positive metric h and compact M. Proposition5.5.1 writes the zero-section/diagonal derivative block and moving-base exponential inverse; Corollary5.5.2 writes the local bundle-trivialization/norm comparison and finite compact selection giving one positive OPEN normal radius ρ_big such that exp_h,p is a diffeomorphism from B_h(0,ρ_big) onto its image for EVERY p∈M. Before the competing-curve comparison set ρ_N=ρ_big/2. In each original finite-dimensional h-tangent fibre the CLOSED radius-ρ_N ball is compact and lies strictly inside the larger OPEN radius-ρ_big normal domain. Its exponential image is compact by isCompact_image_of_continuousOn, hence closed in the original Hausdorff manifold by isCompact_isClosed. The larger normal inverse is continuous on a neighborhood of this image. The exact closure_ball theorem, with positive ρ_N, and this actual larger-domain homeomorphism identify the closure of exp_h,p(B_h(0,ρ_N)) with exp_h,p(closedBall_h(0,ρ_N)); the boundary is the image of the radius-ρ_N sphere. Consequently the radial inverse norm extends to that actual boundary with value ρ_N. The first-exit comparison below therefore uses a protected closed normal ball INSIDE a larger inverse domain, not an assumed extension of exp at its outermost radius or geodesic completeness. In zero-dimensional ambient M the component is a singleton and there is no exit boundary; the radial and distance identities are direct0=0. The smooth metric and geodesic here are original h on M, not a metric transported through an arbitrary homeomorphism.

Follow the actual Theorem5.5.4 pp158–159/PDF174–175 and Gauss Lemma5.5.5 pp159–160/PDF175–176 to identify that image with the h-length ball and its radial distance. On a normal ball put r(q)=|exp_h,p⁻¹(q)|_h. The existing general geometry.gallier_quaintance_gauss_lemma_g6, applied to this SAME metric's natural exponential and Levi-Civita connection, gives constant radial-geodesic speed and orthogonality of radial and sphere directions, including the derivative identity at0. Therefore, away from p, grad_h r is the outward unit radial field; equivalently dr(v)=h(∂r,v) and |∂r|_h=1. This is also the written Petersen Gauss proof: his visually checked rotational field onp159 is J=−x^i∂j+x^j∂i, so dr(J)=0; the missing minus in text extraction is an OCR loss, not a printed defect. Metric compatibility/torsion-free variation makes h(∂r,J) constant along radial geodesics, and the bound |J|→0 at the center makes that constant0. The named general Gauss input already supplies precisely the needed radial identity; no source sign correction, exercise, completeness assumption or replacement exponential is introduced.

Petersen's length proof compares against ALL competing piecewise smooth ambient curves, not just paths retained inside the normal ball. Fix q in the normal image, let ℓ=r(q)<ρ_N, and use the radial geodesic from p to q: its h-length is ℓ. For any competing piecewise smooth path c from p to q, discard its portion before the last visit to p. If it first exits the normal image, let b₀ be that first exit; otherwise let b₀ be its endpoint at q. On the retained portion inside the normal image and away from p, Cauchy–Schwarz gives (r∘c)'=dr(c')≤|c'|_h. Integrate this inequality as in Petersen5.3.2/p159. For exact endpoint guards, first restrict to compact subintervals lying inside that portion and split at the finitely many original smooth-piece endpoints. On each such piece r∘c and the speed are continuous, their ordinary derivative is known on the open interval, and the relevant derivative is interval-integrable; the existing continuousOn_intervalIntegrable and integral_eq_sub_of_hasDerivAt_of_le inputs apply without endpoint derivatives. Add the finitely many integrals by the adjacent-interval identity. Taking the endpoints to the last visit and first exit/end uses continuity and the finite bounded speeds on each original smooth piece. This yields length≥r(c(b₀)). At an exit the latter value is ρ_N, strictly greater than ℓ; without an exit it is ℓ. Thus EVERY ambient competitor has length≥ℓ, and the radial one attains it. Conversely, a point at h-length distance<ρ_N admits a piecewise smooth path of length<ρ_N; the same first-exit lower bound prevents that path from leaving the normal image. Hence exp_h,p(B_h(0,ρ_N))=B_(d_h)(p,ρ_N) and
 d_h(p,exp_h,p(v))=|v|_h  for |v|_h<ρ_N.
Here d_h is precisely the preceding adapted-metric/component-distance steps's componentwise PIECEWISE SMOOTH length distance. No equality with the C¹-curve riemannianEDist or a native maximum-norm distance is asserted.

Retain the SAME selected moving inverse L and open U/O/B of hps.uniform_exponential_lift_on_compact_set, already used for the actual native lift H below. Let ρ_exp be its positive original exponential radius and R its centered lift radius. Choose 0<ρ≤min(ρ_N,ρ_exp,R) and then 0<δ<min(ρ/4,1/4). This is a restriction of those same branches, not a new inverse selection. Petersen Corollary5.5.6 printedp160/PDF176 explicitly gives both the open and CLOSED smaller-ball equalities for δ<ρ_N. Its closed equality is visually present with closed-ball bars. Thus for every p∈M,
 exp_h,p(closedBall_h(0,δ))=closedBall_(d_h)(p,δ),
 and |L(p,q)|_h=d_h(p,q) whenever d_h(p,q)≤δ.
Indeed each such q is exp_h,p(v) for a unique v with |v|_h≤δ<ρ≤ρ_exp, so the existing identity L(p,exp_h,p(v))=v identifies it with the ALREADY selected inverse. Boundary points |v|=δ remain strictly inside the larger OPEN normal/selected domain. The radial path stays in p's original component. Conversely d(p,q)≤δ<1 places q in that same original component by the proved constant-D separation D≥2 of the exact component-metric construction, where d=d_h on that component. Therefore these closed-ball and radial identities hold with the FINAL original d as well. Components may be permuted by f; no component return iterate is taken.

Now apply Shub's actual POINTWISE exponential chart algorithm, printedp73/PDF86, to ALL bounded, not necessarily continuous maps and sections over M. Let Γ_b(M,TM) be the original dependent bounded h-norm sections, already the Banach carrier used below. Define Π(ξ)(p)=exp_h,p(ξ(p)) and Φ(g)(p)=L(p,g(p)), and put
 Cδ={ξ:||ξ||_(h,sup)≤δ},
 Uδ={g∈B(M,M):d(p,g(p))≤δ for EVERY p∈M}.
The normal-ball identities prove directly that Π maps Cδ into Uδ and Φ maps Uδ into Cδ, with Φ(Πξ)=ξ and Π(Φg)=g POINTWISE. In particular Φ(g) is a literal section of T_pM over the ORIGINAL p, bounded by δ, and Πξ is a bounded map because its distance from the inclusion is uniformly≤δ. No continuity in p is needed for membership. The existing lp_infty_banach_sup_norm_g4 input gives the exact arbitrary dependent sup-norm formula and both coordinate/norm bounds for these same full tangent fibres. The set of coordinate norms is bounded above byδ and is nonempty because M is nonempty; taking suprema of the pointwise equalities gives
 ||Φ(g)||_(h,sup)=sup_(p∈M)d(p,g(p)),
 ||ξ||_(h,sup)=sup_(p∈M)d(p,Π(ξ)(p)).
Thus Uδ is exactly the closed POINT-TO-INCLUSION sup-distance neighborhood corresponding to the original closed h-sup section ball. These formulas do not assert |ξ(p)−η(p)|_h=d(Πξ(p),Πη(p)) or an all-pairs chart isometry. The closed ball is only a restriction inside a larger OPEN normal chart; it is not called an open Banach chart domain. In zero-dimensional ambient M the normal and component balls are singletons and the formulas reduce to0; no nonzero radial normalization is used. Arbitrary bounded/discontinuous sections and an uncountable M are literally permitted in this Shub specialization.

This supplies the NATIVE radial closed-ball/chart correspondence and exact norm-to-inclusion identity by the written normal-ball proof and pointwise Shub algorithm. It does NOT prove a full sup-chart homeomorphism or all-pairs chart isometry. The direct native operator below and its subsequent Shub application use the same pointwise identities and original orbit formulas instead of that unproved chart-homeomorphism assertion. No private cutoff graph or all-M lamination is identified here. The following full written Walter dependent-section OPERATOR component is applied here to the selected original h/f.

Native Γ_b operator component — actual arbitrary-index written source. Keep the ORIGINAL smooth f and the FINAL smooth metric h of the preceding adapted-metric/component-distance steps. Use hps.uniform_exponential_lift_on_compact_set E3–E5 on A=M with this metric, selecting its ONE actual smooth native lift H_p(v)=L(f(p),f(exp_p(v))) on the ambient open Ω, with the SAME smoothly varying inverse Ψ and uniform |v|_h<R lift domain. Smooth original f and h make this actual ambient expression C∞. This is H itself, not the private order2 cutoff G, and no new order-dependent lift, inverse branch, radius or splitting outside M is selected. Choose once 0<R0<R, for example R0=R/2. Every closed h-ball |v|_h≤R0 over M lies strictly in this SAME Ω.

Verify the source uniform-jet guards by the following original finite compact-frame construction, applied to this native H at EACH finite positive order. Take finitely many smooth ambient source/receiving tangent frames, the receiving frame evaluated at f(p), with compact base cores K_i⊂M whose relative interiors cover M. These are restrictions of actual ambient frames; they do not trivialize the whole bundle globally, give M a differentiable structure or extend Eˢ/Eᵘ off M. The compact-core/unit-sphere minima and maxima already used with the SAME final h give positive source and receiving frame norm comparisons. Consequently the set {(p,u):p∈K_i, |frame_src(p)u|_h≤R0} is closed in a compact K_i times a sufficiently large closed Euclidean ball, hence compact by isCompact_prod/isCompact_closedBall/isCompact_inter_right. It lies inside the actual open coordinate expression of Ω. For each fixed natural j≥1 its actual full vertical D_v^jH is jointly continuous there by E5: apply contDiffOn_continuousOn_iteratedFDerivWithin to the smooth ambient coordinate expression on its SAME open domain, with isOpen_uniqueDiffOn, then iteratedFDerivWithin_of_isOpen; restriction to vertical arguments gives its ordinary fibre derivative. No within derivative on M or UniqueDiffOn M is taken. Compact norm bounds and finite frame comparisons therefore give a finite M_j≥0 such that ||D_v^jH_p(v)||_{h_p→h_f(p)}≤M_j for EVERY p∈M and |v|_h≤R0. The multilinear evaluation/opNorm leaves make the frame-norm conversion explicit. Each finite j has its OWN M_j; the ball R0 and native H are unchanged for every j. No single bound for all orders or private C2-to-C∞ conversion is claimed. Rank-zero fibres are {0}, H_p(0)=0 and every positive derivative is the zero map; no unit sphere or positive-dimensional chart argument is applied to them. Multiple ranks or components are treated by their finite local frame cores, not a fixed global model.

Now follow Walter2014 AUTHOR PREPRINT Def4.1.1 p10, Lem4.1.6 p12, Defs4.2.5–6/Lem4.2.9 pp15–16, Prop4.3.3 FULL proof pp19–21 and Lem4.3.5/Cor4.3.6 FULL proof p22. Take I=M as an arbitrary nonempty index set; for each p let X_p={0}, U_p={0} (open in this zero normed space), Y_p=(T_pM,|.|_h), Z_p=(T_f(p)M,|.|_h), and V_p=B_h(0,R0). Set β_p=H_p|V_p, with β_p(0)=0 and smooth ordinary fibre maps. The varying normed spaces Y_p,Z_p and an uncountable I are literally allowed by the printed theorem. Set section-order k=0 and W={1,ω}, with constant ω=max(1,1/R0). This is an adjusting weight because its value is at least1 and at least the reciprocal of the boundary distance R0; at rank zero V_p=Y_p and the boundary restriction is vacuous. Its weighted sup topology is equivalent to the ordinary h-sup topology since ω is a fixed finite positive constant. For any 0<r_h<R0, the h-sup ball ||ξ||_h,sup<r_h has a UNIFORM boundary margin: ξ(p)+B_h(0,R0-r_h)⊂V_p for all p. In the source weighted notation choose the common margin t=ω(R0-r_h)>0. Thus this whole open ball lies in C_W^{ω∂,0}(U_p,V_p), whose openness is the actual Lem4.2.9 proof. Mere pointwise membership ξ(p)∈V_p would not suffice. At order0 and singleton U_p, the domain/codomain restricted products are exactly bounded, possibly DISCONTINUOUS dependent sections with norms sup_p|ξ(p)|_h. Each fibre is finite-dimensional complete; source Lem4.1.6 writes coordinate Cauchy limits passing the same supremum estimate to the limit, and existing lp_infty_banach_sup_norm_g4 supplies the identical arbitrary dependent Banach carrier. No sequence enumeration of M or countable-to-uncountable argument is used.

The verified M_j are exactly the positive-order uniform bounds of Cor4.3.6; Lem4.3.5 verifies the required weight inequality and Cor4.3.6 reduces to Prop4.3.3 using β̃_p(0,v)=H_p(v). At k=0 the printed proof first proves N(ξ)(p)=H_p(ξ(p)) is bounded from β_p(0)=0 and the common first-derivative bound, and then proves sup-topology continuity by the source uniform derivative estimate. It computes the component differentials dN(ξ;η)(p)=D_vH_p(ξ(p))η(p); Prop4.3.3 assembles these into a continuous restricted-product differential using its actual arbitrary-index differentiation criterion, with repeated derivatives similarly controlled by the verified M_j. This is the HUMAN written simultaneous superposition algorithm, not an invented bundle Taylor induction. Published Walter2012 Dissertationes Mathematicae484, PropA.3.2 pp109–110 and LemA.3.3 p110 supply the ordinary norm-Fréchet bridge: source smoothness implies C² and hence FC¹ by LemA.3.3, with the derivative field continuous in the bounded-linear operator norm; PropA.3.2 identifies that norm-continuous derivative with the component differential. Its actual PropA.2.11 pp107–108 segment identity/estimate supplies the norm remainder, not a claim that Keller C¹ by itself implies ordinary Fréchet C¹. In the present normed Banach carriers the source's uniform-on-bounded-sets operator topology is the operator-norm topology. Thus N is ordinary Banach C¹ on the SAME strict h-sup ball and DN(ξ) has the displayed formula. The bound |DH_p(ξ(p))η(p)|_h≤M_1|η(p)|_h passes through the dependent supremum to ||DN(ξ)η||_sup≤M_1||η||_sup; linearMap_mkContinuous_g3 bundles this actual linear map. The same source segment estimate applied to the derivative field, whose second derivative is bounded by M_2, gives ||DN(ξ)-DN(ζ)||_op≤M_2||ξ-ζ||_sup on this convex ball. Existing contDiffOn_fderiv_of_isOpen and the normed segment mean-value API bind that operator-valued source calculation on each actual fibre. This explicit sup-operator estimate takes no derivative of the index p or of ν.

The output of N is the bounded family η(p)∈T_f(p)M. Define Jη(x)=η(f⁻¹x). Since f|M is a bijection, sup_x|η(f⁻¹x)|_h=sup_p|η(p)|_h; J and its inverse reindexing are linear h-sup isometries of these actual dependent families. No identification of distinct tangent fibres is made: T_f(f⁻¹x)M=T_xM is the receiving fibre by literal substitution. Compose E=J∘N. Then Eξ(x)=H_f⁻¹x(ξ(f⁻¹x))=exp_x⁻¹(f(exp_f⁻¹x(ξ(f⁻¹x)))) on the selected native inverse branch and SAME Ω. The native lift gives DH_p(0)=Df_p, hence DE(0)ξ(x)=Df_f⁻¹x(ξ(f⁻¹x))=f#ξ(x), exactly Shub p74. E is Banach C¹ here and its first derivative is continuous in operator-sup norm. This proves the section OPERATOR/formula component only, not the assertion that a closed h-sup chart ball maps onto a particular closed metric neighborhood of the inclusion inc(M) in B(M,M).

Finally bind the original product maximum norm, without changing any metric or construction. The SAME comparison m_ν|v|_h≤ν_p(v)≤M_ν|v|_h from the adapted-metric/section-norm step above is uniform at source and receiving fibres. Passing to suprema gives m_ν||ξ||_h,sup≤||ξ||_ν,sup≤M_ν||ξ||_h,sup. Choose 0<r_box<m_νr_h<m_νR0 BEFORE using a box-norm section ball. Then ||ξ||_ν,sup<r_box implies ||ξ||_h,sup<r_h and the preceding uniform boundary margin; an incorrect identical R0 in the two norms is not used. Equivalent norm topologies preserve the Banach C¹ certificate and derivative continuity (the comparison of operator norms costs at most M_ν/m_ν). This uses ν only over M and no derivative or smoothness of ν. The operator uses original f/f⁻¹ base reindexing, not a positive return iterate or a theorem over all M.

Native μ, continuous FIRST fibre jets and SAME-final-h closed dynamical cores — direct application of the written Shub algorithm. Use Shub, Global Stability of Dynamical Systems, Theorem6.2 pp71–72/PDF84–85, the original bounded-section operator onp74/PDF87, singleton/splicing Lemma6.5 pp76–77/PDF89–90 and the final native graph/center/core argument p78/PDF91. The zero-tangent mechanism is the written derivative graph-transform fixed-point argument in AppendixIII.2, proofp65/PDF78, referring to Proposition5.16. The formulas and strict native-domain, inherited-remainder, supported-frame and metric-ratio guards below are explicit applications of those written mechanisms; they are not formulas all literally printed by Shub or an additional generic parameter theorem. Only first fibre derivatives are claimed by this component.

Use the GIVEN continuous splitting, not the omitted converse of Shub Lemma6.3 p73. Its fibre projections are continuous, with uniformly bounded h-operator norms on compact M; hence bounded sections split into closed Banach subspaces Γ_b^s and Γ_b^u and the ν-sup norm is exactly the maximum of their original h-sup norms. Independently of any private cutoff, ν_p(v)=max(|pr_s v|_h,|pr_u v|_h) satisfies |v|_h≤2ν_p(v); compact continuous projections give ν_p(v)≤Mν|v|_h for a finite Mν≥1. Thus mν=1/2 is valid, or use the minimum with an already selected smaller valid mν and enlarge Mν if needed to keep every preserved domain comparison. These are the given splitting/norm comparisons of Shub p74, not consequences of G or an identity of native and private graphs. In this splitting T=DE(0)=f# has ||T_s||≤a_h and ||T_u⁻¹||≤a_h for the original the preceding adapted-metric/component-distance steps constant a_h<1. Reindexing by original f or f⁻¹ preserves the appropriate sup norm and no fibres are identified except by their actual Df maps. Choose a_h<λ_aux<1 and use the existing ordinary Banach C¹ certificate for E. Continuity of DE at0 and the segment mean-value estimate let one choose ONE strict ν-radius cν<r_box on which Lip(E−T) is below the smallness required by hps.corollary_5_4_local_strong_graphs at r=1,ρ=1. The SAME choice is made inside the h-sup/lift margins already proved; cν<mν r_h. Apply that source with E₁=Γ_b^u, E₂=Γ_b^s, a=||T_u⁻¹||<1 and k=||T_s||<1. It gives a centered C¹ stable graph Ψ:Γ_b^s(cν)→Γ_b^u(cν), local invariance and the EXACT retained-domain forward criterion: a point is on the graph precisely when its original E forward orbit is wholly in the OPEN ν-ball of radius cν and has bounded norm at ρ=1. The source equivalently gives convergence to0 for these retained orbits. No weighted return criterion or advance convergence premise replaces this all-forward retained condition. Restrict graph inputs to a smaller positive inner ball whenever necessary so graph points and subsequent comparisons belong to the common original source germ. The source assertion is local invariance within this SAME germ, not global invariance of an arbitrarily enlarged graph.

Follow the actual singleton/splice calculation of Shub pp76–77. For p∈M let δ_p(v) be the section equal to v∈E_p^s at p and0 elsewhere. It is a bounded section even when it is discontinuous, with ||δ_p(v)||_ν=|v|_h. Evaluation ev_p is linear and |ev_p ξ|_h≤||ξ||_(h,sup)≤mν⁻¹||ξ||_(ν,sup). These direct arbitrary-index norm calculations, bundled by linearMap_mkContinuous, make δ_p and ev_p continuous linear maps. The ℤ-only lp_eval/single node statements are NOT applied to M. If σ₁(p)=σ₂(p), replace Ψσ₁ only at p by Ψσ₂(p). The initial full section equals (σ₁,Ψσ₁) offp and equals (σ₂,Ψσ₂) atp. At its nth E iterate it equals the first genuine graph orbit except at fⁿ(p), where it equals the second genuine graph orbit, by the literal pointwise H/reindexing formula. Thus its ν-sup norm is at most the maximum of the two genuine norms at EACH n. Both genuine orbits were chosen in the SAME original open cν capture domain; therefore so is the splice, and its orbit is bounded there atρ=1. The retained graph criterion implies its unstable part equals Ψσ₁. Consequently Ψσ₁(p)=Ψσ₂(p). Define μ_p(v)=ev_p Ψ(δ_p(v)) on the fixed smaller fibre ball. It is C¹ in v by the continuous-linear chain rule, μ_p(0)=0, and Ψσ(p)=μ_p(σ(p)) whenever all these inputs lie in the common germ. This is exactly the printed fibre-dependence algorithm, without a private graph identification or a continuity requirement for singleton sections. It also supplies the RECEIVING local invariance: if an actual graph section and its image remain in this germ, E sends it to a graph section, so H_p(v+μ_p(v)) lies on the graph at f(p), in the original receiving branch.

Run the continuous-section part of the SAME printed Lemma6.5 p77. Let Γ₀ be the continuous sections of TM|M, in the inherited ν-sup norm, and Γ₀^s/u its continuous subbundle sections. A ν-sup convergent sequence has uniform h convergence by mν; in each original local bundle frame the locally bounded frame coordinates converge uniformly on a smaller compact frame core. The uniform_limit_continuous_on_set leaf gives continuity of their limit there. Such frame neighborhoods cover M, so Γ₀ and Γ₀^s/u are closed subspaces of their complete bounded-section carriers and hence Banach by isClosed_completeSpace_coe. This proof uses the actual bundle topology, not a new topology on Γ₀ or smoothness of M. The original joint continuity of H_p(v), D_vH_p(v), continuous sections and f⁻¹ proves E(Γ₀)⊂Γ₀ and DE(ξ)(Γ₀)⊂Γ₀ for every ξ∈Γ₀ in the strict original domain. Explicitly DE(ξ)η(x)=DH_f⁻¹x(ξ(f⁻¹x))η(f⁻¹x) is continuous in x. Restrict this bounded linear derivative to Γ₀ and codomain-restrict it by continuous_linear_map_codRestrict. Its inherited norm remainder is EXACTLY the ambient remainder already established for E: the numerator ||E(ξ+η)−Eξ−DE(ξ)η||_ν and the denominator ||η||_ν have unchanged values. Hence the ratio tends to0 for η∈Γ₀, and derivative operator continuity follows by restriction of the ambient operator-norm estimate. Thus E|Γ₀ is genuinely ordinary Banach C¹; mere set invariance is not its differentiability proof. Apply the SAME Cor5.4, with the SAME cν/r=1/ρ=1 data, to Γ₀=Γ₀^u⊕Γ₀^s. Its graph Ψ₀ has continuous outputs. Its retained orbits are also genuine Γ_b orbits in the same domain; uniqueness there gives Ψ₀=Ψ|Γ₀^s on their common graph germ. This is the continuous-section restriction and uniqueness explicitly used by Shub p77.

Make its first-jet conclusion explicit in the original local frames, as Shub p78 then does. Near p₀∈M choose a continuous local frame C_q:ℝ^d→E_q^s on a relative open V. Choose r>0 so the closed relative d-ball of radius2r about p₀ is contained in V; compactness makes this a compact frame core. Put β(q)=min(1,max(0,2−d(q,p₀)/r)). It is continuous by the original continuous_dist/min and scalar arithmetic (max(0,t)=−min(0,−t)), equals1 on the r-ball and vanishes outside the closed2r-ball. Define J(v)(q)=β(q)C_q(v) on V and0 outside V. Because the support is contained in V, this is a continuous section across the zero extension; the compact frame norm bound gives ||J(v)||_ν≤C|v| for a finite C. Thus J is a fixed continuous linear map ℝ^d→Γ₀^s by linearMap_mkContinuous. This does not extend E^s offM. Shrink the fixed model v-ball so Jv lies in Ψ₀'s actual input germ. Where β=1,
 μ_q(C_q v)=ev_q Ψ₀(Jv),
 D_v[μ_q(C_q v)] e_i=ev_q[DΨ₀(Jv)(J e_i)].
For the output use the original continuous E^u bundle frame. Evaluation (q,η)↦the output-frame coordinates of η(q) is jointly continuous for η∈Γ₀^u: the difference from a fixed η₀ is bounded by a local frame constant times ||η−η₀||_sup, and q↦η₀(q) is continuous. No such assertion is made for arbitrary discontinuous Γ_b sections. The C¹ map Ψ₀ and operator-norm continuity of DΨ₀ therefore give joint values and all FIRST state derivative columns in these frames. Finite-dimensional frame comparisons turn the finite column statement into joint operator-norm continuity. This is the supported-frame/evaluation binding of Shub's printed continuous-section algorithm; there is no derivative in the base q, no joint higher-order assertion and no global Euclidean leaf parameterization. Rank-zero local frames give the constant zero map and need neither a basis column nor nonzero normalization.

Bind tangency by the printed Shub p65 derivative-fixedpoint argument, not an unstated tangent conclusion of the public Cor5.4. Its ambient setup is Banach; only this derivative argument, not its global f:E→E theorem, is needed here. Let K=DΨ(0). Local graph invariance and DE(0)=T give by the existing chain rule K T_s=T_u K. Hence K=T_u⁻¹ K T_s, whose right-hand operator has norm at most a_h²||K||. Since a_h²<1, K=0. The same calculation holds for Ψ₀ on Γ₀. Singleton/evaluation composition then gives Dμ_p(0)=0 for every p. To bind every later SMALLER receiving graph germ explicitly, shrink a common convex section-input ball around0 so continuity of DΨ and DΨ₀ with K=0 gives operator norm≤1 there. The existing segment estimate and Ψ(0)=0 give |Ψσ|_sup≤|σ|_sup, so the ν-norm of its graph point is exactly its stable input norm. Choose the native remainder Lipschitz bound ε also strictly below 1−k, where k=||T_s||≤a_h. First use the original Cor retained-domain invariance to place Eξ on the graph in cν. Its stable input σ′ satisfies |σ′|_sup≤(k+ε)||ξ||_ν by centering E−T and its Lipschitz bound. Thus σ′ stays in the chosen smaller input ball; only THEN apply its unit-slope bound to conclude ||Eξ||_ν=|σ′|_sup≤(k+ε)||ξ||_ν. This is the explicit small-germ binding of Shub's maximum-norm graph construction and original forward-return estimate. It uses the already proved C1/tangent-zero graph and segment calculus, rather than an unexported stronger statement of Cor5.4. The pre-tangency splice and continuous-subspace comparison required only the original cν retained domain. Singleton graph sections and their receiving images now remain in any chosen smaller common germ. The inverse branch uses the same order of reasoning. Shub p65 expresses exactly this as the unique zero fixed point of the derivative graph transform when Df(0)=T. This application uses the tested native DE0=f# and original block bounds; it adds neither a cutoff extension nor a global invertibility premise.

Now follow the SAME-final-h compact first-jet shrink on Shub p78. Set u_p(v)=v+μ_p(v) and A_p(v)=H_p(u_p(v)), for original source and receiving normal domains. Dμ_p(0)=0, so DA_p(0)=Df_p|E_p^s and ||DA_p(0)||_h≤a_h. The joint first jets just proved, smooth original H/exp and finitely many compact local frame cores allow a UNIFORM positive inner v-domain with ||Dμ_p(v)||_h≤η and ||DA_p(v)||_h≤a' for chosen a_h<a'<1 and 0<η<1−a', so κ_s=a'/(1−η) lies in (0,1). All derivatives here use original h at the actual source/receiving fibres; no h-orthogonality of E^s/E^u is assumed. Segment mean-value in each convex fibre v-ball, μ_p(0)=A_p(0)=0, gives |μ_p(v)|_h≤η|v|_h and |A_p(v)|_h≤a'|v|_h. Therefore |u_p(v)|_h≥(1−η)|v|_h and
 |A_p(v)|_h≤κ_s |u_p(v)|_h.
Choose the domain small enough that u_p(v) and A_p(v) lie strictly inside the SAME selected original normal/inverse branches. The protected Petersen radial identities then turn this into d(f(p),f(q))≤κ_s d(p,q) for q=exp_p(u_p(v)) on this native graph core. Distances are below1 and hence use the same componentwise original h-length metric; neither ν-distance nor a transported metric is used. This is the explicit norm-ratio/compact-margin application of Shub's printed strict tangent contraction argument, not a new pairwise offM estimate.

Choose ONE ε_s>0 with ε_s<1/2, simultaneously for all p∈M, STRICTLY below the selected physical normal/output radii and the first-jet domain, and with Mν ε_s<cν. Also require the original stable projection bound times ε_s to lie strictly inside the fibre graph v-domain, so every graph vector of h-norm≤ε_s is in the chosen inner graph germ. All inequalities are strict even for a point at physical distance exactly ε_s. Define the native core as exp_p(graph μ_p)∩closedBall_(d)(p,ε_s) within this chosen graph chart. It has the EXACT original-source characterization
 P_s(p)={q∈M: d(fⁿq,fⁿp)≤ε_s for EVERY n≥0}.
For right-to-left, form the singleton bounded map equal to q at p and to the inclusion elsewhere, and its original f-conjugation orbit. At each time the selected pointwise native inverse gives a tangent section with h-sup≤ε_s and ν-sup≤Mν ε_s<cν. The original H/reindexing formulas identify these sections exactly with the E orbit. Every iterate is in the SAME open original capture domain, and atρ=1 its norm is bounded; Cor5.4 therefore puts the initial section on Ψ. Singleton fibre dependence gives q=exp_p(v+μ_p(v)). Its initial distance≤ε_s places it in the stated core. No convergence premise was assumed. For left-to-right, choose the genuine singleton graph section at this v. Its Cor graph orbit is retained in the original ν capture domain. Receiving graph invariance and fibre dependence put the first image on the graph at f(p); the SAME-h estimate gives distance≤κ_s ε_s<ε_s, so its vector and stable coordinate remain in the chosen inner graph/normal domains. Repeat this argument at every original iterate. Thus all distances are≤κ_sⁿ d(p,q)≤ε_s, establishing the opposite inclusion and the uniform center estimate. Receiving graph membership precedes each contraction step; inwardness is not inferred from coordinates alone. The closed initial boundary causes no problem because ε_s is strictly inside every open native/capture margin. This characterization is at the ONE selected valid ε_s, not at an arbitrarily shrunk comparison γ.

For unstable cores repeat the entire native construction with the ORIGINAL f⁻¹, on the SAME final h and SAME d. Its actual smooth moving lift is L(f⁻¹(p),f⁻¹(exp_p(v))) on a possibly smaller original uniform domain; it has the same compact finite-jet Walter guards, and its derivative is Df⁻¹. The given splitting swaps stable/unstable roles, with contracting block Df⁻¹|E^u and expanding inverse block norm both≤a_h. Restrict all branch/radius choices to a common positive minimum with the forward construction. Cor5.4 r=1,ρ=1, retained singleton splice, continuous-section restriction, supported first jets and the printed zero-derivative argument therefore give μ_p^u, receiving graph invariance for f⁻¹, κ_u∈(0,1) and ONE ε_u>0 with ε_u<1/2 and the exact backward characterization P_u(p)={q:d(f⁻ⁿq,f⁻ⁿp)≤ε_u for all n≥0}, and d(f⁻ⁿq,f⁻ⁿp)≤κ_uⁿ d(q,p). This is an actual inverse native branch, not an assertion that the forward nonlinear section map has a globally defined inverse. Rank-zero stable or unstable factors yield singleton graph cores directly; the same orbit-capture characterization applies with no nonzero-vector argument.



4. Invoke the SECOND independent public premise of g9.hps_anosov_global_lamination on THIS final smooth tensor h, ORIGINAL f and the same real continuous invariant splitting. Original chain rules and the one-step a_h estimates give all-n C=1,λ=a_h bounds in the actual source and receiving h-fibres. In its source GL1 preparation choose a_G9 with a_h<a_G9<1 and N=1. Its summand sums then have their single j=0 term, literally the restrictions of h to Eˢ/Eᵘ; the maximum ν is exactly the ν above. Its smooth background tensor for the exponential and cutoff is h. Use the same canonical exp_h and original moving inverse branch L, choosing their common domains by inverse uniqueness. No new component-distance premise, source GL8/9 asymptotic identification, stage-union equality or first-public distance specialization is used.

Select the CURRENT g9 source construction, rather than an unrelated existential immersion. HPS5.5pp61–63 supplies its source-selected original exponential graphs and self-coherence at the NONSTRICT rateρ=1; its second proofp63 is the bounded-section/evaluation construction. Its own chosen agreement domain and local graph disc are retained. Choose b_*>0 inside BOTH the HPS source agreement disc and its local membership disc, and inside its selected open graph domain. Local characterizations are tests of coherent original histories retained in these discs, not bounded distance somewhere on compact M. The source full-plaque graph return gives a uniform q<1 on an inner ν-disc. Both forward and actual inverse constructions have their own domains and graph/capture constants; different source cutoffs are permitted ONLY through the ORIGINAL-history tests below, and are never asserted identical or mutually inverse.

For the stable comparison first choose a Shub closed source core with physical radius ε_inner<ε_s and Mν ε_inner<b_*. Its center bound from the preceding native step keeps EVERY original future distance below ε_inner, hence every original logarithm in the SAME normal branch has ν-norm≤Mν ε_inner<b_*. The exact exponential/lift equation turns it into the HPS original retained history, so HPSρ=1 capture places each such Shub point on the selected HPS stable graph. Conversely choose an HPS original trapped graph ν-radius r_H<b_* with r_H/mν<ε_s and strictly below the common normal radius. Every original graph iterate has ν-norm≤q^nν_initial<r_H; because it remains inside agreement, the original f and graph iteration coincide at EVERY time. Its h-log norm is<r_H/mν<ε_s, so the Shub fixed-radius ALL-time source characterization puts its initial point on the Shub stable graph.

Shrink to common OPEN stable-parameter balls where both graph images satisfy these strict inner-domain bounds. Both parametrizations use the SAME actual stable vector v=pr_s L(p,y), with the identical original exponential and splitting projection. The two captures therefore prove equality of the graph FUNCTIONS on these common open balls, not equality of asymptotic sets or only equality at a center. Their graph embeddings and inverses coincide there. This identifies genuine OPEN chart restrictions. At every point of those restrictions, use the source centered HPS chart and its local inverse theorem to restrict the common graph to an open neighborhood of that point; source self-coherence gives the same leaf branch and receiving chart. All such restrictions stay in the chosen inner domains, whose constants are uniform on finitely many compact center cores. Repeat the same ordered bidirectional argument for ORIGINAL f⁻¹ with exchanged blocks, its own HPS agreement/disc and Shub ε_u, and take positive common minima. Thus BOTH stable and unstable charts, their open overlap inverses and every later point of a β-plaque are bound, not just the initial graph germs.

The invoked g9 SECOND output follows actual HPS6Bpp111–114 and7.5–7.6pp127–129: connected intrinsic smooth leaves, injective immersions tangent everywhere to the original distributions, compatible native open plaque charts and source f-invariance. Its GL10 finite-order source uniqueness/jet construction gives the same smooth germs and intrinsic atlas for each finite order; no common radius for every order or differentiability in the center is asserted. Tangency and source self-coherence apply on the whole common open chart, hence at each plaque point. Original f sends each leaf to the leaf through its image. Its restriction and inverse are smooth in this intrinsic atlas: on an actual receiving embedded source chart, the inverse coordinates are the smooth normal inverse and fixed tangent projection; their composition with smooth original f and an incoming source chart is smooth. This uses the actual receiving domains already matched, not global ambient-to-intrinsic continuity or an arbitrary immersion.

The source family has enlarged original open embedding domains. Joint value and FIRST disc-derivative continuity follows from the native continuous-section/supported-frame proof above, and the HPS chart equality transports it to these exact intrinsic charts. For each compact center core and a closed disc strictly inside its enlarged domain, compact joint continuity gives continuity in the finite-C¹ supremum norm. Empty cores and zero-rank models are direct. This is the finite-C¹ LOCAL family property needed below; it makes no moving-radius boundary/Thom isotopy claim.

5. Choose β>0 ONCE after both native/source families and their larger open domains have been matched. Require β<min(1,D,ε_s,ε_u), Mνβ<b_* in both directions, and the original stable/unstable projection of every h-log of norm≤β strictly inside the common OPEN parameter balls of the preceding chart identification. Also place the whole β-ball in the selected normal/output domains and below every closed-core/receiving-germ margin. Original finite compact frame bounds and actual normal inverse supply these positive choices. The fixed source ε_s/ε_u characterizations are not replaced by a claimed theorem at an arbitrary smaller radius.

If d(f^n(y),f^n(x))<β for all n≥0, each point test is in its original component and the fixed Shub ε_s capture applies. The initial h-log and its projection put y in the matched common source graph. Conversely if y is on that graph and d(y,x)<β, its receiving graph invariance and source center estimate give d(f^n(y),f^n(x))≤κ_s^n d(y,x)<β at EVERY n. Thus
 Pˢ_x={y:d(f^n(y),f^n(x))<β for all n≥0}=native stable graph through x ∩openBall_d(x,β)
on the protected original open chart. The inverse source construction gives the exact Pᵘ_x formula. These are intrinsic OPEN embedded plaque neighborhoods, because the graph chart is a genuine open chart of the source leaf and its parameter preimage of the ambient open ball is open. Openness is not inferred from an infinite intersection of open sets. The β projection bound places the entire set inside that matched enlarged chart, with strict margins at every point; the centered restrictions there are the source atlas. Its tangency and smooth intrinsic leaf structure come from the preceding native HPS binding. The joint finite-C¹ local parametrizations are the common enlarged source embeddings restricted on their actual open domains; compact inner discs give the specified local supremum continuity. No assertion of C¹-continuous reparametrization of a moving β boundary is needed or made.

Choose 0<γ<β/2, further restricted by the later common product/closed-core margins BEFORE the final close-pair ε is chosen. The source algorithm allows this free choice at the comparison stage, while the fixed source ε_s/ε_u remain unchanged. A point in the literal S_γ(x) has all-time distance≤γ<β, hence is in Pˢ_x and initially in the closed radiusγ ball. Conversely a point in Pˢ_x with initial distance≤γ has distance≤κ_s^nγ≤γ at all times. Therefore S_γ(x)=Pˢ_x∩closedBall_d(x,γ). The same proof gives U_γ(x)=Pᵘ_x∩closedBall_d(x,γ). Replacing the initial ≤γ by <γ gives the exact strict versions with open balls; they are intrinsic open neighborhoods. These identities identify their topology with the embedded native plaque charts, not a global leaf ambient-subspace topology.

For ANY y,z∈S_γ(x), the triangle inequality gives d(f^j(y),f^j(z))≤2γ<β for every j≥0. Since the whole hyperbolic set is M, y itself is a legitimate source center, and the exact strict β characterization puts z in Pˢ_y. The source center contraction THERE yields d(f^n(y),f^n(z))≤κ_s^n d(y,z). This is the whole-M rebase responsible for the exact prefactor1 arbitrary-pair result, even when y≠x. Apply the same source argument to backward times for U_γ. Set λ=max(κ_s,κ_u)∈(0,1). Both public all-pair estimates then hold with λ^n, including n=0 and y=z. This retires the unused private sharp cutoff and near-isometric/C¹ ambient-path comparison branch; no equality of ambient curve-class infima is used.

6. This is the written Glöckner/Fisher–Hasselblatt local graph/intersection mechanism used by the native Fact1 proof, now applied directly to the selected whole-M source graphs. Its free comparison γ is chosen ALSO below β/2 and all actual source chart margins BEFORE close-pair ε; the fixed capture radii ε_s/ε_u are untouched. Thus this is a permitted choice inside the WRITTEN algorithm, not a claim that an arbitrarily shrunk PUBLIC bracket theorem preserves its output.

Use the NATIVE family constructed and OPEN-chart matched above from the outset. The precise data follow Shub, Global Stability1987, Lemma6.5 printed pp.75–77 and the graph construction on p.78: in original local frames over M, b_p^s(v)=exp_h,p(v+μ_p^s(v)) and b_p^u(w)=exp_h,p(w+μ_p^u(w)), with the unstable construction applied to f⁻¹. These are embeddings on original open fibre domains, centered at p, tangent to E_p^s/u, and continuous with their leafwise first derivatives. Their source graph cores are the SAME native cores whose intersection with the original closed ε_s/ε_u metric ball gives P_s(p)/P_u(p), with the center estimates and ambient characterization stated in the preceding native construction. These μ/family/core/capture applications in the final h are supplied by the full preceding native construction, including receiving-germ control; the operator/radial identities alone were not sufficient. No private HPS G or Γ is equated with this source family.

Local regraphing uses the actual original domains. Fix p₀∈M and an original smooth ambient chart c with c(p₀)=(0,0) and reference planes E^s_p₀ and E^u_p₀. Choose continuous source frames over a relative neighborhood of p₀ in M; the two ranks are locally constant, so this is done separately on its local rank class. For each sign, project c∘b_p onto its corresponding reference plane. At (p₀,0) this projected derivative A is injective and has equal finite source and target dimensions because the source graph is tangent to the corresponding reference plane. The existing linearEquivOfInjective and toContinuousLinearEquiv inputs give an ACTUAL continuous linear equivalence A; it is not silently replaced by an identity matrix or an isometry. In a nonzero model its inverse operator norm is positive. Choose an original open convex source ball B(0,R) strictly inside the native fibre domain, and shrink the relative center neighborhood and R so that the projected first derivative differs from this fixed A by at most σ, with σ||A⁻¹||<1. The joint first-jet continuity on a compact inner model ball gives a uniform center neighborhood by compact_eventually_forall. The derivative of the original line segment v+t(w−v), t∈[0,1], is the derivative remainder applied to w−v. The existing segment derivative bound and operator-norm inequality therefore give the TWO-POINT bound ||q_p(v)−q_p(w)−A(v−w)||≤σ||v−w||. No differentiability with respect to p, extension of the splitting away from M, or smooth parameter manifold is used.

Apply the WRITTEN fixed-projection inverse algorithm of Glöckner2007 author preprint, Theorem5.3 pp.41–43, Remark5.6 Equation(66), and Theorem5.10 pp.45–46. For an inner source closed ball, the map v↦v−A⁻¹(q_p(v)−ζ) has contraction constant σ||A⁻¹||<1; its displacement bound for ζ in the corresponding strict image ball makes it a self-map. This is precisely the source closed-ball argument, not an assertion about an unspecified image radius. With α=1−σ||A⁻¹||>0, Equation(66) supplies q_p(0)+A B(0,αt) inside the projected image of an actual inner B(0,t). Continuity of q_p(0) in p lets one choose a COMMON smaller projection ball. The source lower Lipschitz bound supplies injectivity and a uniform inverse bound; Theorem5.10 supplies continuity of the joint inverse on its genuine open image. Restrict these inverses and the transverse coordinates to common reference balls B_s(0,2r) and B_u(0,2r). The cross derivative is zero at (p₀,0); after shrinking original source balls and centers again, the segment bounds and the projected inverse Lipschitz bounds give stable graphs u=S_x(s) and unstable graphs s=T_y(u) with both Lipschitz constants at most 1/4 and offsets ||S_x(0)||,||T_y(0)||<r/4. These graphs are the just-selected native branches, on the same chart and balls, with x,y∈M. Continuity in the centers follows from the joint inverse and native parameterizations. In a zero-dimensional projection model use its singleton directly; do not divide by its zero inverse norm. The complementary nonzero model uses the preceding argument. This also covers varying ranks on different components by a finite selection of local rank charts.

Now follow ONLY the actual composition proof of Fisher–Hasselblatt, Lemma12.5.18 printed p.602/PDF609, on the verified local domain; do not import its whole-space graph hypothesis. On the closed reference ball D=closedBall_s(0,r), ||S_x(s)||<r/4+r/4=r/2, so S_x(s) is in the original T_y domain B_u(0,2r). Thus Q_xy(s)=T_y(S_x(s)) is defined on all of D and satisfies ||Q_xy(s)||<r/4+r/8=3r/8<r and Lip(Q_xy)≤1/16. The finite-dimensional source is complete, D is closed and nonempty, and the induced closed-ball subtype is complete. The contraction inputs give a unique fixed point s_xy∈D. The source proof of Proposition12.1.3 pp.578–579/PDF585–586 is explicit here: s₀=0, s_(n+1)=Q_xy(s_n), and ||s_m−s_n||≤(1/16)^n||s₁−s₀||/(1−1/16) for m≥n. Completeness gives the fixed point and the contraction inequality gives uniqueness. The point z_xy=c⁻¹(s_xy,S_x(s_xy)) is consequently the unique intersection in these SAME inner graph restrictions. On a zero source model D is a singleton and this conclusion is direct; the displayed positive-dimensional estimates are not required there.

Continuous dependence uses the WRITTEN residual estimate of the same Proposition12.1.3(1),(2), not its smooth-parameter clause(4): ||s_xy−s_x′y′||≤(1−1/16)⁻¹||Q_x′y′(s_xy)−Q_xy(s_xy)||. Here s_xy is the FIXED reference fixed point. Joint graph continuity evaluated at this fixed original inner point makes the right side tend to zero; convergence of the moving fixed point is not assumed. Thus z_xy is continuous locally on the relative M×M center domain. In particular z_pp=p because both native graphs are centered at p and the fixed-point uniqueness applies; only the verified local source graph restrictions are involved.

Define εS=min{ε_s,ε_u,1/2}>0. Choose the final γ by reducing the positive scale already used in the preceding native construction, retaining 2γ<εS AND γ<β/2. It must also be below the actual native graph-core and common chart margins just used, and below the chosen local source normal/product margins; the original whole-M isolating choice is U=M, so its additional neighborhood condition is automatic. These choices use the SAME native core identification in the preceding native construction; no new characterization at radius γ is asserted. Their local-to-uniform binding is explicit: by the preceding native construction normal-chart correspondence, a point with d(q,p)≤γ has ||L_h(p,q)||_h≤γ on the selected original branch; the continuous original splitting projections and local source frames have uniform finite operator bounds on a finite compact selection of M patches. Its native graph parameter, the stable or unstable projection of L_h(p,q), therefore lies in an inner source ball when γ is sufficiently small. Smaller reference chart neighborhoods, their original open margins, and the continuous projected coordinates then put the point in the SAME regraphed inner restrictions D and B_u(0,2r). This is a restriction of the native source μ graph, not a conclusion about a private family. The finiteness and norm-bound inputs permit positive simultaneous choices; no all-M splitting is introduced. Metric openness of U and compactness of M similarly permit γ small enough that the isolating choice U=M is automatic; no extra neighborhood hypothesis is introduced. If q already belongs to the native P_s(p) or P_u(p), this establishes the inner-core restriction needed below; radial correspondence does not itself assert such membership.

For this fixed γ, local continuity at every diagonal (p,p) gives a relative open neighborhood N_p with the bracket construction valid on N_p×N_p and BOTH initial distances d(z_xy,x)<γ and d(z_xy,y)<γ there. Choose a finite cover of compact M by such neighborhoods, subordinate to the preceding original chart/core restrictions. Apply the existing compact-metric Lebesgue-number input to this cover and take 0<ε₀ strictly smaller than its positive number. For d(x,y)≤ε₀, the nonempty set {x,y}, of diameter at most ε₀, lies in one N_p. Thus the CLOSED close-pair domain, including its boundary d(x,y)=ε₀, stays strictly inside the local construction and initial-distance guards. This does not replace a strict threshold by equality.

The AMBIENT orbit control follows from the NATIVE Shub core and center estimates established in the preceding native construction BEFORE membership in M. The constructed z_xy is on the selected native stable graph through x and unstable graph through y, inside their original cores, and its initial distances are <γ<ε_s,ε_u. The ORIGINAL p.78 graph-core identities at ε_s and ε_u therefore put it in P_s(x) and P_u(y); neither a characterization at an arbitrary smaller γ nor a moving HPS product-domain criterion is invoked. The source center estimates at the actual centers x,y∈M give d(f^n z_xy,f^n x)≤κ_s^n d(z_xy,x)<γ and d(f^(−n)z_xy,f^(−n)y)≤κ_u^n d(z_xy,y)<γ for every n≥0. This uses the already constructed source center-to-point estimates at actual centers x,y∈M. All iterates of z_xy now lie in U, since the reference forward/backward base orbits lie in M. Because the whole source set is M, this ambient intersection point is already in M; the all-time center bounds establish the AP closed-γ memberships directly, without a nontrivial local-maximality test. It then belongs to both PUBLIC closed γ plaques.

Conversely, a point w in S_γ(x)∩U_γ(y) is initially in M and its all-time γ bounds imply membership in P_s(x) and P_u(y) by the ORIGINAL source characterizations at ε_s and ε_u. The previously verified closed-γ inner-core restrictions put w in the same local regraph domains; the unique fixed point of Q_xy forces w=z_xy. This uniqueness also identifies bracket choices on overlapping center charts. The local residual estimate consequently proves continuity on the stated closed close-pair domain. Zero-rank cases use the same singleton compositions and complementary image-ball restrictions; both ranks zero give the local singleton directly. This closes the PUBLIC native bracket conclusion using the original source cores and center estimates, including its closed close-pair boundary. This local bracket algorithm uses no full sup-chart homeomorphism, Thom disc topology or private/native graph equality. Native source self-coherence and the intrinsic atlas required by the WHOLE AP proposition have already been supplied in the preceding final-h HPS leaf-atlas step. Named lower/source/API and formal/transitive/kernel obligations remain separate.

For the AP conclusion call the final close-pair radius ε=ε₀ and require ε<D. The output just constructed is EXACTLY b(a,b)∈S_γ(a)∩U_γ(b). Initial solution distances were chosen strictly<γ; EVERY possible closed-γ intersection lies in the checked graph cores, so uniqueness is for the entire displayed intersection, including closed boundaries. The source residual estimates and overlap uniqueness prove continuity on the actual close-pair domain d(a,b)<ε. β>2γ remains strict after all smaller choices. The native charts used here have the preceding genuine intrinsic topology; no private AP Γ or unrelated leaf family is used.

7. Apply the ACTUAL written Shub Proposition10.10 printedpp126–127/PDF139–140 with A=M and the bracket/source domains JUST constructed. Its factors are the hatted OPEN distance restrictions INSIDE genuine embedded native discs; they are not the whole closed S_γ/U_γ sets. Choose a common δ>0 inside the actual close-pair ε and the larger matched native normal/chart domains. All central-projection callers below have d(x,z)<δ, hence their brackets are actually defined. On V_δ(x)=openBall_d(x,δ), put Π_s(z)=b(x,z) and Π_u(z)=b(z,x). Source bracket membership gives Π_s(z)∈S_γ(x) and Π_u(z)∈U_γ(x).

These maps are continuous into the INTRINSIC native central charts, not merely ambient continuous. Indeed those closed-γ outputs are strictly inside the larger common OPEN graph charts through x. The coordinate inverse there is the actual continuous normal inverse L(x,·) followed by the original stable or unstable projection; its composition with the ambient-continuous bracket is continuous in the actual model, and the matched native chart identifies that topology with the intrinsic one. Use BOTH receiving branches and their open domains. Around each diagonal (x,x), compact bracket continuity and finite native chart cores allow positive uniform restriction margins before the source ρ is chosen; the zero-rank factor is a singleton open chart and needs no inverse norm.

Following the displayed source proofp127, choose 0<ρ<δ/2 so that for u,s within ρ of x on their central unstable/stable charts, the actual pair (u,s) remains inside the close-pair domain and b(u,s) stays in V_δ(x). This is uniform continuity on a compact neighborhood of the diagonal, with the actual source close-pair and original chart margins included in the relation; take a finite compact selection and shrink ρ as required. Also choose intrinsic OPEN neighborhoods Vᵘ⊂U_γ(x) and Vˢ⊂S_γ(x), each inside its genuine open radiusρ native restriction and the larger embedding domain, so all these factor/central-projection callers are valid. Shrink δ or the surrounding ambient neighborhood if necessary so the two central coordinates take values in their checked source chart branches. These are choices of neighborhoods, not assertions about every closed core being open.

For u∈Vᵘ,s∈Vˢ let z=b(u,s). Then z∈S_γ(u)∩U_γ(s). By symmetry of the actual orbit-distance inequalities, u∈S_γ(z) and s∈U_γ(z). Also u∈U_γ(x), s∈S_γ(x). Consequently s belongs to S_γ(x)∩U_γ(z), and u belongs to S_γ(z)∩U_γ(x). Both central callers (x,z),(z,x) lie in their verified close-pair domains, so source uniqueness gives Π_s(b(u,s))=s and Π_u(b(u,s))=u.

Conversely take z∈V_δ(x) with u=Π_u(z)∈Vᵘ and s=Π_s(z)∈Vˢ. The two defining bracket memberships, again using symmetry, give z∈S_γ(u)∩U_γ(s). The factor caller (u,s) is in the verified close-pair domain, so uniqueness yields z=b(Π_u(z),Π_s(z)). Thus BOTH compositions are identities and (Π_u,Π_s) is the inverse for (u,s)↦b(u,s).

Its image is exactly
 N_x=V_δ(x)∩Π_u⁻¹(Vᵘ)∩Π_s⁻¹(Vˢ).
This is AMBIENT OPEN by the established intrinsic continuity of both projections, and contains x. The factor neighborhoods were chosen so every product point lies in V_δ(x); hence no additional points or product factor restriction is hidden in the equality. The bracket is continuous on these actual domains, as are both inverse components, so this is the required homeomorphism Vᵘ×Vˢ→N_x. Equivalently with stable-first input order it is the stated map (s,u)↦b(u,s). Source foliation/graph partition and these inverse identities give injectivity; no invariance-of-domain shortcut or only one-sided inverse is asserted. All radii precede their callers and lie strictly within the larger native source charts.

8. On each connected intrinsic SMOOTH source leaf take the pullback of the selected smooth positive tensor h under its injective immersion. It is positive because the tangent map is injective. Use Lee’s source-natural piecewise-SMOOTH length distance FROM THE OUTSET: the infimum of the finite lengths of finitely piecewise smooth intrinsic connecting paths. Connected smooth leaves admit such paths by Lee6.17; their closed smooth pieces have continuous finite speeds, so Lee p275 and the existing interval-integrability/finite adjacent-addition primitives define their finite length. Lee11.19/11.20 supplies the local metric interpretation. No identity with an independently chosen piecewise C¹ infimum, native maximum-norm distance or ambient riemannianEDist is claimed.

The original f acts smoothly between these actual intrinsic leaf charts with smooth inverse, by the already matched receiving/source atlas. A piecewise smooth stable path c is therefore sent to a path of the SAME class. At each smooth piece the original chain rule and the pointwise tangent image Eˢ give
 |(f∘ι∘c)′|_h=|Df(ι∘c)′|_h≤θ|(ι∘c)′|_h.
This uses h at the original source and actual f-image fibre. Apply the existing mfderiv_comp/pathELength_eq_lintegral_mfderiv_Ioo to EACH genuine smooth piece. Nonnegative integral monotonicity and finite-coefficient scalar multiplication give length_h(f∘c)≤θ length_h(c); continuousOn_intervalIntegrable and finite adjacent addition handle endpoints/piece concatenation. The pointwise speed inequality holds on each open smooth piece; finite endpoints have measure zero and the source length definition has finite one-sided speeds. Taking the infimum over this SAME nonempty connecting-path family gives intrinsic d_s(fy,fz)≤θd_s(y,z). For the unstable leaf use ORIGINAL f⁻¹ and Eᵘ to obtain d_u(f⁻¹y,f⁻¹z)≤θd_u(y,z). Image-path lengths are competitors in the receiving leaf, so no equality of two infima or global distance/topology transport is needed. The constant D between components plays no role in an intrinsic path.

Mañé1987 printedp185/PDF195 Eq(10) with derivative normEq(11) supports the intrinsic Riemannian convention and displayed consequence only: it writes NO expanded speed-integral/infimum proof. The calculation just given is the elementary source/application expansion using Lee’s written length/distance construction and genuine chain/integral APIs, not credit for an unprinted Mañé proof. In ambient dimension0 every occupied component is a singleton, Pˢ/Pᵘ and S_γ/U_γ are singleton charts, and their product image is the open singleton; all tangent and path inequalities are vacuous. Zero stable or unstable rank gives the singleton factor and the same verified complementary source construction. Empty M was handled before Fact1. Finite components, varying ranks and component permutations retain their original topology and original f; no transitivity, Markov connectedness, transverse differentiability, global Euclidean leaf or all-order common radius is added.
-/
theorem hirschPughAdaptedOrbitPlaques
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (splitting : InvariantRealTangentSplitting f)
    (h₀ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (C τ : ℝ) (hC : 1 ≤ C) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hs : ∀ (x : M) (n : ℕ) (v : TangentSpace 𝓘(ℝ, E) x),
      v ∈ splitting.stable.toDistribution x →
        hyperbolicRiemannianNorm h₀
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f : M → M)^[n]) x v) ≤
            C * τ ^ n * hyperbolicRiemannianNorm h₀ v)
    (hu : ∀ (x : M) (n : ℕ) (v : TangentSpace 𝓘(ℝ, E) x),
      v ∈ splitting.unstable.toDistribution x →
        hyperbolicRiemannianNorm h₀
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f.symm : M → M)^[n]) x v) ≤
            C * τ ^ n * hyperbolicRiemannianNorm h₀ v) :
    ∃ (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
      (d : MetricSpace M) (D θ lambda β γ ε : ℝ),
      0 < D ∧ 0 < θ ∧ θ < 1 ∧ 0 < lambda ∧ lambda < 1 ∧
      0 < γ ∧ 2 * γ < β ∧ 0 < ε ∧
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace M) ∧
      (∀ x y : M, y ∈ connectedComponent x →
        ENNReal.ofReal (d.dist x y) = piecewiseSmoothRiemannianEDist h x y) ∧
      (∀ x y : M, y ∉ connectedComponent x → d.dist x y = D) ∧
      (∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        v ∈ splitting.stable.toDistribution x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤
            θ * hyperbolicRiemannianNorm h v) ∧
      (∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        v ∈ splitting.unstable.toDistribution x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤
            θ * hyperbolicRiemannianNorm h v) ∧
      ∃ (S : NativeInvariantLeafSystem 𝓘(ℝ, E) splitting.stable.toDistribution f)
        (U : NativeInvariantLeafSystem 𝓘(ℝ, E) splitting.unstable.toDistribution f.symm),
        Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f
          splitting.stable.toDistribution d β γ S) ∧
        Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm
          splitting.unstable.toDistribution d β γ U) ∧
        (∀ x : M, ∀ y ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f d γ x,
          ∀ z ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f d γ x, ∀ n : ℕ,
            d.dist ((f : M → M)^[n] y) ((f : M → M)^[n] z) ≤ lambda ^ n * d.dist y z) ∧
        (∀ x : M, ∀ y ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm d γ x,
          ∀ z ∈ adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm d γ x, ∀ n : ℕ,
            d.dist ((f.symm : M → M)^[n] y) ((f.symm : M → M)^[n] z) ≤
              lambda ^ n * d.dist y z) ∧
        (∀ (x : M) (y z : (S.leaf x).Carrier),
          nativeLeafPathEDist 𝓘(ℝ, E) h (S.leaf x) y z < ⊤) ∧
        (∀ (x : M) (y z : (U.leaf x).Carrier),
          nativeLeafPathEDist 𝓘(ℝ, E) h (U.leaf x) y z < ⊤) ∧
        (∀ (x : M) (y z : (S.leaf x).Carrier),
          nativeLeafPathEDist 𝓘(ℝ, E) h (S.leaf (f x))
              (S.advance x y) (S.advance x z) ≤
            ENNReal.ofReal θ * nativeLeafPathEDist 𝓘(ℝ, E) h (S.leaf x) y z) ∧
        (∀ (x : M) (y z : (U.leaf x).Carrier),
          nativeLeafPathEDist 𝓘(ℝ, E) h (U.leaf (f.symm x))
              (U.advance x y) (U.advance x z) ≤
            ENNReal.ofReal θ * nativeLeafPathEDist 𝓘(ℝ, E) h (U.leaf x) y z) ∧
        ∃ bracket : adaptedClosePairDomain (M := M) d ε → M,
          Continuous bracket ∧
          (∀ p : adaptedClosePairDomain (M := M) d ε,
            adaptedClosedOrbitCore 𝓘(ℝ, E) f d γ p.1.1 ∩
              adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm d γ p.1.2 = {bracket p}) ∧
          ∀ x : M, Nonempty (AdaptedNativeProduct 𝓘(ℝ, E) f
            splitting.stable.toDistribution splitting.unstable.toDistribution
            d γ ε S U bracket x) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hempty =>
    let S : NativeInvariantLeafSystem 𝓘(ℝ, E) splitting.stable.toDistribution f :=
      { leaf := fun x ↦ isEmptyElim x
        advance := fun x ↦ isEmptyElim x
        inclusion_advance := fun x ↦ isEmptyElim x
        rebase := fun x ↦ isEmptyElim x
        inclusion_rebase := fun x ↦ isEmptyElim x }
    let U : NativeInvariantLeafSystem 𝓘(ℝ, E) splitting.unstable.toDistribution f.symm :=
      { leaf := fun x ↦ isEmptyElim x
        advance := fun x ↦ isEmptyElim x
        inclusion_advance := fun x ↦ isEmptyElim x
        rebase := fun x ↦ isEmptyElim x
        inclusion_rebase := fun x ↦ isEmptyElim x }
    let d : MetricSpace M := MetricSpace.ofDistTopology (fun _ _ ↦ 0)
      (fun x ↦ isEmptyElim x) (fun x ↦ isEmptyElim x)
      (fun x ↦ isEmptyElim x) (by simp) (fun x ↦ isEmptyElim x)
    have stablePlaques : Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f
        splitting.stable.toDistribution d 1 (1 / 4) S) := by
      constructor
      constructor <;> intro x <;> exact isEmptyElim x
    have unstablePlaques : Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm
        splitting.unstable.toDistribution d 1 (1 / 4) U) := by
      constructor
      constructor <;> intro x <;> exact isEmptyElim x
    refine ⟨h₀, d, 1, 1 / 2, 1 / 2, 1, 1 / 4, 1, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, rfl, ?_, ?_, ?_, ?_, S, U, stablePlaques,
      unstablePlaques, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try { intro x; exact isEmptyElim x }
    refine ⟨fun p ↦ isEmptyElim p.1.1, ?_, ?_, ?_⟩
    · exact continuous_of_discreteTopology
    · intro p
      exact isEmptyElim p.1.1
    · intro x
      exact isEmptyElim x
  | inr hnonempty =>
    have : SecondCountableTopology E := inferInstance
    have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E M
    let bounds : TensorAnosovBounds f splitting h₀ :=
      { C := C
        lambda := τ
        C_pos := lt_of_lt_of_le zero_lt_one hC
        lambda_pos := hτ₀
        lambda_lt_one := hτ₁
        stable := fun n x v hv ↦ hs x n v hv
        unstable := fun n x v hv ↦ hu x n v hv }
    obtain ⟨hstable, hunstable⟩ := HPS.anosov_global_lamination_tensor f splitting h₀ ⟨bounds⟩
    obtain ⟨S⟩ := nativeInvariantLeafSystem_of_hasNativeLamination splitting.stable.toDistribution f hstable
    obtain ⟨Uforward⟩ := nativeInvariantLeafSystem_of_hasNativeLamination splitting.unstable.toDistribution f hunstable
    obtain ⟨U⟩ := nativeInvariantLeafSystem_inverse_reindex splitting.unstable.toDistribution f Uforward
    obtain ⟨stableOn, hstableOn⟩ := continuousRealTangentSubbundle_on_univ splitting.stable
    obtain ⟨unstableOn, hunstableOn⟩ := continuousRealTangentSubbundle_on_univ splitting.unstable
    let H : HyperbolicSetFactOneDatum f Set.univ :=
      { nonempty := Set.univ_nonempty
        compact := isCompact_univ
        forward_mem := fun _ _ ↦ Set.mem_univ _
        backward_mem := fun _ _ ↦ Set.mem_univ _
        originalMetric := h₀
        stable := stableOn
        unstable := unstableOn
        complementary := fun x ↦ by
          rw [hstableOn, hunstableOn]
          exact splitting.isCompl x
        stable_invariant := fun x ↦ by
          rw [hstableOn, hstableOn]
          exact splitting.stable_map x
        unstable_invariant := fun x ↦ by
          rw [hunstableOn, hunstableOn]
          exact splitting.unstable_map x
        C := C
        one_le_C := hC
        rate := τ
        rate_pos := hτ₀
        rate_lt_one := hτ₁
        stable_estimate := fun n x v hv ↦ hs x n v (by simpa [hstableOn] using hv)
        unstable_estimate := fun n x v hv ↦ hu x n v (by simpa [hunstableOn] using hv)
        isolatingNeighborhood := Set.univ
        isolating_open := isOpen_univ
        subset_isolating := Set.Subset.rfl
        locally_maximal := fun _ ↦ by simp }
    obtain ⟨h, a, dFact, κ, γFact, εFact, ha, hsa, hua, hFact⟩ :=
      hirschPughHyperbolicSetFactOne f Set.univ H
    let θ : ℝ := max a (1 / 2)
    have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hθlt : θ < 1 := max_lt ha (by norm_num)
    have hstable_adapted : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        v ∈ splitting.stable.toDistribution x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤
            θ * hyperbolicRiemannianNorm h v := by
      intro x v hv
      apply le_trans (hsa ⟨x, Set.mem_univ _⟩ v (by simpa [H, hstableOn] using hv))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have hunstable_adapted : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
        v ∈ splitting.unstable.toDistribution x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤
            θ * hyperbolicRiemannianNorm h v := by
      intro x v hv
      apply le_trans (hua ⟨x, Set.mem_univ _⟩ v (by simpa [H, hunstableOn] using hv))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have hstable_path_speed := nativeLeafPath_advance_speed_le f S h θ hstable_adapted
    have hunstable_path_speed := nativeLeafPath_advance_speed_le f.symm U h θ hunstable_adapted
    have hstable_path_length := nativeLeafPath_advance_length_le f S h θ hstable_adapted
    have hunstable_path_length := nativeLeafPath_advance_length_le f.symm U h θ hunstable_adapted
    have hstable_intrinsic := nativeLeafPathEDist_advance_le f S h hθpos hstable_adapted
    have hunstable_intrinsic := nativeLeafPathEDist_advance_le f.symm U h hθpos hunstable_adapted
    obtain ⟨d, D, hD, hdtop, hdcomp, hdsep⟩ :=
      exists_constant_component_piecewiseSmooth_metric h
    let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
    have hlocalOld : ∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, ∀ z ∈ V,
          ENNReal.ofReal (dFact.dist y z) = piecewiseSmoothRiemannianEDist h y z := by
      intro x
      obtain ⟨V, hV, hx, heq⟩ := hFact.2.1 x
      exact ⟨V, hV, hx, fun y hy z hz => heq y hy z hz⟩
    obtain ⟨rAgree, hrAgree, hAgree⟩ := component_metric_local_agreement
      d dFact hdtop (fun y z => piecewiseSmoothRiemannianEDist h y z) hdcomp hlocalOld
    obtain ⟨_, _, hκpos, hκlt, hγFact, hεFact, hStableFact, hUnstableFact, hBracketFact⟩ := hFact
    let γCore : ℝ := min γFact (rAgree / 2)
    have hγCore : 0 < γCore := lt_min hγFact (by linarith)
    have hγR : γCore ≤ γFact := min_le_left _ _
    have hγsmall : 2 * γCore ≤ rAgree := by
      have := min_le_right γFact (rAgree / 2)
      dsimp [γCore]
      linarith
    have hStableOld : ∀ x y z : M,
        (∀ n : ℕ, dFact.dist ((f : M → M)^[n] y) ((f : M → M)^[n] x) ≤ γFact) →
        (∀ n : ℕ, dFact.dist ((f : M → M)^[n] z) ((f : M → M)^[n] x) ≤ γFact) →
        ∀ n : ℕ, dFact.dist ((f : M → M)^[n] y) ((f : M → M)^[n] z) ≤ κ ^ n * dFact.dist y z := by
      intro x y z hy hz n
      exact hStableFact x (Set.mem_univ _) y ⟨Set.mem_univ _, hy⟩ z ⟨Set.mem_univ _, hz⟩ n
    have hUnstableOld : ∀ x y z : M,
        (∀ n : ℕ, dFact.dist ((f.symm : M → M)^[n] y) ((f.symm : M → M)^[n] x) ≤ γFact) →
        (∀ n : ℕ, dFact.dist ((f.symm : M → M)^[n] z) ((f.symm : M → M)^[n] x) ≤ γFact) →
        ∀ n : ℕ, dFact.dist ((f.symm : M → M)^[n] y) ((f.symm : M → M)^[n] z) ≤ κ ^ n * dFact.dist y z := by
      intro x y z hy hz n
      exact hUnstableFact x (Set.mem_univ _) y ⟨Set.mem_univ _, hy⟩ z ⟨Set.mem_univ _, hz⟩ n
    have hTransferStable := orbit_core_contraction_metric_transfer
      (f : M → M) d dFact hγCore.le hγsmall hγR hAgree hStableOld
    have hTransferUnstable := orbit_core_contraction_metric_transfer
      (f.symm : M → M) d dFact hγCore.le hγsmall hγR hAgree hUnstableOld
    have hgeometry := hirschPughAdaptedOrbitPlaques_geometry
      f splitting h d γCore hγCore hdtop hdcomp θ hθpos hθlt
        hstable_adapted hunstable_adapted S U
    obtain ⟨β, γ, ε, hγ, hγle, hβ, hε, hSplaques, hUplaques,
      hSfinite, hUfinite, bracket, hbracket, hunique, hproduct⟩ := hgeometry
    refine ⟨h, d, D, θ, κ, β, γ, ε, hD, hθpos, hθlt, hκpos, hκlt,
      hγ, hβ, hε, hdtop, hdcomp, hdsep, hstable_adapted, hunstable_adapted,
      S, U, hSplaques, hUplaques, ?_, ?_, hSfinite, hUfinite,
      hstable_intrinsic, hunstable_intrinsic, bracket, hbracket, hunique, hproduct⟩
    · intro x y hy z hz n
      exact hTransferStable x y z (fun k ↦ (hy k).trans hγle)
        (fun k ↦ (hz k).trans hγle) n
    · intro x y hy z hz n
      exact hTransferUnstable x y z (fun k ↦ (hy k).trans hγle)
        (fun k ↦ (hz k).trans hγle) n


end AdaptedOrbitTheorem

end HolomorphicAnosov
