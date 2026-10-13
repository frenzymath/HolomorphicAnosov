import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphBoundedForcing
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJetIdentification
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSmoothInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphZeroDerivative
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableOrbit
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableTransverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableOrbitConverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableOrbitCharacterization
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstableTransverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstableOrbitConverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstablePreimageBound
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstableOrbit
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstableOrbitCharacterization
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphContractionThreshold
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierComplete
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierRealization
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierMetric
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageCarrier
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableLipschitz
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageCarrier
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphInvariantLipschitz
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageDerivative
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPointReturnContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedDiscContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphChartAction
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasDerivative
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomChartContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLinearTangentZero
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomCoordinates
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageDerivative
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAffinePreimage
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLinearPerturbation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPointReturnSection
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAffineImage
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimagePointComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImagePointComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJetTransport
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageJetComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageJetComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedPoint
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageWeightedComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFibreComplete
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFrameNormBounds
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphOriginalNormBounds
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedGraphRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUniformThreshold
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTangentEquation
import HolomorphicAnosov.Analysis.BoundedContinuousInvariantSections
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJets
import HolomorphicAnosov.Analysis.WellsLipschitzPerturbationSmoothInverse
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Parameter graph construction on a locally finite-rank split real bundle

Source: Hirsch--Pugh--Shub, *Invariant Manifolds*, LNM 583 (1977), pp.53--62,
with the precise source-composite proof in the theorem docstring below.
The genuine bundle and fibre-jet setting is imported from its landed definition module.
-/

noncomputable section

open Set _root_.Topology

namespace HolomorphicAnosov

variable {A : Type*} [TopologicalSpace A] {E₁ E₂ : A → Type*}
  [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
  [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
  [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
  [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]

/-- HPS parameter graph construction in the original locally finite-rank split bundle.

Source: Human written-source COMPOSITE for the unchanged original moving-bundle theorem.
Hirsch–Pugh–Shub, Invariant Manifolds (LNM583,1977): bounded sections3.1p25/PDF29, Lipschitz
jets3.3pp27–29/PDF31–33, compact forcing/Finsler/own-jet/continuous-Hom
inductionpp32–35/PDF36–39, unit discs p36/PDF40; Theorem5.1/Sublemma5.2 image and full-preimage
graph constructionspp53–58/PDF57–62, direct singular reverse-relation p58/PDF62,
cone/closed-preimage/orbit argumentspp58–60/PDF62–64, local strong graphs5.4pp60–61/PDF64–65 and
explicit parameter insertion in first5.5proofp62/PDF66. John C. Wells, Invariant manifolds of
non-linear operators (PJM62(1),1976),pp285–287/PDF2–4: original identity perturbation inverse,
ordinary Frechet finite-order inverse induction, correct NEXT Inverse composed with Df composed
with inverse and finite P_k proof onp287. Its isolated malformed derivative line is disclosed and
not used; global C_U^r assumptions are not imported. James R. Munkres,
Topology2ed(2000),Theorem26.7 Step1/Step2pp167–168/PDF184–185 and Lemma26.8p168/PDF185: actual
compact-model-slice tube and finite OPEN cover proof, no separation assumption. Helge Gloeckner,
Finite order differentiability properties, fixed points and implicit functions over valued
fields,arXiv:math/0511218v2(revised27April2007),AUTHOR PREPRINT5.3/Remark5.6Eq66pp41–43
and5.10(a–c)pp45–47/Cor5.12p47: quantitative closed-ball/image-ball/full-W joint inverse,
arbitrary topological parameter;5.13 smooth-parameter theorem is not invoked. Original norm
suprema, finite thresholds, complete dependent carriers, Neumann UNIT before inverse estimates,
exact state derivative/norm/compactness APIs are bound in the proof. Steps9–12 substantively
reconstruct original inward discs, known forcing/Lipschitz preparation, actual finite C0 return
anchors/outward same-graph germs, triangular STATE inverse retaining SOURCE lower factor, joint
higher inverse jets and compact fixed-disc C^r-sup continuity. Quantitative
frame/derivative/domain bindings and finite P_m multilinear terms are explicit applications of
the written mechanisms, not claimed verbatim printed. Complete at ONE LEVEL relative to named
lower providers; no single verbatim arbitrary-A theorem, purely published-source claim,
transitive DAG/Lean/kernel completion or ambient plaque/global Euclidean/self-coherence theorem.

Complete natural-language proof of the node:

1a. Treat A=∅ first: every asserted family and orbit statement is vacuous, so no real supremum
over an empty set is used. Henceforth A is nonempty. All norms below are the ORIGINAL fibre norms
and their supplied product maximum norm; no adapted norm or norm-defined replacement topology is
introduced. Derive the operator-norm and compact-supremum guards before any graph, graph fixed
point or derivative section is constructed.

Fix p₀ and genuine real-linear source charts near p₀ and receiving charts near h(p₀), with
finite-dimensional real normed models. Restrict the source base to V⊆U_src∩h⁻¹(U_recv). The
assumed continuity of h and T, the genuine forward charts and
Bundle.Trivialization.continuousOn_symm imply, for every fixed model vector v, continuity of
p↦τ_recv,h(p) T_j,p τ_src,p⁻¹v. Each chart fibre map is an actual continuous linear equivalence
by Bundle.Trivialization.continuousLinearEquivAt. Each T₁,p linear isomorphism upgrades, with its
original source and receiving norms, by linearEquiv_toContinuousLinearEquiv; finite-dimensional
Hausdorff real normed spaces satisfy its hypotheses. The exact
finiteDimensional_continuous_clm_apply theorem turns the fixed-v continuity into operator-norm
continuity of the model matrices A_j(p). For A₁(p), the finite-dimensional source model is
complete by finite_dimensional_complete; the existing ContDiffAt operator-inverse theorem
therefore implies continuity of A₁(p)⁻¹. Continuous.clm_apply and the genuine charts give
continuity of the ORIGINAL total inverse map (p,u)↦T₁,p⁻¹u, u∈E₁,h(p). These are precisely the
graph-independent inverse-family ingredients of3a, proved here before3b. No smoothness of h,
global trivialization or graph construction is used.

For clarity derive the generic original-norm comparisons and original Hom-norm continuity
directly, rather than invoking step2 or6 as whole theorems. For a nonzero finite real chart model
F, finite_dimensional_proper_real_g8 and isCompact_sphere make its unit sphere S compact; S is
nonempty by normalizing a nonzero vector, and its subtype is CompactSpace. The function
N(p,u)=‖τ_p⁻¹u‖_p on the base-chart subtype times S is jointly continuous by the genuine inverse
chart and the given continuous TOTAL fibre norm. It is positive because u≠0 and τ_p⁻¹ is
injective. Continuous.div makes1/N jointly continuous using pointwise nonvanishing, without
assuming a uniform lower bound. Apply isCompact_continuous_sSup to N and1/N with γ=the base
subtype, β=S, K=univ and α=ℝ. Their compact images are nonempty and bounded above by
isCompact_bddAbove_image; isLUB_csSup supplies their actual pointwise upper bounds. At p₀ both
suprema are positive. Continuity bounds each by its value at p₀ plus1 on a smaller base
neighborhood. Homogeneity after normalizing any nonzero model vector, and the zero-vector case
directly, give constants c>0,C>0 with c‖v‖≤‖τ_p⁻¹v‖_p≤C‖v‖. A zero model is handled directly by
c=C=1, never by positivity of an empty sphere supremum. Source and receiving charts can be
restricted to a common neighborhood, including h-pullbacks for receiving charts.

For any one of these source/receiving pairs, let Q be a model continuous linear map and
P=τ_recv⁻¹ Q τ_src the ORIGINAL fibre map. Its genuine Hom coordinates are Q;
continuousAt_hom_bundle uses those coordinates and the continuous original base projection, with
no smooth-base hypothesis. If the input model F is nonzero, on its compact nonempty unit sphere
define
 R(p,Q,u)=‖τ_recv,p⁻¹(Q u)‖orig/‖τ_src,p⁻¹u‖orig,
where a receiving chart based at h(p) is understood when appropriate. Continuous.clm_apply, the
original inverse charts, h continuity and the given total norm give joint continuity of the
numerator and denominator; the denominator is positive. Continuous.div applies. For every
fixed(p,Q), compactness gives a bounded nonempty ratio image, so isLUB_csSup defines a finite
nonnegative supremum S(p,Q) with every ratio≤S(p,Q). Normalize the model coordinate of any
nonzero original input: real homogeneity shows ‖Pv‖≤S(p,Q)‖v‖. The zero input gives the same
inequality. continuousLinearMap_opNorm_le_bound yields ‖P‖orig≤S(p,Q). Conversely
continuousLinearMap_le_opNorm gives each ratio≤‖P‖orig, and the least-upper-bound clause of
isLUB_csSup yields S(p,Q)≤‖P‖orig. Thus S(p,Q)=‖P‖orig. isCompact_continuous_sSup with γ=the
chart-base subtype times the fixed Hom model proves joint continuity of this ORIGINAL operator
norm. If the input model is zero then every P is zero and its norm is identically0; no
nonempty-sphere premise is asserted. A zero receiving model gives zero ratios and zero operators.
This copies only the graph-independent compact-sphere ratio argument of6a–b, not any P section,
graph or return map. Apply it to the already continuous T₁ inverse model family, whose input is
the receiving E₁ model and output the source E₁ model, and to the T₂ family. Hence the actual
functions α(p)=‖T₁,p⁻¹‖orig and κ(p)=‖T₂,p‖orig are continuous on A in the original topology.

Compact A and isCompact_bddAbove_image give bounded-above ranges α(A),κ(A). They are NONEMPTY
because A is nonempty. Therefore isLUB_csSup applies to the statement's a=sSup α(A) and k=sSup
κ(A), supplying ‖T₁,p⁻¹‖≤a and ‖T₂,p‖≤k for every p. Since every operator norm is nonnegative and
one p exists, a,k≥0. These are genuine suprema of bounded nonempty compact ranges, not the
default value of an unbounded real csSup. If some E₁,p is nonzero, instantiate
continuousLinearEquiv_norm_symm_pos at the actual original continuous linear equivalence
T₁,p:E₁,p≃L[ℝ]E₁,h(p). Its source is nontrivial, so α(p)>0 and hence a>0. Put m₀=1/a only in this
case. Evaluation of T₁,p⁻¹ at T₁,p x gives ‖x‖≤a‖T₁,p x‖, so ‖T₁,p x‖≥m₀‖x‖, including zero x and
zero fibres. If ALL E₁ fibres are zero, every inverse is the zero operator and a=0; omit m₀ and
every reciprocal-a constraint. T₁,p being an isomorphism makes the zero-E₁ stratum h-invariant.
No zero-E₂ stratum invariance is inferred from possibly singular T₂. A single zero fibre merely
supplies its unique zero coordinate in the corresponding carrier; it does not make other fibres'
carriers singletons.

1b. Produce one finite quantitative threshold from the exact strict gaps. The statement gives
ρ>0, a<ρ⁻¹ and k<ρ, hence aρ<1 and ak<1. As real functions of e near0 put
 U(e)=a/(1−ae), V(e)=k+e, b(e)=a/(1−2ae),
 q₁(e)=a(k+e)/(1−ae)², q₂(e)=a(k+e)/(1−2ae),
 q_J(e)=b(e)(k+2e), c₁(e)=V(e)/(1−ae), B(e)=k+2e.
When a>0 also put L(e)=m₀−e and M(e)=m₀−3e. At e=0 the denominators are1 and these values are
respectively a,k,a,ak,ak,ak,k,k and, when defined, m₀,m₀. Require the finite list
 2ae<1; q₁(e)<1; q₂(e)<1; q_J(e)=a(k+2e)/(1−2ae)<1;
 (k+2e)U(e)<1; c₁(e)<ρ; B(e)<ρ;
and when a>0 also m₀−2e>ρ and M(e)>ρ. For e≥0 the latter gives L(e)≥M(e)>ρ; for e>0 it gives
L(e)>M(e)>ρ. In the strong unstable branch ρ≥1 also require U(e)<min(1,ρ⁻¹); in the strong stable
branch ρ≤1 also require V(e)<min(1,ρ). At ρ=1 include BOTH tests. Every applicable strict test
holds at0: ak<1, k<ρ, m₀>ρ when a>0; for ρ≥1, a<ρ⁻¹≤1; for ρ≤1, k<ρ≤1. Thus the branch tests do
not silently assert a<1 for ρ<1 or k<1 for ρ>1.

Each expression is continuous at0 by continuous_add_g8, continuous_sub and continuous_mul and by
continuousAt_div with the actual denominator value1≠0; powers here are finite products. Encode
each lower-bound test with its negated expression so every test has the form f_i(e)<v_i.
filter_tendsto_eventually_lt_const, applied to the real nhds0 filter and f_i(0)<v_i, makes each
test eventual. Index only this FINITE list, including only the applicable branches and reciprocal
tests; filter_eventually_all gives a single neighborhood of0 where all tests hold.
metric_mem_nhds_iff supplies δ>0 whose real open ball about0 lies in that neighborhood. In
particular EVERY 0≤e<δ satisfies all tests. The first test implies both1−ae>0 and1−2ae>0; all
U,V,b,q₁,q₂,q_J,c₁ are nonnegative there. Thus the contraction constants have their actual NNReal
values and all divisions have positive denominators. If a=0, U=b=q₁=q₂=q_J=0 and c₁=V, with no
m₀,L,M or reciprocal-a constraints; the remaining V/B and applicable stable tests still hold for
one δ>0. This threshold depends only on the original compact linear family and the strict gap,
not on a graph fixed point.

1c. Interpret 'sup Lip(G−T) sufficiently small' as a genuine finite uniform Lipschitz bound:
there is a real η≥0 with η<δ such that for EVERY p and z,z' in its ENTIRE original fibre,
 ‖R_p(z)−R_p(z')‖≤η‖z−z'‖, R_p=G_p−T_p.
This is the usual quantified uniform Lipschitz smallness condition in the statement, not a new
hypothesis or an unbounded real csSup interpreted as0. Fibrewise C^r alone does not imply this
global bound. If described using a least global coefficient that may be infinite, first choose an
actual coefficient η strictly above that infimum and below δ; no attainment of an infimum is
assumed. Set ε=(η+δ)/2. Then ε>0, η≤ε<δ, so EVERY original R_p is LipschitzOnWith ⟨ε,ε≥0⟩ on univ
and all the tests of1b hold at the SAME ε. In particular one cannot choose δ/2 indiscriminately
when η is nonzero. Use the constants U,V,b,q₁,q₂,q_J,c₁,L,M,B at this ε in all subsequent steps,
preserving their formulas and the common choice.

The original hypotheses G_p(0)=0 and DG_p(0)=T_p give R_p(0)=0 and DR_p(0)=0. Fibrewise C^r with
r≥1 supplies the actual Fréchet derivative of R_p at every point of the original real normed
product fibre, into the original receiving product fibre. norm_fderiv_le_of_lipschitzOn_g7
applies with k=ℝ, source/receiving real normed spaces, s=univ∈nhds z and NNReal ε, yielding
‖DR_p(z)‖≤ε. Its fderiv is the actual derivative because of the given C^r differentiability. The
coordinate injections and projections of the product maximum norm have operator norm≤1 by their
pointwise norm inequalities; composition with DR therefore bounds each remainder derivative block
by ε. No derivative-quotient theorem or finite-dimensional completeness is needed for this
derivative API. In particular the actual lower diagonal DG block is T₂,p plus its remainder
block, hence has norm≤k+ε. HPS p.54 uses k for a LOWER DERIVATIVE block bound, whereas here k is
the original sup‖T₂,p‖; the source block coefficient is therefore bounded by the current k+ε.
This is an explicit convention conversion, not a source typo or erratum.

Finally le_opNorm and the uniform remainder inequality give, in the ORIGINAL maximum norm, for
Δz=(Δx,Δy),
 ‖ΔG₁‖≥m₀‖Δx‖−ε max(‖Δx‖,‖Δy‖) when a>0,
 ‖ΔG₂‖≤k‖Δy‖+ε max(‖Δx‖,‖Δy‖).
The first is the preceding lower T₁ bound minus the remainder difference; the second is the upper
T₂ bound plus that difference. They also imply the preserved coarse separated estimates m₀−2ε and
k+2ε, and the source cone constants L=m₀−ε,M=m₀−3ε,B=k+2ε with M>ρ>B. All-zero E₁ uses only the
direct vertical bound V and the surviving tests, not division by a; mixed zero ranks use the same
valid inequalities wherever their vectors are nonzero. The preceding independent compact-supremum
and finite-neighborhood arguments complete this quantitative API binding. They do not claim that
these expanded fixed-T formulas or general-bundle guard calculations are literally printed in
HPS.

For the unstable transform first take the raw real vector space Z of all families s_p:E₁,p→E₂,p
with s_p(0)=0 and finite weighted norm ‖s‖*=sup_{p,x≠0} ‖s_p(x)‖/‖x‖, with value0 for the empty
supremum; no continuity in p or x is imposed in this raw carrier. Define the dependent index
I={(p,x):p∈A, x∈E₁,p, x≠0} and the receiving space F_(p,x)=E₂,p. Every F_i has its given real
normed-space structure and is complete. Indeed the exact existing FiniteDimensional.complete
theorem has binders [NontriviallyNormedField ℝ] [CompleteSpace ℝ] [AddCommGroup F_i]
[UniformSpace F_i] [T2Space F_i] [IsUniformAddGroup F_i] [Module ℝ F_i] [ContinuousSMul ℝ F_i]
[FiniteDimensional ℝ F_i]. The original real normed fibre supplies the additive/module
structures, canonical metric/uniformity, Hausdorffness, uniform additive group and continuous
scalar multiplication; the finite-dimensional bundle hypothesis supplies its finite
dimensionality. Thus the theorem applies to every receiving fibre, without a positive-rank
assumption and without changing its norm or uniformity.

For s∈Z set q_s(p,x)=(1/‖x‖) • s_p(x), with the scalar in ℝ. Each indexed x is nonzero, hence
‖x‖>0, and ‖q_s(p,x)‖=‖s_p(x)‖/‖x‖. The dependent lp∞ membership criterion Memℓp q_s ⊤ ↔ BddAbove
{‖q_s(i)‖:i∈I} identifies the finite-weighted families with Y=lp F (⊤:ENNReal). The inverse
assignment is s_p(0)=0 and s_p(x)=‖x‖ • q(p,x) for x≠0. These two assignments are mutually
inverse and linear, by real scalar distributivity in each fixed receiving fibre. The exact lp∞
norm formula gives ‖q_s‖∞=‖s‖* and ‖q_s−q_t‖∞=sup_{p,x≠0} ‖s_p(x)−t_p(x)‖/‖x‖=d*(s,t). The
generic dependent lp normed/completeness instances apply with the canonical Fact(1≤⊤), the real
normed receiving fibres and the just-proved fibre completeness. Hence Y is a Banach space and
this isometric identification makes the raw Z complete. This is dependent lp over the full (p,x)
index, not a constant-fibre sequence space, a jointly continuous section space, or an assumption
that normalized q_s is continuous at0. No subtraction between different fibres occurs: each
coordinate difference lies in E₂,p for its fixed p.

Now impose the unit-slope condition in that complete raw carrier. For fixed p and x,y∈E₁,p the
required inequality is exactly ‖s_p(x)−s_p(y)‖≤‖x−y‖; both values belong to the same E₂,p. For
fixed nonzero x, the lp coordinate bound gives ‖s_p(x)−t_p(x)‖≤‖x‖ ‖q_s−q_t‖∞, so evaluation at
that x is continuous from Y to E₂,p. Evaluation at x=0 is the constant0 map. Consequently
q↦‖s_p(x)−s_p(y)‖ is continuous for every fixed same-fibre pair, including pairs with a zero
input, and the inverse image of the closed scalar interval (−∞,‖x−y‖] is closed. Intersect these
closed constraints over all p,x,y. They define the centered unit-Lipschitz subset Z(1), which is
closed in Y. The existing IsClosed.completeSpace_coe theorem gives CompleteSpace for this subset
with its induced uniformity, and thus for the unit-slope family carrier with d*. This is
precisely the written HPS(5.2) pp.54–55 closure step: weighted convergence gives convergence at
each fixed x, and the same-fibre Lipschitz inequalities pass to those pointwise limits. Page62
explicitly uses sup_p sup_(x≠0), so the chosen index realizes that displayed parameter metric.
Taking y=0 shows ‖s_p(x)‖≤‖x‖ for every member; hence the unit-slope distance is finite and at
most2. The zero family is a member. If I is empty (including empty A or all source fibres zero),
Y and the centered-family carrier are singletons of norm0, and the same statements hold. Zero
receiving fibres cause no difficulty. The identical raw normalization and closed same-fibre
constraints apply with E₁ and E₂ exchanged for the stable carrier, and on restricted fibre
domains containing0.

Finish the joint-continuous subcarrier closure using the original bundle charts and norm, as
follows. Fix p_0∈A and choose genuine real-linear bundle trivializations τ₁,τ₂ of E₁,E₂ on a
common open base neighborhood U of p_0, with fixed finite-dimensional real normed models F₁,F₂.
These are actual local charts for the given total-space and fibre topologies, not a new global
trivialization or a topology defined by the norm comparison below. The model is
finite-dimensional by its chart linear equivalence with the given finite-dimensional fibre at
p_0. Bundle.Trivialization.continuousOn_symm gives joint continuity of (p,u)↦τ_j,p⁻¹u into the
original total bundle on U×F_j. Bundle.Trivialization.continuousLinearEquivAt, using the given
FiberBundle, τ_j.IsLinear ℝ and p∈τ_j.baseSet, identifies each chart with a continuous
real-linear equivalence E_j,p≃L[ℝ]F_j whose inverse is that same τ_j,p⁻¹. Thus homogeneity and
injectivity used below belong to the genuine original chart maps. Forward joint chart continuity
is part of the same bundle trivialization. No smooth structure on A is used.

For either model F_j first suppose F_j is nonzero. FiniteDimensional.proper_real supplies
ProperSpace F_j; isCompact_sphere gives compactness of S_j={u∈F_j:‖u‖=1}. With its induced
topology S_j is a CompactSpace (the sphere subtype support in
Mathlib/Topology/MetricSpace/ProperSpace.lean:47–60), so K=univ⊆S_j is compact. This sphere is
nonempty: choose w≠0, then u=w/‖w‖ has norm1. On the actual base subtype U and sphere subtype S_j
define N_j(p,u)=‖τ_j,p⁻¹u‖_p, using the ORIGINAL fibre norm. Its joint continuity follows by
composing the joint inverse chart with the given continuous total fibre norm (restricted to the
summand; the product maximum norm restricts to its original summand norm). It is positive at
every (p,u), because u≠0 and the fibre linear equivalence is injective. Continuous.div, with
numerator1 and denominator N_j, therefore makes (p,u)↦1/N_j(p,u) jointly continuous, using only
pointwise nonvanishing, not a uniform positive lower bound.

Apply IsCompact.continuous_sSup with γ=U, β=S_j, α=ℝ, K=univ, first to N_j and then to 1/N_j. It
gives continuous real functions B_j(p)=sSup{N_j(p,u):u∈S_j} and A_j(p)=sSup{1/N_j(p,u):u∈S_j}.
For each fixed p the two images are nonempty, since S_j is nonempty, and bounded above by
IsCompact.bddAbove_image applied to their continuous functions on the compact sphere. IsLUB_csSup
therefore supplies the actual upper-bound clauses N_j(p,u)≤B_j(p) and 1/N_j(p,u)≤A_j(p). In
particular B_j(p_0)>0 and A_j(p_0)>0, by choosing one u∈S_j with both values positive. Set
C_j=B_j(p_0)+1>0 and D_j=A_j(p_0)+1>0. Continuity gives an open base neighborhood V_j⊆U of p_0 on
which B_j(p)<C_j and A_j(p)<D_j. Put c_j=1/D_j>0. For u∈S_j and p∈V_j, N_j(p,u)≤C_j and
1/N_j(p,u)≤D_j imply N_j(p,u)≥c_j. For any nonzero v∈F_j normalize u=v/‖v‖; real linearity of
τ_j,p⁻¹ and norm homogeneity yield
c_j‖v‖≤‖τ_j,p⁻¹v‖_p≤C_j‖v‖.
For v=0 this inequality is0≤0≤0. If F_j is zero, every model vector is0 and every original fibre
in the chart is zero by the chart linear equivalence; take c_j=C_j=1 directly. Do not infer
positivity from an empty sphere supremum. Do this for both input and receiving models, and
intersect the two open neighborhoods to obtain V⊆U with both comparisons, using constants C₁ and
c₂ below. The constants have been derived from original norm continuity and the compact sphere
APIs, so no norm-compatibility premise is imported from HPS(3.1).

Let s_n be jointly continuous centered finite-weighted families converging to a raw family s in
d*. Define their chart maps into the ONE fixed receiving model by f_n(p,u)=τ₂,p(s_n,p(τ₁,p⁻¹u))
for p∈V and u∈F₁, and define f by the same formula with s. Each f_n is continuous on V×F₁:
compose the original jointly continuous family evaluation with the genuine joint inverse input
chart and the genuine forward receiving chart. For p∈V, receiving-chart linearity and the lower
comparison give
‖f_n(p,u)−f(p,u)‖≤(1/c₂)‖s_n,p(τ₁,p⁻¹u)−s_p(τ₁,p⁻¹u)‖_p≤(C₁/c₂)‖u‖d*(s_n,s).
The middle weighted inequality holds for nonzero input by the raw lp coordinate estimate, and for
zero input both centered values are0. Thus zero input is included without any continuity
assertion about the normalized q_s. On every set V×B(0,R) with R>0 the difference is bounded by
(C₁R/c₂)d*(s_n,s), uniformly in p and u. Since d*(s_n,s)→0, for every positive tolerance this
bound is eventually smaller than that tolerance (if the coefficient is zero, all differences are
already0). This is TendstoUniformlyOn f_n f (Nat.atTop) on that SAME set, into the fixed normed
model F₂. Every index n gives ContinuousOn f_n there; Nat.atTop is nontrivial, so continuous
indices occur frequently, as required by the exact TendstoUniformlyOn.continuousOn theorem. That
theorem yields ContinuousOn f on V×B(0,R). For any tested chart input u_0 choose R>‖u_0‖; the
open set V×B(0,R) is a neighborhood of (p_0,u_0), hence f is continuous at that point. As p_0 and
u_0 were arbitrary, the original evaluation of s is jointly continuous in all genuine bundle
charts.

To conclude closedness rather than only a limit-sequence assertion, let s be in the metric
closure of the raw joint-continuous subcarrier J⊆Z. Each ball of radius1/(n+1)>0 centered at s
meets J, by the definition of closure; choose s_n in that intersection. Then d*(s_n,s)<1/(n+1)→0,
so the preceding chart proof gives s∈J. Thus closure(J)⊆J and J is closed in the raw complete
metric carrier. Its intersection with the already closed unit-Lipschitz subset is closed too and
contains the zero family. The existing IsClosed.completeSpace_coe theorem gives completeness with
the induced d* metric of the centered unit-slope JOINT-CONTINUOUS subcarrier. The same proof
works for t_p:E₂,p→E₁,p by exchanging the input and receiving charts. For restricted common fibre
domains containing0, use their inherited chart-domain sets and intersect those with the bounded
model balls; the same uniform estimate and ContinuousOn theorem apply in the induced topology, so
no new domain or zero-input restriction is added. This proves exactly the continuous-parameter
closure used on HPS p.62, by direct existing Mathlib compact-sup and uniform-limit APIs. It says
nothing about fibre differentiability, higher jets, moving graph-induced base actions, or
orbit/domain characterizations.

Construct the actual image graph transform, following HPS pp.54–55 with the parameter p inserted
as on p.62, using the original fixed-T constants of step1 and the complete centered jointly
continuous unit-Lipschitz family carrier proved in step2.

3a. First bind the inverse upper-block family to the original topology. Near any p_0 choose
genuine source E₁ charts over U_src and genuine receiving E₁ charts over U_recv near h(p_0);
restrict p to an open V⊆U_src∩h⁻¹(U_recv). In those fixed finite-dimensional real models, put
A₁(p)=τ_recv,h(p) T₁,p τ_src,p⁻¹. For every fixed source model v, p↦A₁(p)v is continuous: the
original inverse source chart, the assumed continuous total bundle map T covering h, and the
receiving chart are jointly continuous. Each A₁(p) is a continuous real-linear map, since its
source is finite-dimensional and the original T₁,p is linear. The exact
finiteDimensional_continuous_clm_apply theorem, with complete scalar ℝ, finite-dimensional real
normed input model and topological parameter subtype V, upgrades all these fixed-v evaluation
continuities to operator-norm continuity of A₁(p). Every A₁(p) is a linear isomorphism because
T₁,p is invertible, and the finite-dimensional source model is complete by
finite_dimensional_complete. The existing operator-inverse ContDiffAt theorem therefore makes
A₁(p)⁻¹ continuous in operator norm. Continuous.clm_apply, composed with the genuine charts,
gives joint continuity of the ORIGINAL map (p,u)↦T₁,p⁻¹u from u∈E₁,h(p) to E₁,p. The norm bound
is the supplied original ‖T₁,p⁻¹‖≤a, applied by le_opNorm. No smoothness of h or new global
trivialization/inverse family is assumed. The original T₂ evaluations and R=G−T are jointly
continuous by the same genuine charts and original total-map continuity; their original norm
estimates remain those of step1.

3b. Given a centered unit-Lipschitz family s, for p and target u∈E₁,h(p) define on the ENTIRE
original complete real normed fibre E₁,p
 Q_(s,p,u)(x)=T₁,p⁻¹[u−R₁,p(x,s_p(x))].
The product maximum norm of (x,s_p(x))−(x',s_p(x')) is≤‖x−x'‖. Hence Q has Lipschitz constant
q=aε<1, and Q(0)=T₁,p⁻¹u has norm≤a‖u‖. The existing finite_dimensional_complete theorem supplies
the original fibre CompleteSpace. Apply g9.mathlib_contracting_exists_fixedPoint with NNReal
contraction constant ⟨q,q≥0⟩ and initial point0; the displacement is finite, so it gives an
actual fixed point X_(s,p)(u), convergence of Q^[n](0), and tail bound
 ‖Q^[n](0)−X_(s,p)(u)‖≤a‖u‖q^n/(1−q)=U‖u‖q^n.
The existing strict-contraction uniqueness theorem proves it is the only horizontal solution. Its
fixed equation is T₁,p X+R₁,p(X,s_p(X))=u; centeredness gives X(0)=0. From that equation,
(1−aε)‖X(u)‖≤a‖u‖, so ‖X(u)‖≤U‖u‖. Comparing the equations for u,u' similarly gives
‖X(u)−X(u')‖≤U‖u−u'‖. Thus H_(s,p)(x)=G₁,p(x,s_p(x)) is onto, with inverse X_(s,p), and injective
by uniqueness of its horizontal solutions; both fibre maps are continuous and the inverse has the
just-proved Lipschitz bound.

3c. Define (F₁s)_(h(p))(u)=G₂,p(X_(s,p)(u),s_p(X_(s,p)(u)))=T₂,p s_p(X)+R₂,p(X,s_p(X)). Since h
is a homeomorphism, each receiving fibre has the unique source p=h⁻¹(p'), so this defines an
actual family. It is centered. Along any unit-Lipschitz graph the original vertical estimate is
k+ε=V, so its slope is≤VU<1, by the preserved choice (k+2ε)U<1. To compare s,t at the same
receiving u, write d=d*(s,t), X_s=X_(s,p)(u), X_t=X_(t,p)(u). Subtract horizontal equations,
split s_p(X_s)−t_p(X_t) at X_t, and use the unit slope and weighted difference at X_t. This gives
 (1−aε)‖X_s−X_t‖≤aε d‖X_t‖,
 hence ‖X_s−X_t‖≤εU²d‖u‖.
Now split the vertical image difference into the change from X_s to X_t along the s graph and the
change from s_p(X_t) to t_p(X_t) at fixed horizontal coordinate. The first has norm≤(k+ε)εU²d‖u‖,
and the second≤(k+ε)d‖X_t‖≤(k+ε)Ud‖u‖. Thus
 d*(F₁s,F₁t)≤[ε(k+ε)U²+(k+ε)U]d=q₁d,
 q₁=a(k+ε)/(1−aε)²<1.
These are the two terms of the actual HPS p.55 image comparison. BOTH vertical terms have k+ε
under the unchanged current k=sup‖T₂,p‖ convention, rather than importing its derivative-block
k-only term or alleging an erratum. For u=0 both image values vanish; for nonzero u divide by its
original norm and take the sup over all source parameters and targets. This verifies preservation
and the actual weighted contraction; fixed-point existence on the jointly continuous carrier
follows in step4 after verifying continuity.

Prove joint continuity of the actual horizontal inverse and image graph transform, and obtain its
invariant graph family by the source HPS p.62 closed-continuous-carrier argument.

4a. For a jointly continuous s use the same original source and receiving charts as step3 and
define the AMBIENT iterates x_0(p,u)=0, x_(n+1)(p,u)=T₁,p⁻¹[u−R₁,p(x_n(p,u),s_p(x_n(p,u)))].
Every finite iterate is jointly continuous as a map into the original source bundle: the original
s evaluation, R₁ and the just-proved joint T₁ inverse are continuous, and the genuine fibre
linear operations are continuous in those charts. No derivative of the graph is assumed. In fixed
receiving model coordinates restrict u_coord to B(0,R), where R>0. The upper original
receiving-norm comparison from step2 gives ‖u‖≤C_recv R uniformly on a smaller original base
neighborhood. The source lower comparison c_src>0 and the step3 fixed-point tail then give
 ‖τ_src,p x_n(p,u)−τ_src,p X_(s,p)(u)‖≤(U C_recv R/c_src)q^n,
 q=aε∈[0,1).
The exact geometric-decay leaf gives q^n→0, including q=0. This uniform bound supplies
TendstoUniformlyOn along Nat.atTop on the SAME local base-neighborhood×receiving-model ball. Its
continuous approximant maps take values in ONE fixed original source model. Every natural index
is continuous, so continuity occurs frequently along the nontrivial filter Nat.atTop; the exact
uniform_limit_continuous_on_set theorem gives ContinuousOn the limit coordinate there. Any tested
receiving coordinate lies in some B(0,R), so these domains cover the chart and yield joint
continuity of the ORIGINAL X_(s,p)(u), including u=0. Their chart neighborhoods need not be
compact or smooth. Substitution into G and s therefore proves joint evaluation continuity of F₁s
in the original bundle.

4b. Step2 already proves completeness of the centered jointly continuous unit-Lipschitz family
carrier with the original weighted metric d*. Its zero family is an actual member. Step3 and4a
give F₁ as a self-map of precisely that carrier and d*(F₁s,F₁t)≤q₁d*(s,t), q₁<1. All distances
are finite (≤2), so in particular the distance from0 to F₁0 is finite. Apply
g9.mathlib_contracting_exists_fixedPoint with constant ⟨q₁,q₁≥0⟩ and the zero family. It supplies
an actual fixed family s*, convergence of F₁^[n](0), and its geometric fixed-point bound.
Strict-contraction uniqueness identifies every fixed family in the carrier with s*. This is a
typed existence application, not merely a fixed-point-property theorem.

4c. The fixed identity is G_p(graph(s*_p))=graph(s*_(h(p))). Indeed for any receiving u the
horizontal solution X_(s*,p)(u) exists and its vertical output is s*_(h(p))(u); conversely every
input graph point maps to that receiving graph by the fixed transform identity. Thus the equality
uses the horizontal map's proven onto property. The whole graph-induced map on ORIGINAL total E₁
is H(p,x)=(h(p),G₁,p(x,s*_p(x))). It is jointly continuous. Its actual inverse is
H⁻¹(p',u)=(h⁻¹(p'),X_(s*,h⁻¹(p'))(u)), jointly continuous by4a and the original homeomorphism h.
Both compositions are the identity by step3's horizontal fixed equation/uniqueness. This inverse
is the canonical graph return needed in steps6–7 and the later orbit arguments, and never an
inverse of ambient G on all E. Zero source/receiving fibres are handled by their unique
horizontal coordinates, using the same equations and genuine charts.

Construct the actual stable preimage graph transform directly, as HPS pp.56–57 does, without
inverting T₂ or G. Use the original step1 constants and the stable jointly continuous centered
unit-Lipschitz carrier supplied by step2. For a family t, p and y∈E₂,p set
 Q_(t,p,y)(x)=T₁,p⁻¹[t_(h(p))(T₂,p y+R₂,p(x,y))−R₁,p(x,y)].
This formula is an ambient map on the original E₁,p and uses the jointly continuous ORIGINAL
inverse family from step3. For each FIXED p,y restrict it to the actual original closed ball
B_(p,y)={x∈E₁,p:‖x‖≤‖y‖}.

5a. Every original source real normed fibre is complete by finite_dimensional_complete and proper
by finite_dimensional_proper_real_g8. Thus isCompact_closedBall gives compactness of this ball in
the ORIGINAL fibre metric; its topology is Hausdorff, so isCompact_isClosed gives its closedness.
IsClosed.completeSpace_coe then gives completeness of the induced ball subtype. The ball
contains0 because ‖y‖≥0, including y=0 when it is the singleton{0}. For x in that ball, the unit
slope/centering of t and the maximum norm give
 ‖Q(x)‖≤a[(k+ε)‖y‖+ε‖y‖]=a(k+2ε)‖y‖≤‖y‖,
by the unchanged step1 smallness choice. Hence Q maps the SAME closed ball into itself. For x,x'
at the same y, both remainder changes are≤ε‖x−x'‖, while t has unit slope, so
‖Q(x)−Q(x')‖≤2aε‖x−x'‖. Put q₀=2aε∈[0,1). Apply g9.mathlib_contracting_exists_fixedPoint to this
complete ball subtype and its zero member, with NNReal constant ⟨q₀,q₀≥0⟩. Initial displacement
at0 is bounded by a(k+2ε)‖y‖: the contribution of R₁,p(0,y) must be included and is not replaced
by k+ε. The theorem gives an actual fixed solution X_(t,p)(y), ‖X‖≤‖y‖, and tail bound
 ‖Q^[n](0)−X‖≤a(k+2ε)‖y‖q₀^n/(1−q₀)=q_J‖y‖q₀^n≤‖y‖q₀^n.
Equivalently, compare iterates directly with the fixed point to obtain the last bound from its
ball membership. The existing uniqueness theorem gives uniqueness of the fixed solution in this
ball. The subtype restriction is made only for fixed p,y; no topology or completeness is asserted
for a joint varying-ball carrier.

5b. Define (F₂t)_p(y)=X_(t,p)(y), centered because y=0 gives X=0. For two values y,y' at the same
p, subtract their fixed equations and split each remainder change into an x-change at fixed y and
a y-change at fixed x. This gives the preserved inequality
 (1−2aε)‖X(y)−X(y')‖≤a(k+2ε)‖y−y'‖,
so the strict transformed slope is q_J=a(k+2ε)/(1−2aε)<1. For t,t' at the SAME p,y split the
receiving graph difference at the receiving value z=T₂,p y+R₂,p(X_(t,p)(y),y). Its norm
is≤(k+ε)‖y‖ because ‖X‖≤‖y‖. The weighted difference there is≤d*(t,t')‖z‖, and the other
receiving/remainder changes contribute2aε‖X_t−X_t'‖. Consequently
 (1−2aε)‖X_t−X_t'‖≤a(k+ε)d*(t,t')‖y‖,
 d*(F₂t,F₂t')≤q₂d*(t,t'),   q₂=a(k+ε)/(1−2aε)<1.
This is the actual HPS p.57 section comparison in the original fixed-T convention. Its k+ε factor
is DISTINCT from the initial-displacement k+2ε and strict slope q_J; neither constant has been
silently exchanged. Zero receiving values give zero graph differences by centering.

5c. To prove joint continuity for a jointly continuous t, use the AMBIENT formula for all finite
iterates x_0(p,y)=0, x_(n+1)(p,y)=Q_(t,p,y)(x_n(p,y)). Each finite iterate is continuous into the
original source bundle by original T₁ inverse continuity from step3, T₂/R continuity, original t
evaluation and genuine fibre operations. For each p,y induction using5a keeps it in its own fixed
ball, but that pointwise property does not define the joint carrier. In genuine stable input
E₂/source output E₁ charts over a common original neighborhood V, take ‖y_coord‖<R with R>0.
Step2 gives ‖y‖≤C_yR and source-coordinate conversion≤1/c_x. The tail in5a therefore gives
 ‖τ₁,p x_n(p,y)−τ₁,p X_(t,p)(y)‖≤(C_yR/c_x)q₀^n
uniformly on V×B(0,R), including y=0. The exact geometric-decay leaf and
uniform_limit_continuous_on_set, with Nat.atTop and continuous approximants at every index into
the ONE fixed E₁ model, prove continuity of the limit coordinate on this SAME domain. V need not
be compact or smooth. Taking R above every tested coordinate norm and using the original inverse
chart gives joint continuity of X_(t,p)(y), hence of F₂t, on the original bundle. No
discontinuous choice of a varying ball chart or graph differentiability is used.

5d. Thus F₂ preserves the OWN step2 complete centered joint-continuous unit-Lipschitz family
carrier, is a q₂ strict contraction and has zero family as a member, with finite initial
distance≤2. The actual g9.mathlib_contracting_exists_fixedPoint theorem supplies a fixed family
t*, its zero-iterate convergence and geometric bound; strict-contraction uniqueness identifies it
among members of this carrier. Its fixed identity gives G_p⁻¹(graph(t*_(h(p))))=graph(t*_p), with
full preimage rather than only a cone-restricted preimage. To verify this, the fixed equation
characterizes the unique solution in ‖x‖≤‖y‖. An additional solution with ‖x‖>‖y‖ would obey
 ‖x‖≤a[k‖y‖+2ε‖x‖],
so (1−2aε)‖x‖≤ak‖y‖, contradicting (1−2aε)>ak and ‖x‖>‖y‖ from the preserved strict smallness in
step1. Therefore every ambient preimage point is already in that ball and on the actual stable
graph. It follows that G_p(graph(t*_p))⊆graph(t*_(h(p))); equality of the image need not hold, as
the actual source explicitly warns. The whole K(p,y)=(h(p),G₂,p(t*_p(y),y)) is jointly continuous
on ORIGINAL total E₂; its vertical fibre bound is Lip(K_p)≤k+ε=V by the unit graph slope and
maximum norm. K may be noninjective or nonsurjective, and no inverse of K, T₂ or ambient G has
been constructed. This is precisely the forward interface needed by the source Hom and jet
arguments in steps6–7.

Construct the jointly continuous invariant first-slope fields by the actual HPS bounded
continuous Hom-unit-section proof (p.25, continuous Hom action pp.34–35 and47, disc restriction
p.36, singular preimage-base mechanism p.58, parameter p.62). This step is a guarded source
application using the source graph/return constructions now installed in steps3–5, relative to
preserved step1 quantitative convention/smallness and step2 original carrier; it supplies their
first-slope fields and joint continuity without assuming any graph derivative or replacing the
remaining higher/domain/orbit arguments.

6a. Keep the ORIGINAL total-space topologies on X₁=TotalSpace(E₁) and X₂=TotalSpace(E₂). They are
not the discrete spatial sets used for jet comparison in step7. Over (p,x)∈X₁ take the actual
pullback Hom fibre L₁,(p,x)=E₁,p→L[ℝ]E₂,p; over (p,y)∈X₂ take L₂,(p,y)=E₂,p→L[ℝ]E₁,p. They carry
their original continuous-linear-map operator norms. Genuine local linear trivializations τ₁,τ₂
of the original bundles give Hom coordinates Q=τ₂,p∘P∘τ₁,p⁻¹ on a fixed local model F₁→L[ℝ]F₂,
and the exchanged coordinates for L₂. The exact continuousAt_hom_bundle criterion identifies
continuity into the genuine Hom total bundle with continuity of the original base projection and
this operator coordinate. These Hom charts and pullbacks use the original topology; they
introduce no global trivialization or smooth-base assumption.

Use the ORIGINAL-norm constants from step2 in these genuine charts: c_j‖u‖≤‖τ_j,p⁻¹u‖_p≤C_j‖u‖,
with c_j,C_j>0 locally in p. For Q corresponding to P, the original operator evaluation bound
gives c₂‖Qu‖≤‖P‖orig C₁‖u‖, and ContinuousLinearMap.opNorm_le_bound then gives
‖Q‖≤(C₁/c₂)‖P‖orig. Conversely for an original input v, put u=τ₁,p v; the upper receiver/lower
input comparisons give ‖Pv‖≤(C₂/c₁)‖Q‖‖v‖, and opNorm_le_bound gives ‖P‖orig≤(C₂/c₁)‖Q‖. Thus
 (c₂/C₁)‖Q‖≤‖P‖orig≤(C₂/c₁)‖Q‖.
Exactly the same inequalities hold for P−P' and Q−Q', since each chart is linear within its fixed
fibre. Zero input or receiving models give the unique zero Hom map and satisfy these estimates
directly. These comparisons establish genuine local norm compatibility, not an extra assumption
imported from a section theorem.

6b. Verify continuity of the ORIGINAL Hom total norm, rather than defining a new norm by
coordinates. For nonzero input model F₁ let S={u∈F₁:‖u‖=1}. The finite-dimensional model is
proper by finite_dimensional_proper_real_g8, and isCompact_sphere makes S compact; its sphere
subtype is CompactSpace with K=univ. S is nonempty by normalizing a nonzero vector. In actual
chart coordinates define
 R(p,Q,u)=‖τ₂,p⁻¹(Q u)‖_p / ‖τ₁,p⁻¹u‖_p
on U×(F₁→L[ℝ]F₂)×S. Continuous.clm_apply, joint original inverse-chart continuity, and the given
original total fibre-norm continuity make the numerator and denominator jointly continuous. The
denominator is positive because u has norm1 and τ₁,p⁻¹ is injective. Continuous.div supplies
joint continuity of R using that pointwise denominator guard. For each (p,Q) its image on the
compact sphere is bounded above by isCompact_bddAbove_image and nonempty by the same nonempty S.
IsLUB_csSup therefore supplies the finite supremum m(p,Q)=sSup{R(p,Q,u):u∈S}, its upper-bound
clause and its least-upper-bound clause. All ratios are nonnegative, and selecting any u gives
m≥0. If v is any nonzero original input, normalize its nonzero model coordinate τ₁,p v to a unit
vector u. Real homogeneity of both inverse charts cancels the common coordinate norm, giving
‖Pv‖/‖v‖=R(p,Q,u)≤m. The zero input gives the same pointwise bound trivially.
ContinuousLinearMap.opNorm_le_bound hence gives ‖P‖orig≤m. Conversely le_opNorm gives
R(p,Q,u)≤‖P‖orig for every u∈S, so the least-upper-bound clause gives m≤‖P‖orig. Thus m equals
the ORIGINAL operator norm. IsCompact.continuous_sSup with γ=U×(F₁→L[ℝ]F₂), β=the compact sphere
subtype, α=ℝ and K=univ proves continuity of m, hence of the original Hom norm in the genuine Hom
chart. If the input model is zero, Hom is the zero space and its norm is continuously0, avoiding
any inference from an empty sphere supremum. A zero receiving model is harmless: all ratios are0
on the nonempty input sphere. The same proof with F₁,F₂ exchanged gives the L₂ norm. Pulling
these charts to the original spatial total spaces through their base projections proves total
Hom-norm continuity on X₁ and X₂, with no compactness of either spatial base required.

6c. Each original Hom fibre is complete in its original operator-norm uniformity. The existing
finite_dimensional_complete leaf supplies completeness of every receiving real normed fibre, with
its original metric and uniformity. ContinuousLinearMap.instCompleteSpace applies with both
scalar fields ℝ, σ=id, the normed domain and complete receiving fibre. Normed domain structure
supplies the additive topological group, continuous real scalar multiplication and
SequentialSpace; the receiving normed structure supplies the uniform additive group and
continuous scalar multiplication. The real identity homomorphism is isometric, and both fields
are nontrivially normed, so the qualified supporting operator-norm compatibility of this exact
leaf identifies its inherited bounded-convergence uniformity with the original operator-norm
uniformity. No complete-domain or positive-rank guard is needed; the finite model spaces used for
operator-inversion continuity are also complete by the same finite-dimensional leaf.

For either side, raw bounded operator sections are exactly dependent lp (fun z∈X_i => L_i,z)
(⊤:ENNReal) over ALL spatial anchors, with UNWEIGHTED norm ‖P‖∞=sup_z‖P(z)‖orig. The generic lp∞
leaf gives completeness, coordinate bounds and the converse supremum bound; Fact(1≤⊤) is
canonical. There are no normalized q-values or punctured-input indices in this operator-section
carrier. The unit-section carrier {P:∀z,‖P(z)‖orig≤1} is closed: each coordinate evaluation is
continuous by the lp coordinate inequality and the norm unit condition is closed, so intersect
these conditions over all z. IsClosed.completeSpace_coe gives completeness of this induced
unit-section subtype. Its zero section is a member. If the spatial base is empty, or all its Hom
fibres are zero, the section carrier is the complete singleton and the same assertions hold. An
individual zero Hom fibre simply contributes its unique zero coordinate without affecting the
other coordinates.

6d. Retain the actual typed rational actions and quantitative algebra already computed:
Construct a slope field before differentiating the fixed graph. Along either graph write D G_p in
blocks (A B; C D), with ||A−T₁,p||,||B||,||C||≤ε and ||D||≤k+ε. Let H_p(x)=G₁,p(x,s_p(x)) and
K_p(y)=G₂,p(t_p(y),y), using the already constructed continuous unit-Lipschitz graphs s,t. Their
horizontal inverse and forward return have Lipschitz constants U and V respectively.

6d.inverse. Bind the upper-block inverse EXISTENCE and quantitative bound in the ORIGINAL fibres
before using either rational formula. Fix p and an anchor, with T₁,p:E₁,p→L[ℝ]E₁,h(p) the given
bounded linear isomorphism. For an unstable unit source slope S:E₁,p→L[ℝ]E₂,p put
 L_u=A+BS=T₁,p+N_u, N_u=A−T₁,p+BS:E₁,p→L[ℝ]E₁,h(p).
For a stable unit RECEIVING slope P:E₂,h(p)→L[ℝ]E₁,h(p) put
 L_s=A−PC=T₁,p+N_s, N_s=A−T₁,p−PC:E₁,p→L[ℝ]E₁,h(p).
The existing block bounds and unit slopes give ‖N_u‖,‖N_s‖≤2ε by the original operator triangle
and continuousLinearMap_opNorm_comp_le inequalities. In either case define the ORIGINAL E₁,p
endomorphism
 Γ_i=−T₁,p⁻¹∘N_i:E₁,p→L[ℝ]E₁,p, θ=2aε.
Since ‖T₁,p⁻¹‖≤a, the same composition inequality gives ‖Γ_i‖≤θ, with0≤θ<1 from step1. Its sign
gives
 H_i=Id−Γ_i=Id+T₁,p⁻¹N_i, L_i=T₁,p∘H_i.
Only T₁,p is inverted here; the source and receiving fibres and their ORIGINAL norms have not
been identified or renormed.

The original real endomorphism ring E₁,p→L[ℝ]E₁,p is complete: finite_dimensional_complete
supplies CompleteSpace of the given real normed fibre, and continuousLinearMap_instCompleteSpace
applies with real scalar fields and identity homomorphism. The normed metric source supplies
SequentialSpace, additive topological group and continuous scalar multiplication; the original
complete receiver supplies its uniform additive/scalar structures. Real id is isometric, so the
leaf's qualified bounded-convergence/operator-norm compatibility gives precisely the ORIGINAL
operator-norm uniformity. Thus this is a complete normed unital ring and has
HasSummableGeomSeries. isUnit_one_sub_of_norm_lt_one at Γ_i proves H_i is an ACTUAL UNIT with a
continuous-linear inverse, hence is onto. Consequently L_i=T₁,p∘H_i is already an actual bounded
linear isomorphism between E₁,p and E₁,h(p). Invertibility precedes every inverse-continuity
application in6e.

Use the existing HUMAN Wells1976 pp.285–287 identity-perturbation proof for the original
quantitative estimate. Γ_i is a bounded linear, hence continuous affine map;
continuousAffineMap_contDiff gives C¹ and contDiff_contDiffOn restricts it to U=the ENTIRE open
original E₁,p. Its pointwise original norm bound gives Lipschitz coefficient≤θ. Apply
analysis.wells_lipschitz_perturbation_smooth_inverse_g5 with X=E₁,p,r=1,Γ=Γ_i,Q=θ. The theorem
first gives its inverse J_i ONLY on the image V=H_i(E₁,p), with Lip(J_i)≤(1−θ)⁻¹. The already
proved UNIT/onto conclusion, not the Wells image theorem alone, gives V=E₁,p. Uniqueness
identifies J_i with the original continuous-linear unit inverse. It is centered since H_i(0)=0;
hence ‖J_i(v)‖≤(1−θ)⁻¹‖v‖. continuousLinearMap_opNorm_le_bound applies with the positive
denominator1−θ, giving ‖H_i⁻¹‖≤(1−θ)⁻¹. Now L_i⁻¹=H_i⁻¹∘T₁,p⁻¹ has its actual receiving-to-source
type E₁,h(p)→L[ℝ]E₁,p. continuousLinearMap_opNorm_comp_le gives
 ‖L_i⁻¹‖≤a/(1−2aε)=b.
This retains the existing b and smallness, including ε=0/θ=0 with denominator1, without dividing
byθ or by a.

If the individual E₁,p fibre is zero, its T₁,p isomorphism forces E₁,h(p) zero too; each L_i is
the unique isomorphism of singleton spaces, and its inverse norm0≤b directly. This does not make
other fibres or their carriers singletons. If ALL E₁ fibres are zero, a=0 and the direct inverse
conclusion uses b=0/1=0, never1/a. A zero E₂ fibre does NOT bypass this upper inverse proof when
E₁,p is nonzero: the vanishing B/C/slope factors merely simplify the same N_i. No h-invariance of
the zero-E₂ stratum or inverse of T₂/K is assumed.

Resume the typed rational actions of6d. For a unit slope S the unstable slope transform is
Φ₁(S)=(C+DS)(A+BS)⁻¹, indexed at the receiving point H_p(x); for a receiving unit slope P the
stable transform is Φ₂(P)=(A−PC)⁻¹(PD−B), indexed at y and reading the slope at K_p(y). Both
ORIGINAL inverses exist and have norm at most b by the typed UNIT/Wells proof in6d.inverse. The
transformed slopes have norm≤b(k+2ε)<1. Subtracting the rational identities for two input slopes
gives the same contraction bound q_J=b(k+2ε): in the unstable case multiply the output difference
by A+BS and use D−output·B; in the stable case multiply by A−PC and use D+C·output.
Here the unstable blocks have types A:E₁,p→L E₁,h(p), B:E₂,p→L E₁,h(p), C:E₁,p→L E₂,h(p),
D:E₂,p→L E₂,h(p). A unit source P:E₁,p→L E₂,p gives Φ₁(P):E₁,h(p)→L E₂,h(p). A unit receiving
P:E₂,h(p)→L E₁,h(p) gives Φ₂(P):E₂,p→L E₁,p. In both cases the inverse norm≤b established
in6d.inverse and output norm≤q_J=b(k+2ε)<1 imply preservation of the original closed unit disc.
For two unstable unit slopes S,S', the identity obtained by multiplying the output difference by
A+BS has numerator (D−Φ₁(S')B)(S−S'); its norm is at most k+2ε times ‖S−S'‖, because the other
output norm≤1. Multiplication by the inverse gives q_J‖S−S'‖. For two stable unit slopes P,P',
multiply by A−PC: the numerator is (P−P')(D+CΦ₂(P')), again at most (k+2ε)‖P−P'‖; inversion gives
the same q_J. Thus these are uniform original-operator-norm contractions with no new rate or
smallness hypothesis. Images of zero have norm≤bε≤q_J and therefore a common finite bound.

6e. The whole unstable base map H(p,x)=(h(p),G₁,p(x,s_p(x))) and its whole inverse are genuine
continuous inverse maps on ORIGINAL X₁, by steps3–4. The stable base map
K(p,y)=(h(p),G₂,p(t_p(y),y)) is a continuous forward map on ORIGINAL X₂ by step5 and requires no
inverse. To check continuity of the rational actions, use genuine original source charts near p
and receiving charts near h(p), and restrict the anchor neighborhood to the intersection with the
inverse image under H or K of the receiving chart neighborhood. These are ordinary open
restrictions of the existing base, not new domains or global trivializations. The assumed jointly
continuous G fibre derivatives, already continuous original graph evaluations, and the continuous
returns make A,B,C,D jointly continuous operator-coordinate families there. Continuous.clm_comp
supplies their compositions with the varying unit slope. The existing operator-inverse ContDiffAt
theorem, with the now-checked complete fixed finite models and invertible A+BP or A−PC, supplies
continuity of their inverse families. Addition, composition and the genuine Hom continuity
criterion therefore make Φ₁ over H and the evaluation form of Φ₂ continuous on the original Hom
unit-disc total spaces. This argument uses only derivatives of G, which are hypotheses; it
assumes no derivative of s or t.

6f. Continuous bounded operator sections form a closed subset of the raw complete lp carrier. For
a supremum-convergent sequence P_n→P and any genuine local Hom chart, the lower comparison from6a
is c_Hom=c₂/C₁>0 (with indices exchanged on the stable side). On the original chart-domain
subtype the operator coordinates satisfy ‖Q_n(z)−Q(z)‖≤c_Hom⁻¹‖P_n−P‖∞, uniformly in ALL spatial
anchors in that domain. The finite model Hom space is a fixed real normed space. Its continuous
coordinate maps Q_n therefore converge uniformly to Q along Nat.atTop; every index is continuous,
hence continuity occurs frequently in the nontrivial filter Nat.atTop. The exact
uniform_limit_continuous_on_set leaf proves continuity of Q, and continuousAt_hom_bundle gives
continuity of P in the original Hom total-space topology. A metric-closure sequence chosen within
radii1/(n+1) proves that the continuous-section subset is closed. Its intersection with the
original unit-section carrier is therefore closed and complete by IsClosed.completeSpace_coe and
contains the zero continuous section. No compactness of the chart domain or spatial base is used.

6g. For the unstable action put (T_uP)(H(p,x))=Φ₁,(p,x)(P(p,x)). H has the genuine continuous
inverse from steps3–4; disc preservation and6d give a sup q_J contraction on unit sections. After
all the original Hom fibre-completeness, total-norm-continuity and local chart-compatibility
guards above have been checked, the CLOSED UNIT-DISC version of
hps.theorem_3_1_bounded_continuous_sections_g4 applies over ORIGINAL X₁ with base homeomorphism H
and disc map Φ₁. It gives a unique invariant bounded continuous unit section P₁. The
noncompact-base clause of the actual HPS p.25 proof is legitimate because zero images are
bounded≤q_J; no compactness of X₁ is asserted. This invokes the helper only for the unstable
homeomorphism branch, not for K.

For the stable action instead put (T_sP)(p,y)=Φ₂,(p,y)(P(K(p,y))). It is defined at every anchor
because K is a point-valued map, even if K is noninjective or nonsurjective. It preserves the
original unit carrier by6d, and d∞(T_sP,T_sP')≤q_J d∞(P,P') follows pointwise by evaluating at
K(p,y) and taking the supremum. It preserves continuous sections because K and the rational Hom
action are continuous by6e. This is the actual HPS p.58 disjoint inverse-relation mechanism:
distinct target anchors have disjoint inverse sets K⁻¹({z}); these sets may be empty or multiple,
while the reverse map is the single-valued K. Inline the HPS p.25 bounded-section fixed-point
proof for this point-forward section action: apply g9.mathlib_contracting_exists_fixedPoint to
the complete metric unit-section carrier, contraction constant ⟨q_J,q_J≥0⟩<1, and the zero
section. All metric distances are finite; in particular d∞(0,T_s0)≤q_J. The theorem gives a fixed
P₂, T_s^n0→P₂ and the explicit bound d∞(T_s^n0,P₂)≤d∞(0,T_s0)q_J^n/(1−q_J). Every finite iterate
is continuous, since0 is continuous and T_s preserves continuous sections. By the
closed-continuous-carrier argument6f the limit P₂ is continuous in the original topology. The
existing contraction uniqueness leaf gives uniqueness among all bounded unit sections. No
application of the homeomorphism helper to K, no inverse or surjectivity of K or T₂, and no extra
stable-base theorem is used. The unstable helper's printed proof uses the same zero-iterate
convergence and closed-continuous-carrier reasoning; the fixed identities of these two sections
are exactly the rational identities used in step7.

Thus the original P₁,P₂ are genuinely jointly continuous bounded invariant unit-slope fields on
the entire original spatial fibre unions, using the installed source graph/return interfaces of
steps3–5 relative to preserved steps1–2. Step7's already installed restricted own-jet/affine-jet
comparison identifies them with actual fibre derivatives. No arbitrary-topological smooth-base
assumption, approximating-graph derivative convergence, higher jet, compact-tube retention,
finite-return or orbit/source conclusion is imported in this first-Hom-section proof.

Identify the actual graph derivatives by the written HPS closed-differentiable-jet versus own-jet
comparison (Theorem3.3 pp.27–29, invariant-own-jet argument pp.33–34, image action pp.55–56, and
local preimage/set-valued-base action pp.57–58). This step uses the already constructed bounded
invariant slope fields from step6; it does not construct a new field or certify that step's
joint-continuity/source boundary.

7a. Use the full spatial anchor sets X₁=⊔_(p∈A)E₁,p and X₂=⊔_(p∈A)E₂,p, and give ALL their points
(p,x) or (p,y), not just p or an integer orbit index, the discrete topology for jet bookkeeping,
as HPS p.33 prescribes. At each anchor translate both the input and graph value to0 in the
original normed fibres. They are real Banach spaces by the existing finite-dimensional
completeness leaf. HPS Theorem3.3 then gives bounded Lipschitz jets modulo little-o at that
anchor, with closed differentiable subspace J_diff=J_aff isometric to the bounded real-linear
maps between those original fibres. For the unstable own jet take the actual representative
v↦s_p(x+v)−s_p(x); for the stable own jet take v↦t_p(y+v)−t_p(y). Their jet norms are≤1 because
the actual graphs are unit-Lipschitz. The affine jets at these anchors are represented by the
existing slopes P₁,p(x) or P₂,p(y) from step6 and have norms≤1. Only these own jets and affine
unit jets will be compared. Every affine unit jet has a genuine two-point unit-Lipschitz affine
representative through the fixed anchor. No assertion that every radial unit jet admits such a
representative, no topology on a joint family of germ quotients, and no existence theorem for a
new D_diff fixed field is needed.

7b. The whole unstable graph-induced map is H(p,x)=(h(p),H_p(x)), where H_p(x)=G₁,p(x,s_p(x)). By
steps3–4 its inverse is the actual whole-fibre map H⁻¹(p',u)=(h⁻¹(p'),X_(s,h⁻¹(p'))(u)); it maps
between the original fibres. Fix an anchor (p,x) and its graph value s_p(x). For a real-linear
P:E₁,p→E₂,p with ‖P‖≤1 take the affine local graph σ_P(v)=s_p(x)+P(v−x). At (x,s_p(x)) write the
derivative blocks of G_p as A,B,C,D, as in step6. The horizontal derivative of v↦G₁,p(v,σ_P(v))
is A+BP, invertible with inverse norm≤b. The local C¹ implicit-function theorem produces the
horizontal inverse near H_p(x). Its image graph G₂,p(v,σ_P(v)) in this inverse parameter is C¹,
with derivative (C+DP)(A+BP)⁻¹=Φ₁(P). By the bound already computed in step6 this derivative has
norm≤q_J<1 at the anchor. Continuity of the derivative and a smaller convex fibre ball give a
local two-point Lipschitz constant≤1 by the derivative/segment norm estimate. Thus the action on
each affine unit jet has an admissible differentiable unit-Lipschitz representative. The original
graph is another admissible representative through the same anchor, and graph invariance makes
its local image precisely the receiving own graph at H(p,x).

For two admissible local representatives w,w' sharing the input anchor/value, let d be their
input jet distance and let X_w,X_w' be their local horizontal inverses sharing the output anchor.
The same two-term decomposition printed on HPS p.55 applies locally: compare inverses, then
compare vertical values at a fixed horizontal coordinate. For every η>d their normalized input
difference is≤η on a sufficiently small punctured input neighborhood. The horizontal inverse
Lipschitz bound U=a/(1−aε) yields a normalized inverse difference at most εU²η at the output
anchor. The vertical map along a unit-Lipschitz graph has bound k+ε, and its fixed-horizontal
change between graph representatives also has bound k+ε in the current fixed-T convention. Hence
the two normalized vertical differences are bounded by ε(k+ε)U²η and (k+ε)Uη. Taking the limsup
and then η↓d gives the image jet comparison
 d_out≤[ε(k+ε)U²+(k+ε)U]d=q₁d,
 q₁=a(k+ε)/(1−aε)²<1.
Both terms use k+ε; the printed source's smaller k-only term belongs to its different
lower-derivative-block convention and is not substituted for the present k=sup‖T₂,p‖. The same
estimate with d=0 proves independence of equivalent admissible representatives. This comparison
is required only for the actual own jet and affine jet, and does not assume an action on the
whole radial jet disc.

7c. For the stable graph use the whole forward anchor map K(p,y)=(h(p),K_p(y)), where
K_p(y)=G₂,p(t_p(y),y). Put y₁=K_p(y). Graph invariance from step5 gives
G_p(t_p(y),y)=(t_(h(p))(y₁),y₁), so this is the actual receiving anchor. For a receiving
real-linear P:E₂,h(p)→E₁,h(p) with ‖P‖≤1, take τ_P(w)=t_(h(p))(y₁)+P(w−y₁). This representative
satisfies the local cone condition of the last paragraph of HPS p.57: if y₁≠0, the strict graph
slope from step5, q_J=a(k+2ε)/(1−2aε)<1, gives ‖t_(h(p))(y₁)‖<‖y₁‖. Thus the receiving anchor is
in the interior of S₂={ (u,w):‖u‖≤‖w‖ }, and continuity lets one shrink the affine graph domain
to stay in S₂. If y₁=0, centeredness gives t_(h(p))(0)=0 and τ_P(w)=Pw stays in S₂ directly. This
covers a nonzero source y with K_p(y)=0. The receiving actual graph itself is unit-Lipschitz and
lies in S₂.

Solve G₁,p(u,v)=τ_P(G₂,p(u,v)) locally through the ACTUAL output anchor (t_p(y),y). Its partial
derivative in u is A−PC, invertible with inverse norm≤b, so the C¹ implicit-function theorem
gives a unique local preimage graph. Its derivative is (A−PC)⁻¹(PD−B)=Φ₂(P), precisely step6's
rational action, with norm≤q_J<1. As in7b, a smaller convex domain gives a differentiable local
two-point unit-Lipschitz representative. For the own receiving representative, the original
full-preimage graph equality of step5 and uniqueness of the local horizontal solution identify
its output with the actual graph near y. No prior differentiability of that graph is used: its
horizontal equation is already the Lipschitz contraction from step5.

HPS pp.57–58 compares such local preimage representatives sharing the receiving value, whose
output values at y therefore coincide. The horizontal comparison has denominator1−2aε from the
same step5 contraction, and gives the factor a/(1−2aε) multiplying the difference of the
receiving representatives at the fixed actual receiving displacement K_p(y+v)−K_p(y). That
displacement has norm≤(k+ε)‖v‖, because the original graph has unit slope. For any η above their
receiving jet distance, restrict the neighborhood so that the normalized receiving difference
is≤η; if the displacement is0 the difference is exactly0. Passing to the limsup gives
 d_out(p,y)≤q₂ d_in(h(p),K_p(y)),
 q₂=a(k+ε)/(1−2aε)<1.
It also gives well-definedness on equivalent admissible representatives. The source set-valued
base is the inverse relation K⁻¹({z}) on X₂: distinct receiving z have disjoint inverse sets,
with empty or multiple-point inverse sets allowed. Its point-valued reverse map is the actual K.
Our comparison simply reads the receiving jet at K(p,y). K need not be injective, surjective, or
differentiable here; neither K, T₂ nor ambient G is inverted.

7d. Denote the unstable own jets by j₁(p,x) and affine jets of P₁ by ℓ₁(p,x), and the stable ones
by j₂(p,y),ℓ₂(p,y). The original graph identities make the own jets invariant under the preceding
restricted image/preimage actions. The fixed rational identities of the EXISTING step6 fields
make the affine jets invariant under exactly those same actions; no new closed-jet fixed point is
assumed. Their distances D₁=‖j₁−ℓ₁‖ and D₂=‖j₂−ℓ₂‖ are≤2 at every spatial anchor. The local
comparisons yield
 D₁(H(p,x))≤q₁D₁(p,x),   D₂(p,y)≤q₂D₂(K(p,y)).
Iterate the true whole H⁻¹ for the first inequality: at any target anchor D₁≤2q₁^n for every n.
Iterate the point-valued whole K forward for the second: D₂≤2q₂^n for every n. The powers tend
to0 by the existing geometric-decay leaf, hence both distances are0. HPS3.3 and the written
own-jet uniqueness argument pp.33–34 say precisely that the original centered graph
representative agrees modulo little-o with its affine slope representative. Thus
 s_p(x+v)−s_p(x)−P₁,p(x)v=o(‖v‖),
 t_p(y+v)−t_p(y)−P₂,p(y)v=o(‖v‖).
The exact hasFDerivAt_iff_isLittleO_nhds_zero criterion proves Frechet differentiability at every
original fibre point with derivative equal to the corresponding P. Zero input or receiving fibres
have only the zero jet/operator, so their identification is immediate. Step6 supplies joint
continuity of these original invariant Hom slope fields using the source graph/return inputs now
installed in steps3–5, relative to preserved step1 quantitative convention/smallness and step2
original carrier. The derivative equality therefore gives joint first-derivative continuity and
fibrewise C¹ regularity. The independent quantitative guards are proved in Step1; higher
regularity and the orbit characterization are proved in Steps9–14. The scalar E/e Taylor-defect
alternative has been replaced by the actual HPS restricted closed-differentiable-affine versus
own-jet proof, not merely cited or relabeled.

At the zero section the derivative blocks are (T₁,p 0; 0 T₂,p). For the unstable derivative S_p
at zero the fixed jet relation is S_{h(p)}=T₂,p S_p T₁,p⁻¹; for the stable derivative R_p it is
R_p=T₁,p⁻¹ R_{h(p)}T₂,p. Both families have norm at most 1. Iterating either identity along the
appropriate h-orbit bounds the norm at every p by (ak)^n for every n, hence it is zero. This
proves tangency to the respective summand, including for noninvertible T₂, and is the zero-jet
calculation of Corollary (5.3).

Use the local quantitative preparation actually written in HPS pp32–33 before its own-jet
identification, with the original strong graph returns already constructed in Steps3–7. In the
unstable branch set ℛ(p,z)=(h⁻¹(p),H_{h⁻¹(p)}⁻¹(z)); in the stable branch set
ℛ(p,z)=(h(p),K_p(z)). Their original fibre Lipschitz constants are c=U and c=V respectively, and
Step1 gives c<1 in the applicable strong branch. Both returns fix zero. Thus, writing
Dδ(p)={z:||z||_p<δ}, one has ||ℛ_fibre(p,z)||≤c||z||_p and ℛ(Dδ/2(p))⊆Dδ/2(h⁻¹p) or Dδ/2(hp). The
same original radius, rather than a coordinate radius changed at each iterate, gives
||ℛ_fibre^n(p,z)||≤c^n||z||_p for every n. Stable K is only this forward point-valued return; no
inverse or base-homeomorphism theorem is applied to K.

At a derivative stage use only graph jets already proved jointly continuous on the open original
discs Dδ. Choose frames at p₀ and its return base h⁻¹p₀ or hp₀, and intersect the source
neighborhood with h of, or h⁻¹ of, the chosen receiving neighborhood. The original graph values
satisfy ||w_p(z)||≤||z||_p; hence G is evaluated on its original graph over these discs, while ℛ
lands in the original receiving discs just specified. When w is fibre-C^j, the unstable
horizontal inverse is fibre-C^j by the implicit-function/inverse theorem and the already
invertible A+B Dw; its known inverse derivatives are continuous finite compositions of known jets
and that inverse. The stable K=G₂∘(t,id) is fibre-C^j directly. These are local original inverses
from Steps3/6, not a new inverse for G or T₂. No derivative of p or h is taken.

For the uniform bounds use a compact MODEL disc, not a compact closed subset of the base. In a
frame at p₀ let K be the p₀-original closed input disc of radius 3δ/4, viewed in the fixed
finite-dimensional model. It is compact by finite-dimensional properness and the closed-ball
theorem. Continuity of the original norm on the compact p₀-unit sphere gives an OPEN frame
neighborhood on which 7/8||v||_{p₀}≤||v||_p≤9/8||v||_{p₀}. Consequently every p-original closed
disc of radius δ/2 is contained in K, and all of K stays in the p-original open disc Dδ, since
(9/8)(3δ/4)<δ. The zero model has K={0} and needs no unit sphere. Apply the same comparison in
the receiving and iterated Hom frames when they occur; all comparisons concern the original
norms, so they do not change c or the inward-disc estimate.

Let J be any one of the finitely many KNOWN jet/coefficient norm functions needed at this stage
in those paired frames. It is jointly continuous on the open original source/receiving domains.
On {p₀}×K it has a finite bound M≥0 by the compact continuous-bound input. The open inequality
||J(p,v)||<M+1 holds at every (p₀,v), v∈K. The exact compact_eventually_forall input therefore
gives an OPEN base neighborhood on which it holds for ALL v∈K simultaneously. This is the tube
construction written in Munkres Theorem26.7 Step1, pp167–168, and restated as Lemma26.8 p168:
cover the compact model slice by finitely many product neighborhoods and intersect only their
open first factors. The same compact-slice argument gives uniform coordinate continuity at a
fixed p₀ when needed. Neither a Hausdorff parameter base, a closed-core refinement, compactness
of an entire bundle disc nor a global bound on higher derivatives is assumed.

Intersect these neighborhoods for the finite list of known derivatives, norm comparisons and
original open-domain guards. They form an OPEN cover of A. Index their finite unions by finite
sets of centers; this is a nonempty directed family of open sets, including the empty finite set.
The existing isCompact_elim_directed_cover input selects a finite union covering A. Taking the
maximum, or a larger finite sum, of its nonnegative local bounds produces one original-norm bound
valid on all retained discs. For A empty the families are empty and all bounds/sections are
direct. At the next derivative order apply this procedure again on a smaller inner disc within
the domain where the previous order was proved. There are finitely many orders up to r, so
finitely many shrinkings leave one positive common inner radius. The return bound c<1 preserves
every chosen radius independently of the frames. This prepares local regularity only; extending
it to every bounded original disc is the separate Step12 obligation.

On these domains the original slope equation is P(q)=Φ(q,P(ℛq)), with ||D_ZΦ||≤q_J from Step6.
For coefficient bounds with an independent slope argument Z, use the strict ||P||≤q_J<1: choose
two radii strictly between q_J and 1 in the p₀-original Hom norm and shrink the OPEN paired-frame
neighborhood by the same compact-sphere comparison. A fixed compact model Hom disc then contains
every actual slope value and every segment between two such values while remaining inside
||Z||<1. The original upper-block inverses are therefore the same inverses from Step6 on an open
neighborhood of all tested arguments; their derivatives are continuous compositions using the
inverse derivative rule. Spatial compact model discs and these slope discs are a finite product
of compact finite-dimensional sets, so the preceding tube bound applies to the known Φ and ℛ jets
and forcing. In particular the finite bounds needed in Steps10/11 follow from supplied G
derivatives and already known graph derivatives, never from the derivative currently being
established.

This is the quantitative application of the written HPS compact-disc, forcing/cone and local
Finsler preparation pp32–33, followed by the original continuous Hom induction p35, with the
point-valued stable convention p58 and parameter insertion p62. It does not invoke Theorem3.5 as
a theorem over an arbitrary nonsmooth parameter base. The explicit δ/δ2/frame and
finite-open-cover bindings are applications of that mechanism and the named topological APIs;
they are not claimed to be formulas printed in HPS.

For r≥2 apply the bounded-forcing/invariant Lipschitz preparation of HPS pp32–33 to the already
fixed first-slope field, before identifying its differentiable own jet. Supplied G is fibre-C²
and w is already fibre-C¹ with joint first jets, so the original rational Φ and return ℛ are
fibre-C¹ with joint known derivatives on the open domains of Step9. The chain and inverse rules
use only D²G, Dw and the original upper inverse; they do not differentiate P. Step9's
compact-model/open-cover bounds give a finite L≥0 for D_zΦ(q,Z) on the inner spatial discs and on
the compact admissible slope discs. The two-point segment derivative estimate applies in one
original convex spatial fibre disc, with Z held fixed in its correctly typed receiving Hom fibre.
It gives ||Φ(q,Z)−Φ(q′,Z)||≤L||z−z′||. The original slope contraction still gives the independent
Z comparison with coefficient q_J. Also ||D_zℛ||≤c by the derivative bound for a Lipschitz map,
in the original norms. The forcing F_q=D_zΦ(q,P(ℛq)) is thus bounded and jointly continuous by
known jets and the existing continuous P, without DP.

Compare the two fixed equations, first keeping Z=P(ℛq′) fixed and then using the slope
contraction. Since q,q′ lie in one source fibre, their returns lie in the same receiving fibre,
and all slope values/segments belong to Step9's admissible disc. One obtains
||P(q)−P(q′)||≤q_J||P(ℛq)−P(ℛq′)||+L||z−z′||. After N returns the residual is at most 2q_J^N
because ||P||≤1, and the error sum is at most L||z−z′||∑_{i<N}(q_Jc)^i. The original inward-disc
estimate permits every iterate. Let N→∞ to obtain the uniform fibre Lipschitz constant
L_P=L/(1−q_Jc). This is the source bounded-forcing/contraction Lipschitz algorithm specialized to
the actual point-evaluation return; no differentiability of P is assumed. If either factor is
zero, the same estimate applies directly without its reciprocal.

Now use the already reconstructed written fixed-own-jet/closed-differentiable-jet mechanism of
HPS Theorem3.3 pp27–29 and pp33–35, with the singular point-return convention p58 and parameter
convention p62, on these PROVED inward domains and known forcing/Lipschitz bounds. Work with the
fixed graph w and P of Steps6–7. No graph approximant, parameter derivative, extra derivative of
G, replacement graph, or source6.7 immersion is introduced.

10a. At each original spatial anchor q=(p,z) translate the fibre input and the Hom value P(q) to
zero. Let V_q be the original spatial input fibre E₁,p or E₂,p and H_q the original first-slope
Hom fibre from Step6. The original real normed fibres are complete by
finite_dimensional_complete; ContinuousLinearMap.instCompleteSpace gives completeness of H_q in
its original operator norm and then of L(V_q,H_q), with the same real-id/isometric
operator-uniformity guards checked in6c. HPS3.3 gives the Banach space J_b(V_q,0;H_q,0) of
bounded Lipschitz jets modulo little-o and its CLOSED subspace J_diff=J_aff, isometric to
L(V_q,H_q). Discretize ALL spatial anchors only for this jet bookkeeping, as on p33; retain the
original total-space topology for the continuous Hom field below. The product of bounded jet
sections has the dependent lp∞ supremum norm. Completeness follows from the generic lp∞ leaf and
the fibre Banach spaces of3.3; its affine-section subspace is closed because every coordinate
J_diff is closed. This is a product of the original fibre norms, not a common global
trivialization. Empty anchor sets have the unique zero section. Zero input or Hom models have
only their zero jet/operator and need no sphere or reciprocal argument.

10b. Define the action on DIFFERENTIABLE affine jets through the fixed P anchors, rather than on
the entire radial unit-jet disc. An input affine jet at ℛq is represented by u↦P(ℛq)+Su, with
S:V_(ℛq)→L[ℝ]H_(ℛq). Step6 gives the strict uniform bound ||P(ℛq)||≤q_J<1. For every bounded S
one may therefore restrict this representative to an open fibre neighborhood of0 with
||P(ℛq)+Su||<1: choose its radius so that ||S|| times that radius is less than (1−q_J)/2. When
S=0 any sufficiently small original receiving neighborhood works; no division by ||S|| is needed.
Intersect with the actual receiving chart/domain from Step9. Since ℛ is continuous and sends q to
ℛq, shrink the source neighborhood so its image lies there. These are local germ restrictions
inside the Step9 domains, not a single radius asserted for all bounded affine representatives S.
The actual P representative lies in the same unit-slope domain.

The source action representative near q is
 v↦Φ(q+v,P(ℛq)+S[ℛ(q+v)−ℛq]).
Its value at0 is P(q), by the EXISTING fixed identity. Since Φ and ℛ are already fibre-C¹ on
these domains, the ordinary chain-rule leaf gives its derivative
 A_q(S)=F_q+B_q S C_q,
 F_q=D_zΦ(q,P(ℛq)), B_q=D_ZΦ(q,P(ℛq)), C_q=D_zℛ(q),
with the original receiving/source types; no derivative of P is taken. The original slope
contraction supplies ||B_q||≤q_J, and the known return derivative satisfies ||C_q||≤c. Thus
||A_q(S)−A_q(S′)||≤λ||S−S′||, λ=q_Jc<1. F is bounded by the retained forcing bound B₀≥0 and
jointly continuous by the retained known fibre jets. The output differentiable germ has a local
two-point Lipschitz bound after shrinking its convex domain by the derivative/segment estimate;
it represents the affine jet A_q(S), exactly as HPS pp33–34 preserves J_diff. We need neither
preservation of a radial unit ball for derivatives S nor an action on every nondifferentiable
radial jet.

10c. Inline the bounded-section contraction proof of HPS p25, as already implemented in6g/7, on
this CLOSED affine carrier. Put L_P=L/(1−λ) for the retained Lipschitz bound and N=L_P+B₀/(1−λ);
the denominator is positive. Coordinate constraints ||S(q)||≤N are closed in dependent lp∞, so
their intersection with the complete affine carrier is complete by IsClosed.completeSpace_coe and
contains0. The exact point-evaluation section action is (𝒜S)(q)=A_q(S(ℛq)). It preserves that
ball, since ||𝒜S(q)||≤B₀+λN≤N, and contracts supremum distances by λ. Apply
g9.mathlib_contracting_exists_fixedPoint on this complete finite-metric carrier with initial0;
the existing fixed-point/uniqueness inputs give a bounded fixed affine section S and geometric
convergence of its Picard iterates. This is the written closed-differentiable-jet fixed-section
algorithm specialized to the displayed affine action. In the unstable branch ℛ is the actual
horizontal inverse return. In the stable branch it is the actual forward K, possibly noninjective
or nonsurjective. HPS p58's disjoint inverse relation has this point-valued reverse map:
evaluating S at Kq is all that the section action requires. The homeomorphism-exporting3.1
provider is NOT invoked for K. No inverse of K,T₂ or G, or restriction to nonzero return values,
is used.

10d. The known Lipschitz field P has its own jet j(q)=J_q(P), of norm≤L_P. Its fixed identity
makes j invariant under the SAME local representative action. The affine jet
ℓ(q)=J_q(v↦P(q)+S(q)v) is invariant because S=𝒜S. For completeness, the original unit-domain
slope estimate gives the source jet comparison without differentiating P: if η exceeds the input
distance between j(ℛq) and ℓ(ℛq), restrict the receiving neighborhood so the normalized
representative difference is≤η. Their values agree at the receiving anchor. Both slope
representatives stay in the unit domain by10b. Evaluating them at ℛ(q+v), applying the q_J
Lipschitz bound of Φ in its slope argument and ||ℛ(q+v)−ℛq||≤c||v||, then taking the limsup gives
 d(q)≤λ d(ℛq), where d(q)=||j(q)−ℓ(q)||.
If the receiving displacement is0 their difference is exactly0. This is the pairwise
own/affine-jet comparison of HPS pp33–34 and58, not the old scalar Taylor-defect proof. Initially
d(q)≤L_P+N. Iteration on the retained inward domains gives d(q)≤(L_P+N)λⁿ for every n; the
geometric-power leaf gives d(q)=0. HPS3.3 therefore identifies the actual P germ with its
differentiable affine germ. The exact hasFDerivAt_iff_isLittleO_nhds_zero leaf yields DP(q)=S(q).
When c=0 or q_J=0, λ=0 and the first comparison already gives d=0; neither factor is inverted.
Zero models give the same conclusion directly.

10e. Obtain joint continuity in the ORIGINAL topology by the continuous Hom-section
identification of HPS p35, not from continuity on the discretized jet base. S lives in the
iterated genuine Hom bundle L(V_q,H_q). Original charts, operator-norm comparison and total-norm
continuity are the same iterated finite-dimensional Hom construction verified in6a–6c, using
continuousAt_hom_bundle and continuous clm evaluation/composition. F,B,C and ℛ are jointly
continuous on the source/receiving chart domains prepared in Step9, so every finite Picard
iterate from0 is continuous there. The supremum geometric tail gives uniform convergence of their
coordinates on a common genuine chart neighborhood, using the original chart norm comparisons as
in6f; the exact uniform_limit_continuous_on_set API therefore makes S jointly continuous. This
remains valid for a nonsmooth topological parameter base and the stable point-valued K.
Consequently the original w is fibre-C² with joint second-derivative continuity ON THE RETAINED
inward domains. The own/affine-jet argument is unchanged; its Step9/initial Step10 preparation is
now supplied above and the finite-order bootstrap is supplied in Step11. Step12 proves the
finite-return extension and fixed-disc C^r-sup continuity. The completed local5.4 supplier is an
autonomous Banach theorem and is not silently instantiated on G_p:E_p→E_h(p).

Carry out the finite tangent-section induction written in HPS p35 on the original fixed slope
equation. For m=1,…,r−2 suppose the preceding step has proved w fibre-C^(m+1), P=Dw fibre-C^m and
their known jets jointly continuous on a common OPEN original inner disc. Apply Step9's
compact-model/tube and finite OPEN cover argument again inside that known domain, retaining a
smaller inward disc; this bounds precisely those existing jets. Put Q_m=D^mP. The ordinary
iterated chain/product rules applied m times to P(q)=Φ(q,P(ℛq)) give
Q_m(q)=A_m(q)Q_m(ℛq)+F_m(q).
The only term containing D^mP at the receiving point is D_ZΦ(q,P(ℛq)) composed with its m
arguments D_zℛ(q). Thus ||A_m(q)||≤q_Jc^m=:q_m<1. All other terms in F_m are finite
sums/compositions of derivatives of Φ and ℛ through order m and receiving derivatives of P
strictly below m. These are the known lower terms of the source tangent-section induction, with
their original iterated Hom types; no smooth parameter derivative or changing graph is
introduced.

Verify the coefficient order before the next own-jet argument. Differentiating A_m and F_m once
uses Φ through order m+1, ℛ through order m+1 and P through order m. The rational Φ depends on
the supplied first derivative of G evaluated on the known graph and on the original upper
inverse. Consequently these orders require G through m+2 and w through m+1; the inverse/chain
rules use only known graph derivatives and the original invertibility bound. Differentiating a
lower receiving derivative of P reaches at most Q_m, which is already known. It never requires
DQ_m. Step9's compact-model preparation therefore gives bounded jointly continuous A_m,F_m and
their FIRST fibre derivatives on the same smaller inward discs, together with a finite bound M_m
for Q_m. Their original-norm two-point segment bounds give finite Lipschitz constants L_A,L_F.
For m=r−2 this uses exactly G^r, not G^(r+1); G^r is used only continuously after differentiating
G^(r−1). Finitely many shrinkings leave one positive common radius for all orders.

Apply the same bounded-forcing Lipschitz preparation as on HPS pp32–33, now to the affine
equation for the known Q_m. At q,q′ in one original fibre, subtract its two instances; compare
the coefficient at q with the receiving Q_m difference, and bound the coefficient change times
the known M_m. This gives
||Q_m(q)−Q_m(q′)||≤q_m||Q_m(ℛq)−Q_m(ℛq′)||+(L_A M_m+L_F)||z−z′||.
After N inward returns the bounded residual is at most 2M_m q_m^N, while the error is at most
(L_A M_m+L_F)||z−z′||∑_{i<N}(q_mc)^i. Let N→∞. The result is the original fibre bound
Lip(Q_m)≤(L_A M_m+L_F)/(1−q_mc). Zero factors use the same comparison directly; neither c nor q_J
is inverted. This establishes the prerequisites BEFORE differentiating Q_m.

Use the already reconstructed HPS3.3/pp33–35 own-jet/closed affine-jet identification below, with
p58's point-valued return and the actual possibly nonzero anchor Q_m(ℛq), on these prepared
domains and coefficient/Lipschitz bounds. No new graph, global cutoff, smooth base, inverse of K
or higher derivative of Q_m is assumed. The source induction and the explicit finite-order/radius
bindings are distinguished: the latter are quantitative applications of the known-jet source
algorithm, not a printed arbitrary-parameter Theorem3.5.

11a. Write H_m,q for the original finite-dimensional normed fibre of the already known D^mP in
its usual iterated real continuous-linear-map coordinates. Apply the complete original-fibre and
iterated Hom construction of10a/6c to H_m,q and L(V_q,H_m,q). At each spatial anchor translate
input and the actual value Q_m(q) to0. HPS3.3 gives the Banach bounded Lipschitz jets there and
its closed differentiable/affine subspace, isometric to L(V_q,H_m,q). The dependent lp∞ product
over ALL spatial anchors is complete; its affine subspace is closed, and coordinate norm bounds
give closed complete balls by the existing closed-subtype API. This uses the original operator
norms, with only jet bookkeeping discrete; it does not identify the original parameter topology
with a discrete topology. Empty anchors and zero derivative/input models give the corresponding
singleton coordinates directly.

11b. For a derivative candidate ψ at ℛq, use the affine germ u↦Q_m(ℛq)+ψu, anchored at the KNOWN
actual Q_m(ℛq), not at zero. The fixed affine identity supplies the output representative
 v↦A_m(q+v)[Q_m(ℛq)+ψ(ℛ(q+v)−ℛq)]+F_m(q+v)−Q_m(q).
It has value0 at v=0. Its domains are the existing common original source/receiving germs:
continuity of ℛ lets one restrict the source germ to the receiving neighborhood. Unlike the
rational slope action in10b, this action is affine on the ENTIRE higher Hom fibre; no unit-disc
norm restriction or new slack is required. Since A_m,F_m,ℛ are already fibre-C¹ with the stated
bounds, the chain-rule API gives the derivative affine action
 𝔄_m,q(ψ)=D A_m(q)[Q_m(ℛq)]+A_m(q)ψDℛ(q)+D F_m(q).
The coefficient of ψ has norm≤q_m c=:μ_m<1 by the existing composition-norm bounds. Its forcing
is bounded and jointly continuous because D A_m,D F_m,Q_m and ℛ are already known; denote a
nonnegative bound by B_m. The derivative of Q_m is NOT used in this calculation: the only Q_m
value is the fixed anchor Q_m(ℛq). Differentiable input affine germs yield differentiable output
germs, realizing the closed J_diff preservation printed on p34. The derivative/segment estimate
supplies local two-point Lipschitz representatives after a convex germ restriction.

11c. Use the direct bounded-section Picard algorithm of HPS p25/p58 on the closed affine carrier,
as in10c. Put L_m=(L_A M_m+L_F)/(1−μ_m) for the retained Lipschitz bound and N_m=L_m+B_m/(1−μ_m).
The section action reads (𝒯_m S)(q)=𝔄_m,q(S(ℛq)); its output norm is≤B_m+μ_m N_m≤N_m and its
supremum contraction factor is μ_m. The complete closed ball contains0, so the existing
contracting fixed-point APIs give its unique bounded affine section S_m and uniform geometric
convergence of zero Picard iterates. Stable ℛ=K is only a point-valued forward evaluation: p58's
disjoint inverse-relation orientation is used, not the homeomorphism3.1 provider. No inverse of
K,T₂ or G, no one-time autonomous5.4 instantiation, and no(6.7) plaquated-base theorem is
invoked.

11d. Let j_m(q) be the own jet of the fixed Lipschitz Q_m and ℓ_m(q) its affine jet with
derivative S_m(q). The already valid Q_m affine identity makes j_m invariant under the displayed
representative action. The fixed S_m identity makes ℓ_m invariant under the SAME action. For any
η above their receiving jet distance, restrict the receiving germ so the normalized difference
is≤η. The common A_m(q+v) factor and ||A_m||≤q_m, followed by the original ||ℛ(q+v)−ℛq||≤c||v||
bound, give after taking the limsup
 d_m(q)≤μ_m d_m(ℛq).
For zero receiving displacement the compared germs agree exactly. The source action thus compares
the actual own jet only with a differentiable affine jet; it is not an assertion of an action on
the whole radial jet disc. Since d_m≤L_m+N_m, iteration on the retained inward domains gives
d_m(q)≤(L_m+N_m)μ_mⁿ→0 by the geometric-power API. HPS3.3 identifies the own Q_m germ modulo
little-o with its affine germ; hasFDerivAt_iff_isLittleO_nhds_zero yields the ACTUAL DQ_m=S_m.
This replaces the scalar Taylor derivative-defect argument rather than relabeling it. If c=0 or
q_J=0 then μ_m=0 and one comparison suffices, with no division by either. Zero-rank jet models
are direct.

11e. Joint continuity is obtained in the original iterated Hom charts by the p35 continuous
derivative-field mechanism and10e's exact implementation: the known coefficient/forcing and ℛ
families make each Picard iterate jointly continuous; original chart norm comparisons turn the
supremum geometric tail into uniform convergence of fixed-model coordinates, and
uniform_limit_continuous_on_set plus continuousAt_hom_bundle identifies a jointly continuous S_m.
The discrete jet bookkeeping is not used to infer this topology. Thus, on the common domains with
the coefficient/Lipschitz preparation established above, Q_m has a bounded jointly continuous
derivative and the ORIGINAL graph is fibre-C^(m+2) on those inward germs. Step9 supplies the
inward local preparation; Step12 proves the finite-return extension and fixed-disc C^r-sup
continuity. At m=r−2 the coefficient differentiations need precisely G^r, not G^(r+1); G^r need
only be continuous, since one differentiates G^(r−1). For r=2 only the preceding nonlinear base
step is needed; for r=1 only the first slope-defect proof is needed. This proves actual C^r local
graphs with joint derivatives in either strong branch.

12a. Extend the SAME fixed graphs from the inward C^r discs established by Steps9–11, using the
actual image equation of HPS pp54–55 and its local/full-preimage equation pp56–57. In the strong
unstable branch write w_p:E₁,p→E₂,p, H_p(x)=G₁,p(x,w_p(x)), and ℛ(p,x)=(h⁻¹p,H_(h⁻¹p)⁻¹(x)); in
the strong stable branch write t_p:E₂,p→E₁,p, K_p(y)=G₂,p(t_p(y),y), and ℛ(p,y)=(hp,K_p(y)).
These are the ORIGINAL globally constructed jointly continuous graph/return maps, not newly
chosen graphs. Their original input-norm constants are c=U<1 and c=V<1 respectively. Fix R≥0 and
choose a finite N≥1 with c^N R<δ/2, where δ is a common positive inward radius at the final
finite derivative order. This uses geometric decay, not a positive lower bound for c; if c=0 take
N=1. For any tested p₀ and input z₀ of original norm≤R form the finite original chain
(p_j,z_j)=ℛ^j(p₀,z₀), 0≤j≤N. The estimate ||z_j||_(p_j)≤c^j R places z_N in the OPEN known C^r
disc Dδ/2(p_N). At this point only joint C0 continuity of ℛ and its finite compositions is used.
No C^r regularity of the global return or of ℛ^N is assumed in order to select these anchors or
domains.

Choose genuine source and receiving linear bundle frames at each of the finitely many bases p_j.
Pull their OPEN base neighborhoods back by the appropriate finite h or h⁻¹ iterates and intersect
them. This is an open neighborhood of p₀ in the original, possibly non-Hausdorff parameter
topology. In those frames joint continuity of the original C0 chain puts its terminal point
inside the known inner graph germ, and puts all finitely many anchors inside their original chart
domains, after restricting an open product neighborhood of (p₀,z₀). Reconstruct graph germs
OUTWARD, j=N−1,…,0, using the already C^r receiving/source germ at stage j+1. At each stage the
known germ has a genuine open state domain and jointly continuous derivatives through r. Its
domains may be restricted further by ordinary product neighborhoods. When the germ has been
reconstructed at one stage, its equality with the fixed C0 graph supplies the germ used at the
next stage. This finite induction does not differentiate an unknown global return composition.

12b. Here are the precise original equations and state models at an outward stage. In the
unstable case put p=p_j and q=h⁻¹p=p_(j+1). On the known returned graph germ w_q define
Ξ_p(x)=H_q(x)=G₁,q(x,w_q(x)), from the source model of E₁,q to the receiving model of E₁,p. Its
tested derivative is A+B Dw_q, the original invertible upper block of Step6. The original image
equation is
 w_p(Ξ_p(x))=G₂,q(x,w_q(x)).
The existing horizontal inverse at the anchor is the original H_q⁻¹. Joint continuity of this
inverse and of the fixed graph permits restricting target states so that their source solution
stays in the chosen returned germ. The rank of the two E₁ models agrees because T₁,q is an
isomorphism; no equality of E₂ ranks is required.

In the stable case put p=p_j, p_next=hp=p_(j+1), and use the known receiving germ t_next on
E₂,p_next. On its genuine open preimage under G₂,p set
 Θ_p(x,y)=G₁,p(x,y)−t_next(G₂,p(x,y)),
 Ξ_p(x,y)=(Θ_p(x,y),y).
This is a full STATE map from E₁,p⊕E₂,p to E₁,p_next⊕E₂,p: the second TARGET factor is the SOURCE
E₂,p, not E₂,p_next. At the original graph anchor (t_p(y_j),y_j), G₂,p equals y_(j+1) and hence
belongs to the open known receiving germ. Continuity of G₂ and h lets us restrict a product
base/state neighborhood so that ALL evaluations of t_next stay in that SAME germ. The tested
derivative is the triangular continuous-linear map
 DΞ_p=[[L,Θ_y],[0,id]],   L=A−Dt_next C,
with inverse [[L⁻¹,−L⁻¹Θ_y],[0,id]], since Step6 supplies the actual upper inverse L⁻¹. Its
source and target dimensions agree through T₁,p, without assuming E₂,p and E₂,p_next have equal
dimensions. No inverse of K, T₂ or G is used. The original full-preimage graph equation, as HPS
pp56–57 writes even for a singular lower block, is
 Θ_p(t_p(y),y)=0.
Thus the desired original graph is the first coordinate of the local inverse of Ξ_p evaluated at
(0,y), once the image domain is established. Each Ξ_p is fibre-C^r with joint STATE derivatives
through r: it is a composition of supplied G jets with the already known returned graph jets in
paired linear frames. The parameter is p alone, never a differentiable parameter variable or an
unknown graph.

12c. Apply the WRITTEN local inverse mechanism of Glöckner, Finite order differentiability
properties, fixed points and implicit functions over valued fields,
arXiv:math/0511218v2(27April2007), Theorem5.3/Remark5.6 Equation66 pp41–43 and
Theorem5.10(a–c)pp45–47, to either full state map Ξ. This is an author-preprint component. In the
following local proof denote the arbitrary topological parameter by alpha, the full source state
by x and the source/target models by F_s,F_t, and set F(alpha,x)=Ξ_alpha(x). In particular,
stable y is part of x, not a parameter to which a parameter-smoothness theorem is silently
applied. The two models are finite-dimensional real Banach spaces, and the tested full derivative
A0:F_s→F_t is an actual continuous linear equivalence as just shown. The state domain is an
original open graph/receiving domain.

Let A0:F_s→F_t be the fixed invertible tested x derivative in these models. Normalize the
RECEIVING coordinates by this ONE fixed continuous linear inverse, setting f(alpha,x)=A0
inverse(F(alpha,x)). Thus f takes values in F_s, its tested x derivative is id_F_s, and the
comparison operator in Theorem5.10 is id. This is a fixed coordinate normalization of the same
equation, not a replacement of the original fibre norm or a parameter-dependent inverse family.
Original state derivatives and their given joint operator-norm continuity, the chain rule and
continuous composition/application of continuous linear maps supply the joint x derivative of f.
If F_s is zero, invertibility of A0 makes F_t zero too: the x carrier and local solution are
singletons, and continuity is direct. In that case omit every reciprocal norm and the following
nonzero-model estimates. Otherwise choose 0<eta<1. Joint continuity at the tested point, where
D_x f=id, supplies a smaller product Q×B with B=B_r(x0) in the SAME original open germ, r>0, on
which ||D_x f(alpha,x)−id||≤eta for every alpha,x. This is only a local bound derived from the
existing jets; no new global smallness hypothesis or smoothness of Q is imposed.

Derive the true two-point guard, not a radial value estimate. For u,v∈B and fixed alpha use the
scalar path ell(t)=f(alpha,u+t(v−u))−(u+t(v−u)), t∈[0,1]. Convexity of the open ball keeps its
entire closed segment inside B. The existing chain rule and the elementary derivative of the
affine line give HasDerivWithinAt ell ((D_x f(alpha,u+t(v−u))−id)(v−u)) [0,1] t, including the
endpoints by restriction of the derivative in the open state domain. Its norm is≤eta||v−u||.
Apply the EXACT scalar Real→F_s segment-derivative terminal with a=0,b=1,C=eta||v−u|| and
evaluation1. It gives ||f(alpha,v)−f(alpha,u)−(v−u)||≤eta||v−u||. Consequently the actual
two-point supremum required by Theorem5.10 is bounded by eta<1=1/||id inverse||. We use eta
directly as a valid common contraction bound; no empty or unbounded real csSup is assigned a
default value. Put a_star=1−eta>0.

Inline the written image-ball argument of Theorem5.3 and Remark5.6 Equation66. The two-point
inequality gives (1−eta)||v−u||≤||f_alpha(v)−f_alpha(u)||≤(1+eta)||v−u||, hence injectivity,
continuity and the Lipschitz inverse on its image. Given y∈B, 0<s≤r−||y−x0|| and
c∈f_alpha(y)+B_(a_star s)(0), choose 0<tau<1 with ||c−f_alpha(y)||<tau a_star s. The source proof
uses the CLOSED ball closedBall(y,tau s), not an open ball as a complete carrier. Its radius is
strictly below s, so it is wholly inside B even when s equals the distance to the outer boundary.
The original finite-dimensional real model F_s is complete and proper by the existing
finite-dimensional primitives. Its closed ball is compact by isCompact_closedBall, closed in its
Hausdorff model by isCompact_isClosed, and complete with the induced subtype metric by
isClosed_completeSpace_coe_g7. The point y belongs to this carrier. On it set
g(v)=v−(f_alpha(v)−c). The source calculation gives ||g(v)−y||≤eta||v−y||+||c−f_alpha(y)||≤tau s,
so it is a self-map, and ||g(v)−g(w)||≤eta||v−w||. The existing strict-contraction existence
theorem with NNReal eta and basepoint y applies; distances are finite in this model metric. Its
fixed point v0 has f_alpha(v0)=c, and uniqueness follows from the same two-point bound or the
existing fixed-point uniqueness leaf. Thus f_alpha(y)+B_(a_star s)(0)⊆f_alpha(B_s(y)). This is
the printed closed-ball proof and its image-ball consequence, using a common upper coefficient
eta; it is not a new inverse theorem.

Now follow the actual Theorem5.10(a–c) proof of W openness and joint inverse continuity. Let
W={(alpha,z):alpha∈Q,z∈f_alpha(B)} and psi(alpha,z)=(f_alpha|B) inverse(z). For any (alpha0,z0)∈W
choose y∈B with f_alpha0(y)=z0 and any 0<s≤r−||y−x0||. Joint continuity at the FIXED state y
gives a neighborhood Q0 of alpha0 with ||f_alpha(y)−z0||<a_star s/2 for alpha∈Q0. The just-proved
image inclusion yields Q0×B_(a_star s/2)(z0)⊆W and psi(alpha,z)∈B_s(y) throughout that product.
Taking s arbitrarily small proves that W is open and psi is jointly continuous in the original
parameter topology. This is precisely the source image-ball/product-neighborhood proof; it needs
no metric, compactness or differentiable structure on Q. The map (alpha,x)↦(alpha,f(alpha,x)) is
the stated homeomorphism onto W. Undo the fixed A0 inverse normalization to obtain the joint
local horizontal inverse for the original F and its original receiving coordinates.

12d. Follow the actual ordinary inverse proof of Wells, Invariant manifolds of non-linear
operators (1976), pp285–287, on this SAME local inverse. For fixed alpha, f_alpha is fibre-C^r on
B and Γ_alpha(x)=x−f_alpha(x) has the true two-point Lipschitz constant≤eta<1 just proved. The
existing source-backed Wells perturbation-inverse theorem gives a C^r inverse on the actual OPEN
image f_alpha(B); it needs neither a global extension nor bounded/uniformly continuous higher
derivatives. Its inverse agrees with psi(alpha,·) by the already proved injectivity. Undoing the
ONE fixed A0 normalization gives the same joint-continuous inverse J_p for the original Ξ_p on
the corresponding original open image W. The scalar state inverse/implicit APIs bind fibrewise
smoothness and the upper block; they do not differentiate p.

For joint higher STATE derivatives use Wells's written recursion on printed p287, rather than its
global C_U^r continuity table. The Lipschitz inverse and the little-o identity at an arbitrary
state give
 D_z J_p(z)=[D_v Ξ_p(J_p(z))]⁻¹.
Operator inversion is smooth near each tested continuous linear equivalence;
composition/application in the genuine Hom frames, joint continuity of J, and the known joint DΞ
make this derivative jointly continuous in (p,z). The isolated preceding printed formula on p287
has Df⁻¹ inside the inverse and is incorrect as written; the NEXT displayed composition
explicitly reads Df⁻¹=Inverse∘Df∘f⁻¹. It is that correct written composition, and the subsequent
P_k proof, that is followed here. No alleged erratum or silent use of the incorrect line is
asserted.

Induct on m=2,…,r by the actual finite polynomial P_m differentiation of Ξ_p∘J_p=id, with p
fixed. To spell out its types, for state directions v₁,…,v_m at a target z, separate the term
DΞ_p(J_p(z))[D^mJ_p(z)(v₁,…,v_m)] from the iterated chain rule. Every other term is indexed by a
partition π of {1,…,m} into k≥2 blocks and equals
 D^kΞ_p(J_p(z))[D^(|B₁|)J_p(z)(v_i:i∈B₁),…,D^(|B_k|)J_p(z)(v_i:i∈B_k)].
Consequently D^mJ is the NEGATIVE of the sum of these terms postcomposed with [DΞ_p(J_p(z))]⁻¹.
Every J derivative on the right has order<m, and every Ξ derivative has order≤m. These are the
finite multilinear contractions of Wells's P_m, in the original fixed local state/Hom models.
Known joint continuity, continuous operator inversion, and the finite sum/composition rules
therefore prove joint continuity of D^mJ. The per-fibre derivatives themselves exist by Wells's
C^r inverse proof, so this identity identifies their actual values; it does not posit
differentiability from separate continuity. For r=1 only the first formula is used. No derivative
of p,h or a smooth base is required; no global higher bounds or uniform continuity on the entire
open state domain from Wells's C_U^r table are assumed.

12e. Identify the reconstructed germ with the ORIGINAL graph at every outward stage. Unstably,
J_p(z) solves H_q(x)=z in the chosen known source germ. The already jointly continuous original
inverse H_q⁻¹(z) stays in its source ball after restricting a product neighborhood of the tested
target anchor; it solves that same equation, so local injectivity gives J_p(z)=H_q⁻¹(z). The HPS
image equation then gives
 w_p(z)=G₂,q(J_p(z),w_q(J_p(z))).
Its derivatives through r, obtained by the ordinary state chain rule, are jointly continuous
because all entries are now known. Stably, the open image W contains the tested (p₀,(0,y_j)). Its
preimage under the continuous map (p,y)↦(p,(0,y)) is OPEN. Restrict there and put
λ_p(y)=pr₁J_p(0,y). Since the second component of Ξ is the unchanged y, J_p(0,y)=(λ_p(y),y); λ is
fibre-C^r with joint state derivatives through r. The original C0 graph (t_p(y),y) stays in the
chosen source ball after restriction and satisfies exactly Θ_p(t_p(y),y)=0. The same local
injectivity yields λ_p(y)=t_p(y). This is the source local-preimage equation and zero-slice
argument (Glöckner Cor5.12p47), with a full state inverse to retain the y derivatives. It is
valid for a singular or zero lower block and for unequal adjacent lower ranks. Repeating these
local equations the finite N times produces a genuine open graph neighborhood of every (p₀,z₀)
with joint derivatives through r. There is no inference that arbitrary continuous transport of a
frame or homeomorphism has derivatives.

12f. Prove the fixed-disc C^r supremum topology using the written
compact-slice/product-neighborhood mechanism of Munkres, Topology2ed(2000), Theorem26.7 Step1
pp167–168 and Lemma26.8p168, with the existing compact_eventually_forall API. Fix p₀, one genuine
input/output bundle frame near p₀, and a fixed compact MODEL closed input disc K with a slightly
larger open state neighborhood. Finite-dimensional properness and isCompact_closedBall make K
compact in that model. If original varying-norm discs of radius R must be included, first choose
a larger p₀-model disc and restrict the open base neighborhood by the compact-sphere norm
comparison of Step9; then every required p-original disc is inside K, with positive outer margin.
No compactness or Hausdorffness of the base neighborhood is used.

For each z₀∈K the preceding finite C0-anchor/outward-germ construction gives a product
P_(z₀)×O_(z₀), with P_(z₀) open about p₀ and O_(z₀) open about z₀, on which the SAME fixed graph
and all of its derivatives through r are known jointly continuous. Apply compactness to the open
state cover {O_(z₀)} of K, or to its directed finite unions using the existing compact
directed-cover terminal, and choose finitely many such state neighborhoods covering K. Intersect
their finitely many OPEN base neighborhoods; the resulting P contains p₀, and on P×(union O_(z₀))
the graph jets are jointly continuous. On overlaps these are derivatives of one and the same
already constructed graph, so uniqueness of the Frechet derivative, iterated through the finite
orders, makes them agree. This is a finite restriction of genuine open neighborhoods, not a new
patched graph, a compact closed base-core refinement or a globally chosen frame. The terminal
domains remain the original receiving graph germs selected before inversion.

Write J_j(p,z)=D_z^j w_p(z) or D_z^j t_p(z), with J₀ the graph map, in the genuine fixed iterated
Hom frames over this P. For each j=0,…,r, joint continuity gives the open relation
 ||J_j(p,z)−J_j(p₀,z)||<ε
in a product neighborhood of every (p₀,z₀), z₀∈K. Here z↦J_j(p₀,z) is a continuous reference
field on the SAME fixed model K, not a comparison between unidentified fibres. The exact
compact_eventually_forall input gives an open neighborhood of p₀ on which this inequality holds
for ALL z∈K. Intersect these neighborhoods for the finitely many j. Compact continuous-bound and
the same tube inequality give finite bounds for every compared norm on K, so each displayed
supremum is genuinely bounded; no default csSup on an unbounded family is used. Thus
 max_(0≤j≤r) sup_(z∈K)||J_j(p,z)−J_j(p₀,z)||→0
as p→p₀ in the original topology. This is precisely continuous C^r dependence on fixed local
fibre discs. Actual continuous Hom-frame/norm comparisons ensure the original bundle-chart
interpretation, without changing the fibre norms or invoking a global frame, bundle uniformity,
closed continuous-section carrier or Wells's global C_U^r assumptions.

12g. The construction is local at arbitrary graph points, hence proves fibre-C^r on the entire
strong graph and the asserted C^r dependence on every fixed bounded local disc. At ρ=1 use the
two independent returns U<1 and V<1 and apply the two reconstructions separately. If A is empty
all assertions are vacuous. A zero input model has compact carrier {0} and the centered graph is
zero, so its higher jets and the supremum comparisons are direct; there is no reciprocal of a
sphere radius, rank or c. At any nontrivial triangular stage only the tested full
continuous-linear equivalence is inverted; if its entire state model is zero both models and the
local inverse are singletons. Zero E₁ along an h-orbit is preserved by T₁; no invariance of a
zero E₂ stratum is asserted. The proof is a guarded combination of the written HPS
image/local-preimage equations, the author-preprint full-W local inverse, Wells's ordinary
inverse/P_m algorithm and the compact MODEL slice proof. Their exact applications and finite
dimensional/derivative APIs are explicit above. Together with Steps1–11 and13–14 this proves the
stated graph families, strong-branch regularity, continuous C^r dependence and normalized local
orbit characterization, relative to the named lower inputs.

Follow the actual HPS pp.58–60 cone/graph-equality proof, with the parameter insertion of p.62
and the original fibre norms throughout. Write G_p^N for the actual N-fold composition from E_p
to E_(h^N(p)), with G_p^0=id. Define the CLOSED horizontal and vertical cones
 S₁,p={(x,y):‖x‖≥‖y‖},   S₂,p={(x,y):‖y‖≥‖x‖}.
The source's W₁,p is ∩_(N≥0) G_(h⁻ᴺ(p))^N(S₁,h⁻ᴺ(p)); membership means for EACH N there exists an
N-th preimage in that cone. These preimages may be independent and are not assumed to form a
coherent history. The source's W₂,p consists of points whose actual forward iterates all lie in
S₂,hᴺ(p). These are whole original fibre sets for the already globally defined G; no cutoff or
extension premise is needed.

13a. On strata with nonzero E₁ use L=m₀−ε, M=m₀−3ε, B=k+2ε from the small choice added to step1.
They satisfy L>M>ρ>B≥V=k+ε≥0, so L>0, M>0. For z=(x,y)∈S₁,p the original maximum norm is‖x‖; the
upper-block lower bound gives ‖G₁,p z‖≥L‖x‖=L‖z‖, while ‖G₂,p z‖≤k‖y‖+ε‖z‖≤V‖z‖. Since L>V, every
nonzero horizontal-cone point maps into the STRICT horizontal cone; zero maps tozero. In
particular S₁ is forward invariant and ‖G_pz‖≥L‖z‖ there. For z∈S₂,p the original maximum norm
is‖y‖, and ‖G₂,pz‖≤V‖z‖. Hence whenever its next iterate also lies in S₂, ‖G_pz‖=‖G₂,pz‖≤V‖z‖.
These are the original same-fibre cone bounds used in the source, not coordinate-norm quotients.

13b. Use the actual graph families s*,t* already constructed in steps3–5, and abbreviate them
s,t. Let Δ_s,p(x,y)=‖x−t_p(y)‖ and Δ_u,p(x,y)=‖y−s_p(x)‖. Both are≤2‖(x,y)‖, by the centered unit
graph slopes. The printed HPS p.58 inequalities(1),(2), in the present fixed-T convention, may be
used in their coarser separated form
 ‖G₁,pz−G₁,pz'‖≥(m₀−ε)‖x−x'‖−ε‖z−z'‖,
 ‖G₂,pz−G₂,pz'‖≤(k+ε)‖y−y'‖+ε‖z−z'‖.
The original step1 sharper bounds imply these inequalities by decreasing the horizontal
coefficient and increasing the lower-block coefficient. Compare z=(x,y) with w=(t_p(y),y). The
same-y horizontal inequality gives at least(m₀−2ε)Δ_s,p(z); the vertical difference is≤εΔ_s,p(z).
Because G_pw lies on the receiving stable graph and that graph has unit slope, the triangle
inequality gives the source p.59(3) transverse estimate
 Δ_s,h(p)(G_pz)≥(m₀−3ε)Δ_s,p(z)=MΔ_s,p(z).
This is the actual printed coarse source factor, rather than reusing the former sharper m₀−2ε
scalar-defect alternative. For the unstable comparison take w=(x,s_p(x)). Its image is on the
receiving unstable graph. The ORIGINAL same-x vertical estimate is ‖G₂,pz−G₂,pw‖≤(k+ε)Δ_u,p(z),
and the original R₁ same-x horizontal estimate is ‖G₁,pz−G₁,pw‖≤εΔ_u,p(z). The receiving unstable
graph has unit slope, so its horizontal correction contributes at most the latter εΔ_u term.
Consequently
 Δ_u,h(p)(G_pz)≤[(k+ε)+ε]Δ_u,p(z)=(k+2ε)Δ_u,p(z)=BΔ_u,p(z).
This is the source p.59(4) forward transverse contraction, which is used backward along preimages
without dividing by B. No alleged source typo/erratum or new rate is introduced.

13c. Every unstable graph point is in W₁,p: the actual whole H inverse from step4 supplies its
canonical graph preimages of every depth, all in S₁ by the unit graph slope. Every stable graph
point is in W₂,p: the actual whole K forward graph return from step5 stays on that graph in S₂.
Conversely for z∈W₂,p, iteration of the source transverse estimate and the vertical-cone norm
bound gives
 M^NΔ_s,p(z)≤Δ_s,hᴺ(p)(G_p^Nz)≤2‖G_p^Nz‖≤2V^N‖z‖.
Since M>0 and 0≤V/M<1, divide only by M^N and use the exact geometric-decay leaf to obtain
Δ_s,p(z)=0. Thus W₂,p is exactly the stable graph. For z∈W₁,p choose an independent N-th preimage
z_−N∈S₁,h⁻ᴺ(p). Its finite forward chain stays in S₁ by cone invariance, so ‖z_−N‖≤L^(−N)‖z‖. The
forward unstable transverse estimate gives
 Δ_u,p(z)≤B^NΔ_u,h⁻ᴺ(p)(z_−N)≤2(B/L)^N‖z‖.
As L>0 and 0≤B/L<1, geometric decay gives Δ_u,p(z)=0. Hence W₁,p is exactly the unstable graph.
This proof uses independent N-th preimages just as the actual source does, and takes no ratio of
vector coordinates or division by B or V, so their zero values pose no difficulty.

13d. Localize the graph inclusion in the strong branches as in HPS(5.4) pp.60–61 and the orbit
characterization p.60. Choose the SAME common original fibre radius b>0 and use graph
representatives over ‖x‖<b or ‖y‖<b. Since a centered unit graph in the maximum norm has the norm
of its base coordinate, the canonical unstable graph backward map has boundU, and in the strong
unstable branch U<min(1,ρ⁻¹). It therefore supplies a coherent backward graph history z_−N in the
original fibres E_(h⁻ᴺ(p)) with ‖z_−N‖≤U^N‖z‖<b at every step. Multiplying byρ^N gives
‖z_−N‖/ρ^(−N)≤(Uρ)^N‖z‖→0. In the strong stable branch the canonical graph forward map has
boundV<min(1,ρ), so its whole history remains in the SAME radius b and ‖G_p^Nz‖/ρ^N≤(V/ρ)^N‖z‖→0.
The geometric-decay leaf applies to both ratios, includingV=0; limit zero implies bounded
normalized norms. These are actual coherent histories when required by the local target, not an
assumed coherence of the W₁ preimage witnesses. Atρ=1 both strong branches apply. The moving
fibres and original norms remain unchanged; no ambient manifold chart or self-coherent
exponential-image plaque is asserted.

13e. Empty A is vacuous. The zero E₁ stratum is h-INVARIANT because T₁,p is a linear isomorphism,
so E₁,p=0 iff E₁,h(p)=0. On this stratum no m₀=1/a is used: the stable graph is the entire
vertical fibre and ‖G_pz‖≤V‖z‖ directly; S₂ is the whole fibre, S₁ is{0}, and every G_p^N({0})
is{0}, so W₂ is the stable graph and W₁ is the zero unstable graph directly. In the strong stable
branch the same V bound supplies the local retained forward history; the unstable graph's only
history iszero. For possibly zero E₂ at selected parameters, do NOT assume that its zero-rank
stratum is h-invariant: T₂ may be singular. On any nonzero E₁ orbit the preceding comparisons
remain valid using the actual source and receiving fibres, including zero receiving values; they
never divide by a vertical coordinate or invert T₂. If all E₂ fibres arezero, their graph/Hom
carriers have their obvious zero coordinates, but no such global-zero condition is added to the
theorem.

Complete the normalized bounded-orbit exclusion by the LITERAL source HPS p.60 cone-exit and
CLOSED full-preimage lower-bound argument, with the original same-fibre compositions and
parameter insertion of p.62. Use the cone/graph equalities of step13, not the superseded sharper
equal-horizontal c₁ or scalar Taylor-defect estimates.

14a. On a nonzero E₁ orbit, if z is not on the stable graph, it is not in W₂, so for some N its
actual forward iterate z_N lies OUTSIDE the closed vertical cone S₂,hᴺ(p), hence in the STRICT
horizontal cone. It is nonzero. By the source forward horizontal-cone invariance, every
subsequent forward iterate stays in S₁ and has norm at least L^m‖z_N‖. Since L>ρ, a bound
‖G_p^nz‖≤Cρ^n would give
 ‖z_N‖≤Cρ^N(ρ/L)^m
for every m, contradicting ‖z_N‖>0 as the geometric factor tends tozero. This proves that no
retained forward orbit with bounded normalized norms can start off the stable graph; retention in
a common local disc only restricts these same actual iterates and cannot defeat the
contradiction. Conversely step13 supplies the retained graph forward history with normalized
limitzero in the strong stable branch. Thus the target's bounded normalized local forward
condition is exactly stable graph membership. On the h-invariant zero E₁ stratum every point is
on the vertical stable graph, so the exclusion is empty and the directV graph-history bound
applies without m₀.

14b. If z is not on the unstable graph, then by W₁=graph(s) some N satisfies
z∉G_(h⁻ᴺ(p))^N(S₁,h⁻ᴺ(p)). Put
 P_N={w∈E_(h⁻ᴺ(p)):G_(h⁻ᴺ(p))^N(w)=z},
the FULL original fixed-fibre N-th preimage set. This set may be empty. If it is empty, no
coherent backward history of lengthN exists and hence the target backward-orbit condition already
fails. If P_N is nonempty, every w∈P_N lies outsideS₁ and therefore in the STRICT vertical cone.
Also z≠0, since the zero point lies on the unstable graph, and G fixes0. The finite composition
G_(h⁻ᴺ(p))^N is continuous between the ORIGINAL normed fibres. The singleton{z} is closed by the
existing is_closed_singleton_g8 leaf under the original T1 (in fact Hausdorff) normed topology;
the existing isClosed_preimage_g8 makes P_N closed in its ORIGINAL source fibre. It excludes0
because that composition sends0 to0≠z. Thus the complement of P_N is open and contains0. Apply
metric_isOpen_iff_g8 in that same original normed fibre to obtain d>0 with B(0,d)⊆P_Nᶜ. Every
w∈P_N has ‖w‖≥d. This is the exact source closed nonzero-preimage positive-distance step: no
compactness of P_N, infimum attainment, coordinate minimum or extra norm is assumed.

Now suppose a coherent backward history z_−n existed with G_(h^−n(p))(z_−n)=z_−(n−1) and
‖z_−n‖≤Cρ^(−n) for all n. Its N-th term z_−N lies in P_N, so d≤‖z_−N‖. For any m≥0 all terms
z_−(N+j),0≤j≤m, lie inS₂: if an earlier term were inS₁, forwardS₁ invariance would put z_−N inS₁,
contrary to P_N∩S₁=∅. Apply the source vertical-cone forward bound to that finite coherent chain,
where both adjacent points lie inS₂, to obtain
 d≤‖z_−N‖≤V^m‖z_−(N+m)‖≤Cρ^(−N)(V/ρ)^m.
Here0≤V/ρ<1 in each permitted case. On a nonzero E₁ orbit, the source constants give V≤B<ρ. On
the h-invariant zero E₁ stratum, use instead the preserved choice c₁=V/(1−aε)<ρ and0≤aε<1: it
gives V=(1−aε)c₁≤c₁<ρ. This includes the globally zero E₁ case a=0, where c₁=V. Thus the
zero-stratum argument does not use B, which was introduced only on nonzero E₁ strata. Geometric
decay contradicts d>0. This formulation remains valid whenV=0 and uses no division byV or B. It
requires neither inverse/surjectivity of G or T₂ nor compactness of the preimage set. The
original source's inverse iterates may be independent before this point; the target condition
itself supplies the coherent history used in this exclusion. If the source E₁ iszero along its
h-invariant orbit, then S₂ is the entire fibre and the same closed-preimage/verticalV argument
proves exclusion of every nonzero point from the zero unstable graph, without L,M or m₀. No claim
that a selected zero E₂ stratum is h-invariant is used.

14c. Therefore any retained coherent backward orbit with bounded ‖z_−n‖/ρ^(−n) starts on the
actual unstable graph. Conversely in the strong unstable branch step13's canonical H⁻¹ graph
history remains within the SAME original radiusb, is coherent, and has normalized norms tending
tozero; the zero graph case is immediate. Likewise in the strong stable branch forward bounded
normalized retention is precisely stable graph membership, with graph history limitzero. Atρ=1
both statements apply. All cone and preimage calculations occur in the actual original moving
fibres, for the globally given G; the local b restriction merely selects graph representatives
and retained histories. This completes the source orbit component and does not assert higher
fibre regularity or self-coherent ambient plaques. Step1 supplies the original quantitative
guards, and Steps9–12 supply the higher regularity and fixed-disc C^r dependence of these same
graph families.


-/

theorem parameter_graph_construction
    [CompactSpace A] (r : ℕ) (hr : 1 ≤ r)
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (hT : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, (T₁ z.1 z.2.1, T₂ z.1 z.2.2)⟩ :
        Sigma (fun p ↦ E₁ p × E₂ p))))
    (ρ : ℝ) (hρ : 0 < ρ)
    (ha : sSup (Set.range (fun p ↦ ‖(T₁ p).symm.toContinuousLinearMap‖)) < ρ⁻¹)
    (hk : sSup (Set.range (fun p ↦ ‖T₂ p‖)) < ρ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p),
        JointFiberContDiff e.total e.total h r G →
        (∀ p, G p 0 = 0) →
        (∀ p, fderiv ℝ (G p) 0 = (T₁ p).toContinuousLinearMap.prodMap (T₂ p)) →
        (∃ η : NNReal, (η : ℝ) < δ ∧ ∀ p,
          LipschitzWith η (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2))) →
        ∃ s : ∀ p, E₁ p → E₂ p, ∃ t : ∀ p, E₂ p → E₁ p,
          (∀ p, s p 0 = 0 ∧ t p 0 = 0 ∧
            LipschitzWith 1 (s p) ∧ LipschitzWith 1 (t p)) ∧
          (∀ p, G p '' Set.range (fun x ↦ (x, s p x)) =
            Set.range (fun x ↦ (x, s (h p) x))) ∧
          (∀ p, G p ⁻¹' Set.range (fun y ↦ (t (h p) y, y)) =
            Set.range (fun y ↦ (t p y, y))) ∧
          JointFiberContDiff e.first e.second id 1 s ∧
          JointFiberContDiff e.second e.first id 1 t ∧
          (∀ p, fderiv ℝ (s p) 0 = 0 ∧ fderiv ℝ (t p) 0 = 0) ∧
          (1 ≤ ρ →
            JointFiberContDiff e.first e.second id r s ∧
            FixedDiscCrContinuous e.first e.second id r s ∧
            ∃ d : ℝ, 0 < d ∧ ∀ p (z : E₁ p × E₂ p), ‖z‖ < d →
              (z ∈ Set.range (fun x ↦ (x, s p x)) ↔
                ∃ v : ℕ → Sigma (fun p ↦ E₁ p × E₂ p),
                  v 0 = ⟨p, z⟩ ∧
                  (∀ n, (⟨h (v (n + 1)).1, G (v (n + 1)).1 (v (n + 1)).2⟩ :
                    Sigma (fun p ↦ E₁ p × E₂ p)) = v n) ∧
                  (∀ n, ‖(v n).2‖ < d) ∧
                  ∃ C : ℝ, 0 < C ∧ ∀ n, ‖(v n).2‖ ≤ C * (ρ⁻¹) ^ n)) ∧
          (ρ ≤ 1 →
            JointFiberContDiff e.second e.first id r t ∧
            FixedDiscCrContinuous e.second e.first id r t ∧
            ∃ d : ℝ, 0 < d ∧ ∀ p (z : E₁ p × E₂ p), ‖z‖ < d →
              (z ∈ Set.range (fun y ↦ (t p y, y)) ↔
                let g : Sigma (fun p ↦ E₁ p × E₂ p) →
                    Sigma (fun p ↦ E₁ p × E₂ p) :=
                  fun v ↦ ⟨h v.1, G v.1 v.2⟩
                (∀ n : ℕ, ‖((g^[n]) ⟨p, z⟩).2‖ < d) ∧
                ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
                  ‖((g^[n]) ⟨p, z⟩).2‖ ≤ C * ρ ^ n)) := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · refine ⟨1, zero_lt_one, ?_⟩
    intro G hG hzero hderiv hsmall
    refine ⟨(fun p ↦ isEmptyElim p), (fun p ↦ isEmptyElim p), ?_⟩
    simp [JointFiberContDiff, FixedDiscCrContinuous]
    exact ⟨fun _ ↦ ⟨1, zero_lt_one⟩, fun _ ↦ ⟨1, zero_lt_one⟩⟩
  · let : ∀ p, CompleteSpace (E₁ p) := fun p ↦ parameter_graph_fibre_complete e.first p
    let : ∀ p, CompleteSpace (E₂ p) := fun p ↦ parameter_graph_fibre_complete e.second p
    obtain ⟨hsclosed, hscomplete, hsnonempty⟩ := parameter_graph_carrier_complete E₁ E₂
    obtain ⟨htclosed, htcomplete, htnonempty⟩ := parameter_graph_carrier_complete E₂ E₁
    let : CompleteSpace {q : ParameterGraphCarrier E₁ E₂ // q ∈ parameterGraphUnitSet E₁ E₂} :=
      hscomplete
    let : CompleteSpace {q : ParameterGraphCarrier E₂ E₁ // q ∈ parameterGraphUnitSet E₂ E₁} :=
      htcomplete
    let : Nonempty {q : ParameterGraphCarrier E₁ E₂ // q ∈ parameterGraphUnitSet E₁ E₂} :=
      hsnonempty.to_subtype
    let : Nonempty {q : ParameterGraphCarrier E₂ E₁ // q ∈ parameterGraphUnitSet E₂ E₁} :=
      htnonempty.to_subtype
    let a : ℝ := sSup (Set.range (fun p ↦ ‖(T₁ p).symm.toContinuousLinearMap‖))
    let k : ℝ := sSup (Set.range (fun p ↦ ‖T₂ p‖))
    have ha0 : 0 ≤ a := Real.sSup_nonneg (by rintro _ ⟨p, rfl⟩; exact norm_nonneg _)
    have hk0 : 0 ≤ k := Real.sSup_nonneg (by rintro _ ⟨p, rfl⟩; exact norm_nonneg _)
    obtain ⟨δ, hδ, hthreshold⟩ := parameter_graph_contraction_threshold a k ρ ha0 hk0 hρ ha hk
    refine ⟨δ, hδ, ?_⟩
    intro G hG hzero hderiv hsmall
    obtain ⟨η, hηδ, hη⟩ := hsmall
    obtain ⟨hsmall₂, hden₁, hden₂, hpreimage, himage, hjet, hslope, hinverseJet,
      hstableRate, hverticalRate, hunstableRate, hunstableStrong, hstableStrong, hexpansion⟩ :=
      hthreshold η η.coe_nonneg hηδ
    have hbounds :
        (∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a) ∧
        (∀ p, ‖T₂ p‖ ≤ k) := by
      simpa [a, k] using parameter_graph_original_norm_bounds e h T₁ T₂ hT
    let aN : NNReal := ⟨a, ha0⟩
    let kN : NNReal := ⟨k, hk0⟩
    let qI : NNReal := ⟨a * (k + η) / (1 - a * η) ^ 2,
      div_nonneg (mul_nonneg ha0 (add_nonneg hk0 η.coe_nonneg)) (sq_nonneg _)⟩
    let qP : NNReal := ⟨a * (k + η) / (1 - 2 * a * η),
      div_nonneg (mul_nonneg ha0 (add_nonneg hk0 η.coe_nonneg)) hden₂.le⟩
    obtain ⟨Φs, hΦs, hΦsgraph⟩ := parameter_graph_image_carrier E₁ E₂ h.toEquiv
      T₁ T₂ G hzero aN kN η qI hbounds.1 hbounds.2
      (by change a * (η : ℝ) < 1; linarith) hslope.le le_rfl hpreimage hη
    obtain ⟨Φt, hΦt, hΦtgraph⟩ := parameter_graph_preimage_carrier E₁ E₂ h
      T₁ T₂ G hzero aN kN η qP hbounds.1 hbounds.2 hsmall₂ hslope le_rfl himage hη
    obtain ⟨qs, hqs, _⟩ := parameter_graph_fixedPoint Φs qI hΦs
    obtain ⟨qt, hqt, _⟩ := parameter_graph_fixedPoint Φt qP hΦt
    let s : ∀ p, E₁ p → E₂ p := parameterGraphValue E₁ E₂ qs.1
    let t : ∀ p, E₂ p → E₁ p := parameterGraphValue E₂ E₁ qt.1
    have hs (p : A) : s p 0 = 0 ∧ LipschitzWith 1 (s p) :=
      ⟨by simp [s, parameterGraphValue], qs.2 p⟩
    have ht (p : A) : t p 0 = 0 ∧ LipschitzWith 1 (t p) :=
      ⟨by simp [t, parameterGraphValue], qt.2 p⟩
    have hsgraph (p : A) : G p '' Set.range (fun x ↦ (x, s p x)) =
        Set.range (fun x ↦ (x, s (h p) x)) := by
      simpa only [hqs, s, Homeomorph.coe_toEquiv] using hΦsgraph qs p
    have htgraph (p : A) : G p ⁻¹' Set.range (fun y ↦ (t (h p) y, y)) =
        Set.range (fun y ↦ (t p y, y)) := by
      simpa only [hqt] using hΦtgraph qt p
    have hGtotal := parameter_graph_joint_value_continuous e.total e.total h h.continuous G r hG
    have hsc : Continuous (fun z : Sigma E₁ ↦ (⟨z.1,s z.1 z.2⟩ : Sigma E₂)) := by
      exact parameter_graph_image_fixed_continuous e h T₁ T₂ G hGtotal hzero aN kN η qI
        hbounds.1 hbounds.2 (by change a*(η:ℝ)<1; linarith) hslope.le hη
        Φs hΦs hΦsgraph qs hqs
    have htc : Continuous (fun z : Sigma E₂ ↦ (⟨z.1,t z.1 z.2⟩ : Sigma E₁)) := by
      exact parameter_graph_preimage_fixed_continuous e h T₁ T₂ G hGtotal aN η qP
        hbounds.1 hsmall₂ hη Φt hΦt hΦtgraph qt hqt
    have hregularity :
        JointFiberContDiff e.first e.second id 1 s ∧
        JointFiberContDiff e.second e.first id 1 t ∧
        (1 ≤ ρ → JointFiberContDiff e.first e.second id r s) ∧
        (ρ ≤ 1 → JointFiberContDiff e.second e.first id r t) := by
      exact parameter_graph_fixed_graph_regularity r hr ρ e h T₁ T₂ G hG hzero hderiv
        aN kN η hbounds.1 hbounds.2 hsmall₂ hjet hslope.le hinverseJet
        (fun hρ ↦ (hunstableStrong hρ).trans_le (min_le_left _ _))
        (fun hρ ↦ (hstableStrong hρ).trans_le (min_le_left _ _)) hη s t
        (fun p ↦ ⟨(hs p).1, (hs p).2⟩) (fun p ↦ ⟨(ht p).1, (ht p).2⟩)
        hsc htc hsgraph htgraph
    have hDG (p : A) : HasFDerivAt (G p)
        ((T₁ p).toContinuousLinearMap.prodMap (T₂ p)) 0 := by
      rw [← hderiv p]
      exact ((hG.1 p).differentiable (by simpa using (show r ≠ 0 by omega)) 0).hasFDerivAt
    have hgap : (aN : ℝ) * kN < 1 := by
      change a * k < 1
      have : a * (2 * (η : ℝ)) ≥ 0 := mul_nonneg ha0 (by positivity)
      nlinarith
    have htangent := parameter_graph_zero_derivative h.toEquiv T₁ T₂ G hzero hDG
      aN kN hgap hbounds.1 hbounds.2 s t
      (fun p ↦ ⟨(hs p).1, (hs p).2,
        ((hregularity.1.1 p).differentiable (by norm_num) 0)⟩)
      (fun p ↦ ⟨(ht p).1, (ht p).2,
        ((hregularity.2.1.1 p).differentiable (by norm_num) 0)⟩)
      (fun p x ↦ by
        obtain ⟨y, hy⟩ := hsgraph p ▸
          (show G p (x, s p x) ∈ G p '' Set.range (fun x ↦ (x, s p x)) from
            ⟨(x, s p x), ⟨x, rfl⟩, rfl⟩)
        rw [← hy]; rfl)
      (fun p y ↦ by
        have hm : (t p y, y) ∈ G p ⁻¹' Set.range (fun y ↦ (t (h p) y, y)) := by
          rw [htgraph]; exact ⟨y, rfl⟩
        obtain ⟨v, hv⟩ := hm
        rw [← hv]; rfl)
    refine ⟨s, t, (fun p ↦ ⟨(hs p).1, (ht p).1, (hs p).2, (ht p).2⟩),
      hsgraph, htgraph, hregularity.1, hregularity.2.1, htangent, ?_, ?_⟩
    · intro hρ₁
      have hsr := hregularity.2.2.1 hρ₁
      refine ⟨hsr, parameter_graph_fixed_disc_continuity e.first e.second id
        continuous_id r s hsr, 1, zero_lt_one, ?_⟩
      intro p z hz
      exact parameter_graph_unstable_orbit_characterization h.toEquiv T₁ T₂ G hzero
        aN kN η ρ hρ hρ₁ (by change a * (η : ℝ) < 1; linarith)
        hunstableRate.le hverticalRate hbounds.1 hbounds.2 hη s hs hsgraph 1 p z hz
    · intro hρ₁
      have htr := hregularity.2.2.2 hρ₁
      refine ⟨htr, parameter_graph_fixed_disc_continuity e.second e.first id
        continuous_id r t htr, 1, zero_lt_one, ?_⟩
      have hexpand : ∃ m : ℝ, 0 ≤ m ∧ ρ < m - 3 * (η : ℝ) ∧
          ∀ p, m * ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ 1 := by
        by_cases ha' : 0 < a
        · refine ⟨a⁻¹, inv_nonneg.mpr ha0, hexpansion ha', ?_⟩
          intro p
          calc
            a⁻¹ * ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a⁻¹ * a :=
              mul_le_mul_of_nonneg_left (hbounds.1 p) (inv_nonneg.mpr ha0)
            _ = 1 := inv_mul_cancel₀ ha'.ne'
        · have ha' : a = 0 := le_antisymm (le_of_not_gt ha') ha0
          refine ⟨ρ + 3 * (η : ℝ) + 1, by positivity, by linarith, ?_⟩
          intro p
          have hp : ‖(T₁ p).symm.toContinuousLinearMap‖ = 0 :=
            le_antisymm (ha' ▸ hbounds.1 p) (norm_nonneg _)
          simp [hp]
      obtain ⟨m, hm, hmx, hmT⟩ := hexpand
      intro p z hz
      exact parameter_graph_stable_orbit_characterization h T₁ T₂ G hzero m ρ hm hρ
        kN η hmx ((hstableStrong hρ₁).le.trans (min_le_right _ _)) hρ₁
        hmT hbounds.2 hη t ht htgraph 1 p z hz


end HolomorphicAnosov
