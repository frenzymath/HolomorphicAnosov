import HolomorphicAnosov.Analysis.ParametricInverseSpatialRegularityG18
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.FiniteSpatialJetCompositionContinuous
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetNorm
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Topology.ProjectedNativeFamilyBoxG4
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ManifoldInverse
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import HolomorphicAnosov.Geometry.AmbientOpNormEventuallyLt
import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import Mathlib.Topology.Semicontinuity.Basic
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSmoothInverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Convex.PathConnected
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundleLocalRankG10
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergySplitNormContinuityG10
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergyUniformComparisonG10
import HolomorphicAnosov.Dynamics.Anosov.ExplicitMetricUniformComparisonG10
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergyContinuousRestrictedNorm
import HolomorphicAnosov.Dynamics.Anosov.FiniteEnergySplitNorm
import HolomorphicAnosov.Dynamics.Anosov.NativeFibreChartExpressionTransport
import HolomorphicAnosov.Dynamics.Anosov.NativeFibreIteratedJetTransport
import HolomorphicAnosov.Dynamics.Anosov.FiniteWeightedEnergy
import HolomorphicAnosov.Dynamics.Anosov.FiniteC1NativePlaqueFamily
import HolomorphicAnosov.Dynamics.Anosov.FiniteOrderNativePlaqueCoherence
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphConstruction
import HolomorphicAnosov.Paper.HPS.LocalStrongGraphs
import HolomorphicAnosov.Geometry.UniformExponentialLift
import HolomorphicAnosov.Dynamics.Anosov.SourceBoundTransportedPlaqueStages
import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataG8
import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataTensorToBundle
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Dynamics.Anosov.VerticalJetTransport
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationGraphHelpers
universe u v
noncomputable section
set_option linter.style.haveILetI false
open Set Filter _root_.Topology
open scoped ContDiff Manifold _root_.Topology Bundle Uniformity
namespace HolomorphicAnosov.HPS

/-- The maximum gauge on a direct sum is the maximum of its restrictions.
Only definiteness at zero and nonnegativity of the full gauge are needed;
the two preliminary energy functions need not be separately normalized.

Source: the finite-energy adapted splitting in HPS Chapter 5. Evaluate the
splitting at (v,w), (v,0), (0,w), and (0,0). The last evaluation bounds both
zero values by zero. Nonnegativity bounds them by the value at (v,w), so
expanding the two restricted gauges gives the same maximum. -/
theorem split_gauge_max_restrictions
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P Q : Submodule ℝ V) (hPQ : IsCompl P Q)
    (ν νP νQ : V → ℝ) (hν : ∀ v, 0 ≤ ν v) (hν0 : ν 0 = 0)
    (hsplit : ∀ v, ν v =
      let z := (Submodule.prodEquivOfIsCompl P Q hPQ).symm v
      max (νP z.1) (νQ z.2))
    (v : P) (w : Q) : ν (v.val + w.val) = max (ν v.val) (ν w.val) := by
  let e := Submodule.prodEquivOfIsCompl P Q hPQ
  have hvw : e (v, w) = v.val + w.val := rfl
  have hv : e (v, 0) = v.val := by simp [e]
  have hw : e (0, w) = w.val := by simp [e]
  have he (a : P) (b : Q) : ν (e (a, b)) = max (νP a) (νQ b) := by
    rw [hsplit]
    change max (νP (e.symm (e (a, b))).1) (νQ (e.symm (e (a, b))).2) = _
    rw [e.symm_apply_apply]
  have hz := he 0 0
  rw [show e (0, 0) = 0 from map_zero e, hν0] at hz
  simp only [Submodule.coe_zero] at hz
  have hv' := he v 0
  have hw' := he 0 w
  rw [hv] at hv'
  rw [hw] at hw'
  rw [← hvw, he, hv', hw']
  have hn : 0 ≤ max (νP v) (νQ w) := by rw [← he]; exact hν _
  exact le_antisymm
    (max_le (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _)))
    (max_le
      (max_le (le_max_left _ _) ((le_max_right _ _).trans (hz ▸ hn)))
      (max_le ((le_max_left _ _).trans (hz ▸ hn)) (le_max_right _ _)))

end HolomorphicAnosov.HPS

/-!
 # Native data for the HPS real Anosov lamination statement

Source: Hirsch--Pugh--Shub, *Invariant Manifolds* (1977), continuous-foliation,
unbranched-lamination and intrinsic-topology conventions, printed pp.115--116; point-foliation
continuation (6B.1)--(6B.4), pp.111--114. These concrete interfaces support the two
existential theorem statements. Published native family, estimate and finite-order
coherence definitions are reused. The proofs construct the intrinsic leaves, smooth
families, ambient boxes, dynamical invariance and distance characterization.
-/

open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open TopologicalSpace Set

namespace HolomorphicAnosov.HPS

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/--
 Concrete existence of a smooth invariant lamination with finite-C¹ and all-finite-order coherent families.

Source: HPS (5.5), (6B.1)--(6B.4) and §7, pp.61--63,111--116. Every carrier, topology, atlas,
immersion and plaque is existential output. Ranks vary by leaf. This differs from
`TransverseContinuousFoliations`: it is one distribution's smooth lamination on an arbitrary real
model, and imposes no global rank pair. The fixed-rank pair interface remains reusable on
individual clopen rank strata.
-/
def HasNativeLamination
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (extra : ∀ {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
      [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
      [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)],
      (F : LeafPartition D ι L r) → SelectedFiniteC1NativePlaqueFamilies F →
        SelectedFiniteOrderNativePlaqueFamilies F → Prop) : Prop :=
  ∃ (ι : Type u) (L : ι → Type u) (r : ι → ℕ) (top : ∀ i, TopologicalSpace (L i)),
    letI := top
    ∃ (charts : ∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)),
      letI := charts
      ∃ (smooth : ∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)),
        letI := smooth
        ∃ F : LeafPartition D ι L r,
          (∃ (β : Type u) (d : β → ℕ) (T : β → Type u)
            (topT : ∀ b, TopologicalSpace (T b)),
            letI := topT
            Nonempty (LaminationBoxes F β d T)) ∧
          Nonempty (LeafDynamicalInvariance F f) ∧
          ∃ families : SelectedFiniteC1NativePlaqueFamilies F,
            ∃ coherent : SelectedFiniteOrderNativePlaqueFamilies F, extra F families coherent

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/--
Manifold chain rule for the linear reparameterization used by the native stable
plaque family.

Source: Mathlib's `mfderiv_comp`, `mfderiv_eq_fderiv`, and the derivative theorem
for continuous linear maps. A continuous linear equivalence is smooth in vector
space charts; its derivative is its underlying continuous linear map. Applying
`mfderiv_comp` to `β ∘ A` and rewriting that derivative yields the asserted
composition. This statement is agent-written as the exact local specialization
needed by the HPS source family, with no transverse differentiability claim.
-/
theorem mfderiv_linear_plaque_reparam
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : V ≃L[ℝ] W) (β : W → M) (v : V)
    (hβ : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) β (A v)) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun w ↦ β (A w)) v =
      (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) β (A v)).comp A.toContinuousLinearMap := by
  have hA : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) A v :=
    A.contDiff.contMDiff.contMDiffAt.mdifferentiableAt (n := (∞ : ℕ∞ω)) (by simp)
  have hd : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) A v = A.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact A.toContinuousLinearMap.hasFDerivAt.fderiv
  change mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (β ∘ A) v = _
  convert (mfderiv_comp v hβ hA).trans (congrArg
      (fun L ↦ (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) β (A v)).comp L) hd) using 1; rfl

/-- The empty ambient manifold has the empty native lamination, with all source
stage data given by empty dependent functions.

Source: the empty-manifold case of the HPS lamination conclusion. Use the
empty ambient type for the leaf and box indices and zero for the ranks. All
charts, families, transport stages, and their obligations are constructed by
empty elimination; the existential package therefore contains actual data. -/
theorem empty_native_lamination_distance [IsEmpty M]
    (D : RealTangentDistribution 𝓘(ℝ, E) M)
    (f g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (distance : M → M → ℝ≥0∞) :
    HasNativeLamination D f
      (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent g distance) := by
  let r : M → ℕ := fun _ ↦ 0
  let L : M → Type u := fun _ ↦ M
  letI : ChartedSpace (Fin 0 → ℝ) M := ChartedSpace.empty _ _
  let charts (i : M) : ChartedSpace (Fin (r i) → ℝ) (L i) := inferInstance
  let smooth (i : M) : IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i) := inferInstance
  let F : LeafPartition D M L r := {
    leaf := fun i ↦ isEmptyElim i
    cover := fun p ↦ isEmptyElim p
    disjoint := fun i ↦ isEmptyElim i }
  let families : SelectedFiniteC1NativePlaqueFamilies F := {
    dimension := fun p ↦ isEmptyElim p
    family := fun p ↦ isEmptyElim p }
  let coherent : SelectedFiniteOrderNativePlaqueFamilies F := {
    dimension := fun _ p ↦ isEmptyElim p
    family := fun _ p ↦ isEmptyElim p
    coherence := fun _ p ↦ isEmptyElim p }
  refine ⟨M, L, r, fun _ ↦ inferInstance, charts, smooth, F, ?_, ?_, families, coherent, ?_⟩
  · refine ⟨M, r, L, fun _ ↦ inferInstance, ⟨?_⟩⟩
    exact {
      boxes := fun b ↦ isEmptyElim b
      cover := fun p ↦ isEmptyElim p
      topology_generated := fun i ↦ isEmptyElim i }
  · exact ⟨{
      permutation := Equiv.refl M
      transport := fun i ↦ isEmptyElim i
      intertwining := fun i ↦ isEmptyElim i }⟩
  · let label : M → M := id
    let sourceDisc : ∀ x, Opens (Fin (r (label x)) → ℝ) := fun x ↦ isEmptyElim x
    let sourceMap : ∀ x, sourceDisc x → M := fun x ↦ isEmptyElim x
    let stages : NativeSourcePlaqueStages (fun i ↦ (F.leaf i).inclusion)
        label g sourceDisc sourceMap := by
      constructor <;> exact fun x ↦ isEmptyElim x
    refine ⟨label, sourceDisc, sourceMap, stages, ?_, ?_, ?_⟩
    · exact ⟨{ label := label, equality := fun x ↦ isEmptyElim x }, rfl⟩
    · exact fun p ↦ isEmptyElim p
    · exact fun _ p ↦ isEmptyElim p


/-- Shrink simultaneous local constraints to an open parameter neighborhood and a ball.

Source: Mathlib `mem_nhds_prod_iff'` and `Metric.mem_nhds_iff`, applied to the
local-domain step in HPS (5.5), pp.61–63. Continuity at the marked point pulls the
strict real bound and the open receiving domain back to neighborhoods. Their
intersection contains a product of open neighborhoods; the metric factor contains
a positive ball. Restricting to that product proves both constraints, without any
assumption about the plaque representative outside its local domain.
DAG node: `topo.exists_local_product_ball_g4`.
-/
theorem exists_local_product_ball_g4
    {A V M : Type*} [TopologicalSpace A] [MetricSpace V] [TopologicalSpace M]
    (a : A) (zero : V) (ν : A × V → ℝ) (P : A × V → M)
    (R : ℝ) (U : Set M)
    (hν : ContinuousAt ν (a, zero)) (hP : ContinuousAt P (a, zero))
    (hR : ν (a, zero) < R)
    (hU : IsOpen U) (hP0 : P (a, zero) ∈ U) :
    ∃ V₀ : Set A, IsOpen V₀ ∧ a ∈ V₀ ∧ ∃ r : ℝ, 0 < r ∧
      ∀ p ∈ V₀, ∀ v ∈ Metric.ball zero r, ν (p, v) < R ∧ P (p, v) ∈ U := by
  have hνO : {z : A × V | ν z < R} ∈ 𝓝 (a, zero) :=
    hν (isOpen_Iio.mem_nhds hR)
  have hPO : P ⁻¹' U ∈ 𝓝 (a, zero) := hP (hU.mem_nhds hP0)
  obtain ⟨V₁, V₂, hV₁, haV₁, hV₂, hzV₂, hprod⟩ :=
    mem_nhds_prod_iff'.mp (inter_mem hνO hPO)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV₂.mem_nhds hzV₂)
  refine ⟨V₁, hV₁, haV₁, r, hr, ?_⟩
  intro p hp v hv
  have hz : (p, v) ∈ V₁ ×ˢ V₂ := ⟨hp, hball hv⟩
  exact ⟨hprod hz |>.1, hprod hz |>.2⟩

/-- Reinterpret joint continuity on a product with a subtype as continuity
on the corresponding product set. This is a domain/coercion adapter.

Source: Mathlib's restriction characterization of ContinuousOn. The map
from the subtype of univ × s to P × s has continuous coordinate projections;
composing it with the given continuous map is the required restriction. -/
lemma continuousOn_univ_prod_of_subtype_g4
    {P V W : Type*} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace W]
    (s : Set V) (f : P × V → W)
    (hf : Continuous (fun z : P × s ↦ f (z.1, z.2.val))) :
    ContinuousOn f (Set.univ ×ˢ s) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let j : (Set.univ ×ˢ s : Set (P × V)) → P × s :=
    fun z ↦ (z.val.1, ⟨z.val.2, z.property.2⟩)
  have hj : Continuous j := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  exact hf.comp hj

set_option maxHeartbeats 1800000 in
set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option backward.isDefEq.respectTransparency true in
/--
 HPS real Anosov global laminations for the supplied Riemannian distance.

Source: Hirsch--Pugh--Shub, *Invariant Manifolds* (1977), (2.8)--(2.9), pp.13--15; (5.1)--(5.5),
pp.53--63; (6.5)--(6.7), pp.80--93; (6B.1)--(6B.4), pp.111--114; §7 pp.115--116; (7.5)--(7.6),
pp.127--129. The detailed source proof is the current DAG node `g9.hps_anosov_global_lamination`.
`IsRiemannianManifold` expresses the given extended Riemannian path distance using its own
already supplied smooth bundle norms. HPS printed p.86 defines the length metric on connected
components; across components the infimum of path lengths is infinity. Thus `EMetricSpace` and
`edist` retain the disconnected source scope without a finite cross-component distance or a
connectedness assumption. The natural statement’s `dist` is read as this extended path distance.
No tensor argument or extra identification with an independent tensor-induced distance is assumed.

Proof: GL1: HPS §5 pp.53,61–62, expanded adaptation to the given splitting. Choose a with λ<a<1
and N≥1 such that Cλ^N<a^N, using geometric decay. On Eˢ define
|v|²_s=Σ_{j=0}^{N−1}a^(−2j)‖D(f^j)v‖², with each norm taken at f^j(x); on Eᵘ use
|w|²_u=Σ_{j=0}^{N−1}a^(−2j)‖D(f^(−j))w‖². These are continuous positive fibre inner products.
Invariance and the chain rule give |Df v|²_s=a²(|v|²_s−‖v‖²+a^(−2N)‖D(f^N)v‖²)≤a²|v|²_s, and the
analogous estimate |Df⁻¹ w|_u≤a|w|_u. On the full tangent space use the product maximum norm of
the two components; the continuous projections for the complementary splitting and compactness
make it uniformly equivalent to the original norm. Thus Df has stable norm≤a<1 and unstable
conorm≥a⁻¹>1 in this auxiliary norm. The original Riemannian metric, given estimates and distance
are not replaced: this norm is used only for constructing uniform graph domains. If a summand has
dimension zero its graph is a point and the corresponding contraction estimate is vacuous. Source
norm construction: HPS (2.8), printed pp.13–14/PDF17–18, including the finite-sum remark on p.14,
and bundle version (2.9), pp.14–15/PDF18–19. This is the existing finite-sum applicability
calculation. Write its one-step contraction bound as theta<1 below. No iterate replaces the
original f.

GL2: HPS first proof of (5.5), printed pp.61–63/PDF65–67, using (5.1)–(5.4), pp.53–61/PDF57–65.
Select the plaque data by this published construction. Apply the exponential/cutoff supplier on
A=M, h=f, T=Df and the GL1 product maximum norm; use the common exponential supplier to retain one
inner agreement domain. The first proof lifts f by H_p(v)=exp_(fp)^(-1)(f(exp_p(v))) and extends
it by averaging with T using a smooth bump on T_M M. Concretely use the already established
smooth-Riemannian squared-norm bump construction G_p=T_p+chi_p(H_p-T_p), with support strictly
inside the H-domain and chi=1 on a smaller common domain; the zero collar makes the patch equal to
T outside that support. Choose its initial first-order error epsilon small enough for the graph
and jet margins in the retained graph suppliers. In particular, for the ACTUAL derivative blocks
of G, alpha_*=sup||(D_vG_11)^(-1)|| is bounded by theta/(1-theta epsilon), and k_*=sup||D_vG_22||
is bounded by theta+epsilon; require BOTH upper bounds<1, as well as the source off-diagonal graph
margins, at this initial choice. These are derivative-block bounds, not an identification with the
fixed T block norms. The actual source cone margins alpha_*^(-1)-3epsilon>1 and k_*+epsilon<1 from
(5.1), pp.59–60, are included in this SAME initial source smallness choice. They concern the
derivative-block constants of this selected G; no fixed-T/core constant is substituted for
alpha_*. No smallness of higher jets is required. The selected G is C-infinity fibrewise: the
fixed smooth local exponential expression, smooth bump and zero collar give every finite-order
fibre derivative, jointly continuous in local frames. Compact frame cores give the corresponding
finite-order uniformity. This is the source smooth-bump construction, not a claim that the old
private cutoff graphs are its exported outputs.

Follow the first proof's parameter section space Z_0(1): centered unit-slope maps over E^u_p, with
weighted metric sup_p sup_(v!=0)||s_p(v)-s'_p(v)||/||v||. The zero family is in the space; its
weighted distances are finite, and the Cauchy argument of (5.2) gives a complete closed carrier.
The image graph transform covers h and is a strict contraction by the estimates of (5.1); the
analogous preimage transform over E^s has the source whole-fibre horizontal fixed-point inverse.
Use the retained parameter graph supplier at rho=1 on THIS selected G and splitting. Its fixed
graph families are Gamma^u_p and Gamma^s_p. The transforms preserve continuous parameter families;
the differentiated closed-jet transform identifies their fibre derivatives and preserves
continuous derivative sections, as in pp.62 and 55–58. Thus the families have the stated
finite-order C^r dependence on fixed local discs. The fixed-point suppliers give existence and
uniqueness on these actual complete metric carriers; no autonomous map G_p:E_p→E_p is substituted
for the moving bundle. Exponentiate the small graph discs in the inner agreement domain to obtain
the SOURCE-SELECTED plaques P^s(p),P^u(p), forward/backward trapped respectively. All subsequent
G, graphs and plaques refer to this choice. The public statement is existential, so no equality
with any superseded private G or old section carrier is needed.

GL3: HPS (5.1) characterization, pp.54,59–60/PDF58,63–64; (5.4), pp.60–61/PDF64–65; and the actual
(5.5) statement/proof, pp.61–62/PDF65–66. The printed inequalities in (5.5) are NONSTRICT: rho>=1
for the unstable branch and rho<=1 for the stable branch. Therefore at rho=1 BOTH source
self-coherence and C^r local characterization apply; the former strict-branch reading and its
auxiliary identification are removed. The word local is essential: bounded distance somewhere on
compact M is not a plaque-membership test. The retained parameter supplier gives coherent forward
or backward G-histories entirely in one small common fibre disc, with norms bounded at rate1.
Choose b_*>0 inside BOTH that local-membership disc and the source-selected exponential/cutoff
agreement disc, and inside the selected plaque radius. In this disc the exact exponential equation
transports these histories to the original f. The source local bounded-orbit characterization
captures their initial points on Gamma^s or Gamma^u; on the graph the strict stable/unstable
graph-return bound q<1 gives contraction. The source proof of self-coherence on p.62 uses this
characterization after recentering at a plaque intersection. Equivalently, the existing
short-plaque-path calculation restricts each intersecting plaque to paths whose f-iterate
endpoints stay in the common domains centered at the intersection point. The rate1 test puts both
restricted pieces on that centered source graph. They have its dimension and are immersions, so
the local inverse theorem makes their images relative open neighborhoods there. Their intersection
is relatively open in each plaque. This is applied only to the actual diffeomorphism and its
inverse, not a disputed general singular endomorphism statement.

Retain the already written tangency calculation for these selected graphs. In their trapped graph
coordinates the forward derivative contracts by q; the graph and exponential first derivatives are
uniformly bounded on the common discs. Every stable plaque tangent vector therefore has forward
derivative bounded by K q^n times its coordinate norm. Its E^u component would grow at least
theta^(-n) under the original invariant splitting, whose projections are uniformly bounded. That
component is zero. Dimensions give tangency exactly E^s at every plaque point. Apply the same
argument to f^(-1) for E^u. Zero-dimensional fibres use the supplier's zero-coordinate case rather
than a minimum over an empty unit sphere.

GL4: HPS (6.1), pp.68–74,94–107/PDF72–78,98–111; (6B.1)–(6B.2), pp.111–113/PDF115–117. Use the
point foliation F_0: its intrinsic manifold V_0 is the disjoint union of singleton points of M.
Each component is a complete, boundaryless zero-manifold; the tangent bundle is zero, the
image/closure is compact M, and f permutes components smoothly. HPS explicitly permits this
nonseparable/disconnected leaf-manifold convention (p.68 examples and p.116), and identifies
normal hyperbolicity of the point foliation with Anosov on p.116. GL1 supplies the normal
stable/unstable splitting for the original f at every finite order. Apply the printed (6.1)
construction to this source datum. Its proof constructs uniform tubular/exponential plaque charts
(pp.94–100), the overflowing image graph transform (pp.101–105), and uses Lipschitz jets,
(6.5)–(6.7), and the Grassmann induction to obtain C^r leaf immersions (pp.105–107). Part(e) is
the strong-family construction already proved in §5, and (6B.4) applies to the selected §5 strong
plaque families themselves. We take these HPS outputs; no old private leaf atlas or cutoff-to-leaf
identification is a premise.

Continue the source plaques by the actual compact-limit argument of (6B.2). Restrict the
exponential graph parametrizations to closed discs lying strictly inside the common embedding
domain. On each closed frame core, compactness and joint continuity of each derivative through
order r give continuity of the family in the C^r supremum topology: use uniform continuity on the
core times the closed disc, for the finitely many derivative orders. Its compact parameter image
is therefore compact in the local C^r embedded-disc topology; the finite union of these images is
precompact. The embedding property holds on the common enlarged open discs because the graph
projection is injective and the exponential chart is an embedding there. This verifies precisely
the finite-r plaque precompactness used by (6B.2). The continuation for different r uses the same
source graph germs, by GL10. If a finite connected union of plaques has been continued and p is a
point on one of them, take approximating connected plaque unions, choose plaques centered at
points converging to p, and use precompactness to extract a convergent centered plaque. This is
exactly the extension step of (6B.2); its limit extends the finite union at p. Cover the boundary
of the initial closed parameter disc by interiors of these centered extensions. It is a compact
boundary covered by relatively open neighborhoods, so choose finitely many extensions. Repeat on
the newly uncovered boundaries, enumerating the finite batches. This produces a countable
connected family {β_j} continuing the initial plaque with no remaining boundary. In the
strong-plaque case self-coherence makes the extension unbranched: intersecting plaque interiors
agree on open pieces, so continuation does not insert a different branch. The source also chooses
approximating plaques p_jn with the property that, for each fixed j, p_jn intersects p_kn only for
k≤K(j), with K(j) independent of n. This bounded overlap property, source (b) on p.113, follows by
choosing extensions only at uncovered boundaries, restricting discs as in source (u) on p.112, and
using the compact family of restricted plaques. It is part of the actual construction; arbitrary
lists of immersions do not have it. The restricted property(u) and bounded-overlap property(b) are
conclusions of this source continuation, not added hypotheses. In the lemma, the approximating
unions are connected in their original intrinsic manifold: a plaque centered at a point tending to
p is appended to that same union, and precompactness extracts its centered limit. The finite-batch
boundary covering and the restricted-disc selection are exactly the mechanism on pp.112–113.
Source §6B completes the resulting leaf immersions; it does not assume the old agent atlas already
complete. Boundary/source-domain guard: the complete BOUNDARYLESS starting input is the point
carrier V_0, not a positive-radius local Wu/Ws disc from (6.1), which can have an outer boundary.
Use the actual (6B.3)/(6B.4) packaging and the (6B.2) strong-plaque boundary-extension/quotient
construction. No open local disc is assumed complete and fed into (6B.1). For point center, weak
and strong stable/unstable dimensions coincide. In (6.1) pp.101–106 the graph return is inverted
only on its restricted X(m-prime epsilon) domain whose image covers X(epsilon), with actual
overflow; no erroneous unstable subset sign from the statement on p.71 is used.

GL5: Apply the following existing quotient-chart argument to the SOURCE-SELECTED strong plaque
continuation of GL4. HPS §6B proof (6B.1), p.113, and Corollary (6B.4), p.114. Form the disjoint
union of the open parameter discs indexed by j. Identify (j,u) and (k,v) when β_j(u)=β_k(v) and
the branches are joined by the overlapping approximating plaques; use the equivalence generated by
these identifications. Let B_x be the connected continuation component. For each point u in the
j-th disc let U_jk be the open overlap domain with the k-th disc. There are only finitely many
relevant k, by source property (b), so U_j(u), the intersection of the U_jk containing u, is an
open neighborhood of u. The maps u′↦[(j,u′)] on these neighborhoods are the source quotient
charts. Unbranchedness makes their transfers β_k⁻¹∘β_j well defined and C^r on the open overlaps;
the quotient construction gives inverses onto their chart images and makes those images open. The
maps b_x([(j,u)])=β_j(u) agree on overlaps, so define a continuous C^r immersion. In the strong
self-coherent case, equal ambient image points are identified: the centered plaque at their common
image agrees locally with both representatives, and the corresponding overlap identifications join
the two representatives. This is the injectivity conclusion of (6B.4), not injectivity inferred
from merely local immersions. Its tangent space at every point is Eˢ or Eᵘ, as stated in (6B.4).
The connected glued component is boundaryless because every plaque boundary encountered in
continuation was covered by centered extensions. Source typography guard: the p.113/PDF117 display
prints beta_j(x)=beta_j(y), while its second chart index and transfer are k. Use equality of the
two actual ambient images beta_j(x)=beta_k(y), as the next printed transfer beta_k^(-1) composed
beta_j requires. This is an index typo, not a different equivalence relation.

GL6: The source manifold assertion on HPS p.113 includes the following elementary topology checks.
Each chart domain is an open subset of a finite-dimensional Euclidean space. Only countably many
original discs occur; their open subcharts have a countable refinement obtained from rational
Euclidean balls. The images of these balls form a countable base for the quotient-chart topology,
hence B_x is second countable. For distinct p,q∈B_x, injectivity of b_x gives distinct image
points in the Hausdorff manifold M. Choose disjoint ambient open neighborhoods and pull them back
by the continuous b_x; these separate p and q, hence B_x is Hausdorff. Connectedness follows
because the initial plaque and every subsequent centered extension join through a nonempty open
overlap; each finite continuation union is connected, and their increasing union is connected.
These checks refer to the intrinsic chart topology. They do not identify it with the ambient
subspace topology, and do not require properness of b_x. HPS p.114/PDF118 also proves that the
continued map is a leaf immersion, using compactness of the restricted plaque family for
pullback-Finsler completeness and its finite-order tangent extension. Its common centered inner
plaque charts and uniform metric comparisons are those established in (6.2) and the proof of
(6.7), pp.72–74 and 86. Use the actual uniform estimates (1),(2) in the proof of (6.7), printed
p.86/PDF90: there is xi>0 such that intrinsic distance from a plaque center below xi puts a point
in its centered plaque, and intrinsic and plaque-coordinate distances have uniform two-sided
comparison. The source proves these estimates by the positive boundary-exit length, not by
summability of an arbitrary Cauchy tail. Fix a sufficiently late Cauchy index p so every
subsequent term has intrinsic distance from p below xi and below the threshold for a closed inner
parameter disc. All these terms then lie in the SAME centered inner plaque; their coordinates are
Cauchy by the lower comparison. The compact closed inner disc supplies a limit, and the upper
comparison gives pullback-metric convergence. Centered continuation plaques are available at every
point, so a chart boundary is not an uncovered leaf boundary. This is the compactness step written
tersely on p.114, not completeness of an arbitrary immersed image or ambient subspace topology.
The source convention allows the disjoint union of connected intrinsic components; each component
has the countable Hausdorff manifold topology proved above.

GL7: HPS (6B.3)–(6B.4), printed p.114/PDF118, and (7.5)–(7.6), pp.127–129/PDF131–133. The point
foliation F_0 from GL4 is a C-infinity foliation of all M and has unique path lifting: a C1 path
with zero tangent is contained in its point leaf. The normally hyperbolic source leaf immersions
and the §5 strong plaque continuation therefore give the printed invariant Ws,Wu; (6B.4) gives
injectively immersed strong laminae tangent E^s,E^u. Follow the actual proof of (7.5)(b). For a
short C1 path x_t tangent to Wu, the strong unstable plaque at x_t meets a stable plaque at x_0 in
a unique point y_t; the source local plaque coordinates give a C1 path y_t tangent to F_0. It
stays in its original point leaf, so x_t stays in the original Wu lamina. The stable argument
reverses time. Part(c) supplies unique path lifting for F_0, and (7.6) concludes that Ws and Wu
are unbranched C1 laminations, with unique path lifting. The source construction identifies their
compatible continuation germs; it is not a conclusion about an arbitrary unrelated graph family.

Use the source definitions exactly: on p.115/PDF119 a continuous foliation is a partition into
connected injectively immersed leaves with ambient C0 product boxes, and an unbranched C^r
lamination is that continuous foliation with coherently immersed C^r leaves. Thus the actual
unbranched-lamination output supplies the ambient boxes; no transversely smooth foliation is
asserted. On p.116/PDF120 its leaf manifold has the intrinsic NON-induced topology. The source
invariance carries the lamina through x onto the one through fx. The original f is used throughout
GL1–GL3, so no iterate-to-original comparison is needed. The eventual-normal-hyperbolicity
argument on p.52/PDF56 is consistent with this scope but is not a hidden hypothesis or alternate
construction.

The ambient boxes are constructed from the selected family as follows. Fix the ordinary ambient
chart at x, subtract its value at x, and compose with the inverse of the complementary stable and
unstable linear frame. Project its value on each nearby stable plaque onto the stable factor.
The derivative of this projected map at the central zero parameter is the identity, by the
centered plaque derivative and the manifold chart chain rule. Joint continuity of the family
and its spatial derivative gives parameter inverse charts on one common stable ball. Restrict
to the open invertibility locus; the inverse-function theorem upgrades each inverse to smoothness.
Compose the intrinsic leaf chart with this inverse and take its open image in the intrinsic leaf.
Shrink the center neighborhood so the projected center belongs to the common ball. The inverse
identities now give the exact projection and centering laws of ProjectedNativePlaqueFamily.
Its connected-section uniqueness theorem identifies intersecting charts, and its rectangular
restriction supplies an ambient NativeProductBox. These boxes cover M because the construction
is performed at every x; their open intrinsic plaque charts generate each leaf topology.

GL8: Nested stages and exact asymptotic range, expanded from HPS (5.1)–(5.5) pp.54,59–62 and the
source continuation of §6B. With the forward-trapped open stable plaques of the SOURCE-SELECTED
GL2 family define A_n(x)=f^(−n)(Pˢ(f^n x)). Each A_n contains x, is connected and embedded, and is
open in the intrinsic lamina by the chart/germ construction. Trapping gives A_n⊆A_(n+1). If y∈A_n,
the strict local graph bound after time n gives dist(f^(n+m)y,f^(n+m)x)≤K_y q^m, with a finite K_y
coming from the adapted-to-original coordinate comparison. Hence y is forward asymptotic to x.
Conversely, if dist(f^m y,f^m x)→0, choose n sufficiently large that EVERY subsequent pair lies in
the uniform inner exponential domains and its actual lifted coordinate
v_m=exp_(f^(n+m)x)⁻¹(f^(n+m)y), m≥0, has norm<b_* in the SAME source-selected disc chosen in GL3.
The existing uniform exponential-coordinate and original/adapted norm comparisons allow this
choice from asymptotic closeness alone, before assuming graph membership. On every step the
source-selected exact agreement equation gives G_(f^(n+m)x)(v_m)=v_(m+1). Hence these are the
actual coherent forward coordinates in the moving fibres of the selected G, retained inside both
the parameter local-membership domain and the exponential/cutoff agreement domain. Their norms are
bounded at rate1. Apply the SAME moving-parameter output instantiated in GL3 at
A=M,h=f,r=1,ρ=1,E₁=Eᵘ,E₂=Eˢ; it puts v₀ on the source stable graph constructed in GL2. Its
centered unit slope makes the graph norm equal the stable base-coordinate norm, so that norm
is<b_*<b only AFTER membership has been obtained. Thus f^n y∈Pˢ(f^n x) and y∈A_n. This proves that
the increasing union of the A_n is exactly the forward asymptotic set; no exponential rate was
assumed for the converse. This is the existing original-f asymptotic/coordinate argument, now
bound to the HPS-selected family. All future inner-domain coordinate bounds are obtained BEFORE
graph membership. Rate1 capture is the literal nonstrict (5.5) branch, not an assumed exponential
decay of a merely asymptotic orbit. The forward-trapped plaques and their graph membership radius
come from the source strong local graphs on one smaller common disc. For the unstable statement
repeat with f^(-1) and the source backward-trapped family.

GL9: The asymptotic union is the whole continued lamina, not merely an immersed subset of it.
Every A_n lies in the lamina by f-invariance from GL7. If y belongs to Bˢ_x, connectedness and the
manifold charts give a finite piecewise C¹ intrinsic path from x to y. Its image γ has tangent in
Eˢ everywhere, and has finite length ℓ(γ) in the original Riemannian metric. The original
hypothesis and chain rule bound the length of f^m∘γ by Cλ^mℓ(γ). Ambient endpoint distance is at
most that length, so dist(f^m y,f^m x)→0. GL8 then puts y in some A_n. Consequently the intrinsic
lamina is the increasing union of these open embedded stages; their chart topology is its original
intrinsic topology. Apply exactly the same argument to f⁻¹ and Eᵘ to obtain Bᵘ_x and the stages
f^n(Pᵘ(f^(−n)x)). The zero-dimensional case gives singleton leaves and requires no positive path
length. Empty M gives an empty lamination and all point-indexed conclusions are vacuous. Here
B^s_x and B^u_x are the HPS-created unbranched laminae from GL7. No private old B_x is identified
with them. For an intrinsic open set O and y in O, the increasing union places y in some A_n; A_n
is itself intrinsically open, so O intersect A_n contains a transported plaque neighborhood of y.
Conversely every such transported plaque neighborhood is intrinsically open. This gives the stated
intrinsic topology, using the existing manifold charts rather than the ambient subspace topology.
On disconnected M, the continuous splitting has only finitely many rank pairs on compact M; their
clopen strata are f-invariant by Df. The construction is applied on each such compact stratum and
assembled, without adding a constant-rank or connectedness hypothesis.

GL10: HPS (5.1), pp.54–58/PDF58–62; (5.4), pp.60–61/PDF64–65; first proof of (5.5),
pp.61–63/PDF65–67; and the written uniform regularity proof (6.5)–(6.7), pp.80–93/PDF84–97.
Printed (5.4) explicitly permits 1<=r<=infinity. Retain the single source-selected smooth G from
GL2. The actual derivative-block constants alpha_* and k_* have BOTH been made<1 at the initial
first-order choice; hence k_* alpha_*^j<1 and alpha_* k_*^j<1 for every positive j. These are
precisely the all-order strong graph/jet domination inequalities used in (5.1)/(5.4), not an
assertion that fixed T norms equal the actual derivative norms. Higher derivatives need only exist
with the source finite-order continuity/uniformity; they need not be small.

For each finite r, follow the SAME source weighted graph transform and its
differentiable-jet/continuous derivative-section proof. Its C0 fixed section is unique on the
fixed complete centered unit-slope carrier, so the higher-regularity output is the already
selected graph, not a graph on an independently selected global cutoff. The local uniqueness in
(5.4) likewise identifies restrictions of the strong germs. For each finite r, the parameter
version on p.62 gives C^r continuity on common local discs at that order, so the compact
plaque-family/precompactness argument of GL4 applies for that r. Local discs/coordinate charts may
be restricted at a given order; no common lower radius for ALL orders is required. In the
leaf-immersion proof, (6.7) constructs the uniform connection and slope carrier, obtains the
differentiable fixed jets, locates the tangent graph section and inducts on r (pp.85–93); (6.6)
then upgrades the source immersion through the Grassmann construction (pp.83–84), as used in (6.1)
pp.105–107. This is the published regularity mechanism, replacing the old
suspension/section-superposition/Pötzsche/Wells route.

The continuation uses the same unbranched source germs and has the intrinsic topology already
fixed in GL5–GL9. Every finite-order chart transfer is the source plaque inverse composed with a
source plaque chart; its inverse has that regularity on the open overlap. Thus the same connected
intrinsic laminae are smooth, injectively immersed and tangent to the original splitting. The
fixed source G and its fixed C0 graph are unchanged across orders. The source
C-infinity/local-germ argument does not interchange order-dependent cutoffs or assume an all-order
common chart radius. HPS p.128/PDF132 explicitly states that every submanifold tangent to the
source uniquely integrable lamination field lies in a leaf; (7.5)/(7.6) and the local strong-germ
uniqueness therefore bind the finite-order source immersions to the same C1 intrinsic leaves. At
each point their local source plaque charts are the same germs, so the fixed intrinsic topology
receives all finite-order regularity. No arbitrary C1 reparameterization or transverse smoothing
is used. On a stratum where E^s has rank zero the stable plaques and leaves are points; where E^u
has rank zero the unstable plaques and leaves are points; on empty M the lamination is empty and
all point-indexed conclusions are vacuous.
-/
theorem anosov_global_lamination_distance
    [FiniteDimensional ℝ E] (X : Type u) [EMetricSpace X] [CompactSpace X]
    [SecondCountableTopology X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsRiemannianManifold 𝓘(ℝ, E) X]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X X ∞)
    (S : InvariantRealTangentSplitting f) (h : BundleAnosovBounds f S) :
    HasNativeLamination S.stable.toDistribution f
      (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent f edist) ∧
    HasNativeLamination S.unstable.toDistribution f
      (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent f.symm edist) := by
  have hforward (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X X ∞)
      (S : InvariantRealTangentSplitting f) (h : BundleAnosovBounds f S) :
      HasNativeLamination S.stable.toDistribution f
        (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent f edist) := by
    rcases isEmpty_or_nonempty X with hempty | hnonempty
    · exact empty_native_lamination_distance _ f f edist
    obtain ⟨θ, K, νs, νu, ν, hθ, hθ1, hK, hνscontinuous, hνucontinuous,
      hνsupper, hνuupper, hνsplit, hνzero, hνadd, hνsmul, hνlower,
      hνstable_contract, hνunstable_contract, hνcontinuous⟩ :=
      continuous_anosov_finite_energy_split_norm X f S h
    have hνnonneg (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : 0 ≤ ν x v := by
      linarith [norm_nonneg v, hνlower x v]
    have hνdef (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ν x v = 0 ↔ v = 0 := by
      constructor
      · intro hv
        apply norm_eq_zero.mp
        simpa [hv] using hνlower x v
      · rintro rfl
        exact hνzero x
    let nν := continuousRestrictedTangentNorm_univ ν hνnonneg hνdef hνadd hνsmul hνcontinuous
    obtain ⟨gMetric, hm, hM, hmpos, hMpos, hνlowerMetric, hνupperMetric⟩ :=
      exists_metric_uniform_comparison X nν
    let F : ↥(Set.univ : Set X) → ↥(Set.univ : Set X) := fun p ↦ ⟨f p, trivial⟩
    let G : ↥(Set.univ : Set X) → ↥(Set.univ : Set X) := fun p ↦ ⟨f.symm p, trivial⟩
    let hbase : (Set.univ : Set X) ≃ₜ (Set.univ : Set X) := {
      toFun := F
      invFun := G
      left_inv := fun p ↦ Subtype.ext (f.symm_apply_apply p)
      right_inv := fun p ↦ Subtype.ext (f.apply_symm_apply p)
      continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk (fun _ ↦ trivial)
      continuous_invFun := (f.symm.continuous.comp continuous_subtype_val).subtype_mk (fun _ ↦ trivial) }
    have hhomeo : IsHomeomorph F := hbase.isHomeomorph
    have hcutoff (ε : ℝ) (hε : 0 < ε) :=
      ExponentialCutoff.exponential_cutoff_extension gMetric univ isCompact_univ f ⊤
        (by simp) f.contMDiff (fun _ _ ↦ trivial) hhomeo nν ε hε
    have hνsubzero (P : Submodule ℝ E) (p : X) (v : P) :
        ν p v.val = 0 ↔ v = 0 := by
      constructor
      · intro hv
        apply Subtype.ext
        exact (hνdef p v.val).mp hv
      · rintro rfl
        exact hνzero p
    have hcU : letI := subbundleSigmaTopology S.unstable
        Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦ ν z.1 z.2.val) := by
      letI := subbundleSigmaTopology S.unstable
      exact hνcontinuous.comp (show Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) from continuous_induced_dom)
    have hcS : letI := subbundleSigmaTopology S.stable
        Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦ ν z.1 z.2.val) := by
      letI := subbundleSigmaTopology S.stable
      exact hνcontinuous.comp (show Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) from continuous_induced_dom)
    let gu (p : X) := finiteDimensionalRenorm (fun v : S.unstable.toDistribution p ↦ ν p v.val)
      (fun v ↦ hνnonneg p v.val) (fun v ↦ hνsubzero _ p v)
      (fun v w ↦ hνadd p v.val w.val) (fun c v ↦ hνsmul p c v.val)
    letI (p : X) : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
      (gu p).toSeminormedAddCommGroup
    let su (p : X) : @NormedSpace ℝ (S.unstable.toDistribution p) _
        (gu p).toSeminormedAddCommGroup :=
      @NormedSpace.mk ℝ (S.unstable.toDistribution p) _ (gu p).toSeminormedAddCommGroup
        (Submodule.module (S.unstable.toDistribution p)) (fun c v ↦ (hνsmul p c v.val).le)
    let gs (p : X) := finiteDimensionalRenorm (fun v : S.stable.toDistribution p ↦ ν p v.val)
      (fun v ↦ hνnonneg p v.val) (fun v ↦ hνsubzero _ p v)
      (fun v w ↦ hνadd p v.val w.val) (fun c v ↦ hνsmul p c v.val)
    letI (p : X) : SeminormedAddCommGroup (S.stable.toDistribution p) :=
      (gs p).toSeminormedAddCommGroup
    let ss (p : X) : @NormedSpace ℝ (S.stable.toDistribution p) _
        (gs p).toSeminormedAddCommGroup :=
      @NormedSpace.mk ℝ (S.stable.toDistribution p) _ (gs p).toSeminormedAddCommGroup
        (Submodule.module (S.stable.toDistribution p)) (fun c v ↦ (hνsmul p c v.val).le)
    letI := subbundleSigmaTopology S.unstable
    letI := subbundleSigmaTopology S.stable
    letI := productSigmaTopology (V := fun p ↦ S.unstable.toDistribution p)
      (W := fun p ↦ S.stable.toDistribution p)
    have au : @FiniteRankNormedAtlas X _ (fun p ↦ S.unstable.toDistribution p) gu su _ := adaptedSubbundleFiniteRankNormedAtlas S.unstable (fun p v ↦ ν p v.val)
      (fun p v ↦ hνnonneg p v.val) (fun p v ↦ hνsubzero _ p v)
      (fun p v w ↦ hνadd p v.val w.val) (fun p c v ↦ hνsmul p c v.val) hcU
    have as' : @FiniteRankNormedAtlas X _ (fun p ↦ S.stable.toDistribution p) gs ss _ := adaptedSubbundleFiniteRankNormedAtlas S.stable (fun p v ↦ ν p v.val)
      (fun p v ↦ hνnonneg p v.val) (fun p v ↦ hνsubzero _ p v)
      (fun p v w ↦ hνadd p v.val w.val) (fun p c v ↦ hνsmul p c v.val) hcS
    let splitAtlas := splitFiniteRankNormedAtlas au as'
    have hnormU (p : X) (v : S.unstable.toDistribution p) : ‖v‖ = ν p v.val := by rfl
    have hnormS (p : X) (v : S.stable.toDistribution p) : ‖v‖ = ν p v.val := by rfl
    let Tu (p : X) : S.unstable.toDistribution p ≃L[ℝ] S.unstable.toDistribution (f p) :=
      (f.mfderivToContinuousLinearEquiv (by simp) p).ofSubmodules
        (S.unstable.toDistribution p) (S.unstable.toDistribution (f p)) (S.unstable_map p)
    let Ts (p : X) : S.stable.toDistribution p →L[ℝ] S.stable.toDistribution (f p) :=
      ((f.mfderivToContinuousLinearEquiv (by simp) p).ofSubmodules
        (S.stable.toDistribution p) (S.stable.toDistribution (f p)) (S.stable_map p)).toContinuousLinearMap
    have hTs (p : X) : ‖Ts p‖ ≤ θ := by
      apply ContinuousLinearMap.opNorm_le_bound _ hθ.le
      intro v
      rw [hnormS, hnormS]
      exact hνstable_contract p v
    have hTu (p : X) : ‖(Tu p).symm.toContinuousLinearMap‖ ≤ θ := by
      apply ContinuousLinearMap.opNorm_le_bound _ hθ.le
      intro v
      have hinv : ((Tu p).symm v).val = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f p) v.val := by
        apply (f.mfderivToContinuousLinearEquiv (by simp) p).injective
        change (f.mfderivToContinuousLinearEquiv (by simp) p)
          ((f.mfderivToContinuousLinearEquiv (by simp) p).symm v.val) = _
        rw [ContinuousLinearEquiv.apply_symm_apply]
        change v.val = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f p) v.val)
        have hid := derivative_forward_inverse f (f p) v.val
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm (f p))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f p) v.val) = v.val at hid
        rw [f.symm_apply_apply] at hid
        exact hid.symm
      rw [hnormU, hnormU]
      change ν p ((Tu p).symm v).val ≤ θ * ν (f p) v.val
      rw [hinv]
      have hc := hνunstable_contract (f p) v
      change ν (f.symm (f p)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm (f p) v.val) ≤
        θ * ν (f p) v.val at hc
      rw [f.symm_apply_apply] at hc
      exact hc
    have ha : sSup (Set.range (fun p ↦ ‖(Tu p).symm.toContinuousLinearMap‖)) < 1 :=
      lt_of_le_of_lt (csSup_le (Set.range_nonempty _) (by
        rintro _ ⟨p, rfl⟩
        exact hTu p)) hθ1
    have hk : sSup (Set.range (fun p ↦ ‖Ts p‖)) < 1 :=
      lt_of_le_of_lt (csSup_le (Set.range_nonempty _) (by
        rintro _ ⟨p, rfl⟩
        exact hTs p)) hθ1
    have hTuc : Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦
        (⟨f z.1, Tu z.1 z.2⟩ : Sigma fun p ↦ S.unstable.toDistribution p)) := by
      apply continuous_induced_rng.mpr
      exact (f.contMDiff.continuous_tangentMap (by simp)).comp
        (show Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦
          (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) from continuous_induced_dom)
    have hTsc : Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
        (⟨f z.1, Ts z.1 z.2⟩ : Sigma fun p ↦ S.stable.toDistribution p)) := by
      apply continuous_induced_rng.mpr
      exact (f.contMDiff.continuous_tangentMap (by simp)).comp
        (show Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
          (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) from continuous_induced_dom)
    have hTc : Continuous (fun z : Sigma fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p ↦
        (⟨f z.1, (Tu z.1 z.2.1, Ts z.1 z.2.2)⟩ : Sigma fun p ↦
          S.unstable.toDistribution p × S.stable.toDistribution p)) := by
      have hpair : Continuous (fun z : Sigma fun p ↦
          S.unstable.toDistribution p × S.stable.toDistribution p ↦
          ((⟨z.1, z.2.1⟩ : Sigma fun p ↦ S.unstable.toDistribution p),
            (⟨z.1, z.2.2⟩ : Sigma fun p ↦ S.stable.toDistribution p))) := continuous_induced_dom
      exact continuous_induced_rng.mpr ((hTuc.comp hpair.fst).prodMk (hTsc.comp hpair.snd))
    obtain ⟨εGraph, hεGraph, hgraphSupplier⟩ := parameter_graph_construction 1 le_rfl
      splitAtlas f.toHomeomorph Tu Ts hTc 1 zero_lt_one
        (by set_option backward.isDefEq.respectTransparency false in simpa using ha) hk
    let merge (p : X) :
        (S.unstable.toDistribution p × S.stable.toDistribution p) ≃L[ℝ]
          TangentSpace 𝓘(ℝ, E) p :=
      (Submodule.prodEquivOfIsCompl (S.unstable.toDistribution p)
        (S.stable.toDistribution p) (S.isCompl p).symm).toContinuousLinearEquiv
    have hmerge : Continuous (fun z : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p) ↦
        (⟨z.1, merge z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) X)) := by
      have hpair : Continuous (fun z : Sigma (fun p ↦
          S.unstable.toDistribution p × S.stable.toDistribution p) ↦
          ((⟨z.1, z.2.1⟩ : Sigma fun p ↦ S.unstable.toDistribution p),
            (⟨z.1, z.2.2⟩ : Sigma fun p ↦ S.stable.toDistribution p))) := continuous_induced_dom
      have hiU : Continuous (fun z : Sigma fun p ↦ S.unstable.toDistribution p ↦
          (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) := continuous_induced_dom
      have hiS : Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
          (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) := continuous_induced_dom
      apply continuous_iff_continuousAt.mpr
      intro z
      have hu := (FiberBundle.continuousAt_totalSpace E _).mp ((hiU.comp hpair.fst).continuousAt (x := z))
      have hs := (FiberBundle.continuousAt_totalSpace E _).mp ((hiS.comp hpair.snd).continuousAt (x := z))
      apply (FiberBundle.continuousAt_totalSpace E _).mpr
      refine ⟨hu.1, ?_⟩
      apply (hu.2.add hs.2).congr_of_eventuallyEq
      have hb := (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp
        (hiU.comp hpair.fst)
      filter_upwards [hb.continuousAt.preimage_mem_nhds
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1))] with w hw
      change ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1)
        ⟨w.1, merge w.1 w.2⟩).2 = _
      change ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1)
        ⟨w.1, w.2.1.val + w.2.2.val⟩).2 = _
      have hlin := congrArg (fun l : TangentSpace 𝓘(ℝ, E) w.1 → E ↦
        l (w.2.1.val + w.2.2.val) = l w.2.1.val + l w.2.2.val)
        (Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ)
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.1) hw)
      exact hlin.mp (map_add _ _ _)
    have hsplitContinuous : Continuous (fun z : TangentBundle 𝓘(ℝ, E) X ↦
        (⟨z.proj, (merge z.proj).symm z.snd⟩ : Sigma (fun p ↦
          S.unstable.toDistribution p × S.stable.toDistribution p))) := by
      apply continuous_induced_rng.mpr
      apply Continuous.prodMk
      · apply continuous_induced_rng.mpr
        exact NativeSplittingPreparation.continuous_native_projection
          (I := 𝓘(ℝ, E)) S.unstable S.stable (fun p ↦ (S.isCompl p).symm)
      · apply continuous_induced_rng.mpr
        convert NativeSplittingPreparation.continuous_native_projection
          (I := 𝓘(ℝ, E)) S.stable S.unstable S.isCompl using 1
        funext z
        change (⟨z.proj, (((Submodule.prodEquivOfIsCompl
          (S.unstable.toDistribution z.proj) (S.stable.toDistribution z.proj)
            (S.isCompl z.proj).symm).symm z.snd).2 : TangentSpace 𝓘(ℝ, E) z.proj)⟩ :
            TangentBundle 𝓘(ℝ, E) X) = _
        rw [Submodule.prodEquivOfIsCompl_symm_apply]
        rfl
    have hνmerge (p : X) (v : S.unstable.toDistribution p × S.stable.toDistribution p) :
        ν p (merge p v) = max (ν p v.1.val) (ν p v.2.val) := by
      change ν p (v.1.val + v.2.val) = _
      rw [add_comm]
      exact (split_gauge_max_restrictions (S.stable.toDistribution p)
        (S.unstable.toDistribution p) (S.isCompl p) (ν p) (νs p) (νu p)
        (hνnonneg p) (hνzero p) (hνsplit p) v.2 v.1).trans (max_comm _ _)
    obtain ⟨εJet, hεJet, hjetThreshold⟩ := parameter_graph_contraction_threshold
      θ θ 1 hθ.le hθ.le zero_lt_one (by simpa using hθ1) hθ1
    let ε := min (min (εGraph / 2) (εJet / 2)) ((1 - θ) / 4)
    have hεpos : 0 < ε := lt_min (lt_min (half_pos hεGraph) (half_pos hεJet)) (by linarith)
    have hεgraph : ε < εGraph :=
      ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hεGraph)
    have hεjet : ε < εJet :=
      ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hεJet)
    have hεrate : θ + ε < 1 := by
      have he : ε ≤ (1 - θ) / 4 := min_le_right _ _
      linarith
    obtain ⟨ρ, R, δ, b, logarithm, hρ, hR, hRρ, hδ, hδR, hb,
      hExpLog, hExtension, hAgreement⟩ := hcutoff ε hεpos
    let extension := ExponentialCutoff.extension Set.univ f gMetric
      (fun p ↦ ExponentialLift.centeredLift gMetric f logarithm p) R δ
    let G (p : X) (v : S.unstable.toDistribution p × S.stable.toDistribution p) :
        S.unstable.toDistribution (f p) × S.stable.toDistribution (f p) :=
      (merge (f p)).symm (extension ⟨p, mem_univ p⟩ (merge p v))
    have hextensionZero (p : (Set.univ : Set X)) : extension p 0 = 0 :=
      hExtension.2.2.1 p
    have hGzero (p : X) : G p 0 = 0 := by
      have hm : merge p (0 : S.unstable.toDistribution p × S.stable.toDistribution p) = 0 :=
        (merge p).map_zero
      have h1 : extension ⟨p, mem_univ p⟩ (merge p 0) = 0 :=
        (congrArg (extension ⟨p, mem_univ p⟩) hm).trans (hextensionZero ⟨p, mem_univ p⟩)
      have h2 : (merge (f p)).symm (extension ⟨p, mem_univ p⟩ (merge p 0)) =
          (merge (f p)).symm 0 := congrArg (merge (f p)).symm h1
      exact h2.trans (merge (f p)).symm.map_zero
    have hmergeDerivative (p : X)
        (v : S.unstable.toDistribution p × S.stable.toDistribution p) :
        merge (f p) (Tu p v.1, Ts p v.2) =
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (merge p v) := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p v.1.val +
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p v.2.val =
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (v.1.val + v.2.val)
      exact (map_add _ _ _).symm
    have hGerror (p : X)
        (v w : S.unstable.toDistribution p × S.stable.toDistribution p) :
        ν (f p) (merge (f p)
          ((G p v - (Tu p v.1, Ts p v.2)) -
            (G p w - (Tu p w.1, Ts p w.2)))) ≤
          ε * ν p (merge p (v - w)) := by
      have he := hExtension.2.2.2.2.1 ⟨p, mem_univ p⟩ (merge p v) (merge p w)
      change ν (f p)
        ((extension ⟨p, mem_univ p⟩ (merge p v) -
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (merge p v)) -
         (extension ⟨p, mem_univ p⟩ (merge p w) -
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (merge p w))) ≤
            ε * ν p (merge p v - merge p w) at he
      simpa only [map_sub, hmergeDerivative, G,
        ContinuousLinearEquiv.apply_symm_apply] using he
    let η : NNReal := ⟨ε, hεpos.le⟩
    have hηsmall : (η : ℝ) < εGraph := hεgraph
    let splitGroups (p : X) : NormedAddCommGroup
        (S.unstable.toDistribution p × S.stable.toDistribution p) := by
      letI := gu p
      letI := gs p
      exact inferInstance
    let splitSpaces (p : X) : @NormedSpace ℝ
        (S.unstable.toDistribution p × S.stable.toDistribution p) _
        (splitGroups p).toSeminormedAddCommGroup := by
      letI := gu p
      letI := gs p
      letI : SeminormedAddCommGroup (S.unstable.toDistribution p) :=
        (gu p).toSeminormedAddCommGroup
      letI : SeminormedAddCommGroup (S.stable.toDistribution p) :=
        (gs p).toSeminormedAddCommGroup
      letI := su p
      letI := ss p
      exact inferInstance
    have hGlipschitz (p : X) := @lipschitz_of_gauge_bound
      (S.unstable.toDistribution p × S.stable.toDistribution p)
      (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p))
      (splitGroups p) (splitGroups (f p))
      (fun v ↦ ν p (merge p v)) (fun v ↦ ν (f p) (merge (f p) v))
      (by intro v; exact hνmerge p v)
      (by intro v; exact hνmerge (f p) v)
      (fun v ↦ G p v - (Tu p v.1, Ts p v.2)) η (hGerror p)
    have hExtensionDeriv (p : X) : HasFDerivAt
        (extension ⟨p, mem_univ p⟩)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p) 0 := by
      exact hExtension.2.2.2.1 ⟨p, mem_univ p⟩
    have hGderiv (p : X) := @derivative_conjugate
      (S.unstable.toDistribution p × S.stable.toDistribution p)
      (S.unstable.toDistribution (f p) × S.stable.toDistribution (f p)) E
      (splitGroups p) (splitSpaces p) (splitGroups (f p)) (splitSpaces (f p)) _ _
      (merge p) (merge (f p)) (extension ⟨p, mem_univ p⟩)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p)
      ((Tu p).toContinuousLinearMap.prodMap (Ts p)) (hmergeDerivative p) (hExtensionDeriv p)
    have hGreg (r : ℕ) := @nativeJointFiberContDiff E _ _ _ X _ _ _ _
      (fun p ↦ S.unstable.toDistribution p × S.stable.toDistribution p)
      splitGroups splitSpaces _ splitAtlas.total f f.continuous merge hmerge hsplitContinuous
      (fun p ↦ extension ⟨p, mem_univ p⟩) hExtension.2.1 r
    obtain ⟨unstableGraph, stableGraph, hGraphCentered, hUnstableInvariant,
      hStableInvariant, hUnstableC1, hStableC1, hGraphTangent,
      hUnstableCharacterization, hStableCharacterization⟩ :=
        hgraphSupplier G (hGreg 1) hGzero (fun p ↦ (hGderiv p).fderiv)
          ⟨η, hηsmall, hGlipschitz⟩
    have hStableNorm := fun p ↦ @stable_graph_image_norm
      (S.unstable.toDistribution p) (S.stable.toDistribution p)
      (S.unstable.toDistribution (f p)) (S.stable.toDistribution (f p))
      (gu p) (su p) (gs p) (ss p)
      (gu (f p)) (su (f p)) (gs (f p)) (ss (f p))
      (Tu p).toContinuousLinearMap (Ts p) (G p) (stableGraph p) (stableGraph (f p))
      (hGraphCentered p).2.2.2 (hGraphCentered p).2.1
      (hGraphCentered (f p)).2.2.2 (hGraphCentered (f p)).2.1
      (fun y ↦ by
        set_option backward.isDefEq.respectTransparency false in
        have hy : G p (stableGraph p y, y) ∈
            Set.range (fun v ↦ (stableGraph (f p) v, v)) := by
          change (stableGraph p y, y) ∈ G p ⁻¹'
            Set.range (fun v ↦ (stableGraph (f.toHomeomorph p) v, v))
          rw [hStableInvariant p]
          exact ⟨y, rfl⟩
        obtain ⟨v, hv⟩ := hy
        rw [← hv])
      (hGzero p) η (hGlipschitz p) θ (hTs p)
    have hθeps : θ * (η : ℝ) < 1 := by
      change θ * ε < 1
      have he : ε < 1 := by linarith [hεrate, hθ]
      nlinarith [hθ1]
    have hStableGauge (p : X) (y : S.stable.toDistribution p) :
        ν p (merge p (stableGraph p y, y)) = ν p y.val := by
      rw [hνmerge]
      exact @graph_norm (S.unstable.toDistribution p) (S.stable.toDistribution p)
        (gu p) (gs p) (stableGraph p)
        (hGraphCentered p).2.2.2 (hGraphCentered p).2.1 y
    obtain ⟨localLog, ρLog, logDomain, hρLog, hLogDiagonal, hLogInverse, hLogImage, hLogDomain, hLogSmooth, hLocalLog⟩ :=
      uniform_exponential_logarithm_small gMetric ν hνcontinuous hνzero
    let exponentialChart (p : X) := exponential_fibre_chart gMetric p ρLog logDomain
      (localLog p) (hLogInverse p) (hLogImage p) (hLogDomain p) (hLogSmooth p)
    let plaqueRadius := min b (hm * min ρ ρLog) / 2
    have hPlaqueRadius : 0 < plaqueRadius :=
      half_pos (lt_min hb (mul_pos hmpos (lt_min hρ hρLog)))
    have hPlaqueAgreement : plaqueRadius ≤ b :=
      (half_le_self (le_of_lt (lt_min hb (mul_pos hmpos (lt_min hρ hρLog))))).trans (min_le_left _ _)
    have hPlaqueInjective : plaqueRadius < hm * ρ :=
      (half_lt_self (lt_min hb (mul_pos hmpos (lt_min hρ hρLog)))).trans_le
        ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hmpos.le))
    have hPlaqueLogRadius : plaqueRadius < hm * ρLog :=
      (half_lt_self (lt_min hb (mul_pos hmpos (lt_min hρ hρLog)))).trans_le
        ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hmpos.le))
    have hSmallMetric (p : X) (v : TangentSpace 𝓘(ℝ, E) p)
        (hv : ν p v < plaqueRadius) : ExponentialLift.metricNorm gMetric p v < ρ := by
      have hmν := hνlowerMetric ⟨p, mem_univ p⟩ v
      change hm * ExponentialLift.metricNorm gMetric p v ≤ ν p v at hmν
      exact (mul_lt_mul_iff_right₀ hmpos).mp (hmν.trans_lt (hv.trans hPlaqueInjective))
    have hSmallLogMetric (p : X) (v : TangentSpace 𝓘(ℝ, E) p)
        (hv : ν p v < plaqueRadius) : ExponentialLift.metricNorm gMetric p v < ρLog := by
      have hmν := hνlowerMetric ⟨p, mem_univ p⟩ v
      change hm * ExponentialLift.metricNorm gMetric p v ≤ ν p v at hmν
      exact (mul_lt_mul_iff_right₀ hmpos).mp (hmν.trans_lt (hv.trans hPlaqueLogRadius))
    let stablePlaque (p : X) (y : S.stable.toDistribution p) :=
      ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p y, y))
    have hStablePlaqueZero (p : X) : stablePlaque p 0 = p := by
      simp only [stablePlaque, (hGraphCentered p).2.1, ← Prod.zero_eq_mk, map_zero]
      exact (riemannianExponential_zero gMetric p).2
    have hStableTrap (p : X) (y : S.stable.toDistribution p)
        (hy : ν p y.val < plaqueRadius) :
        ∃ y' : S.stable.toDistribution (f p),
          ν (f p) y'.val ≤ (θ + ε) * ν p y.val ∧
          ν (f p) y'.val < plaqueRadius ∧
          f (stablePlaque p y) = stablePlaque (f p) y' := by
      have hygraph : G p (stableGraph p y, y) ∈
          Set.range (fun v ↦ (stableGraph (f.toHomeomorph p) v, v)) := by
        set_option backward.isDefEq.respectTransparency false in
        change (stableGraph p y, y) ∈ G p ⁻¹'
          Set.range (fun v ↦ (stableGraph (f.toHomeomorph p) v, v))
        rw [hStableInvariant p]
        exact ⟨y, rfl⟩
      obtain ⟨y', hy'⟩ := hygraph
      have hnorm := hStableNorm p y
      have hgauge : ν (f p) y'.val ≤ (θ + ε) * ν p y.val := by
        rw [← hy'] at hnorm
        have hsrc := @graph_norm (S.unstable.toDistribution p) (S.stable.toDistribution p)
          (gu p) (gs p) (stableGraph p)
          (hGraphCentered p).2.2.2 (hGraphCentered p).2.1 y
        have htgt := @graph_norm (S.unstable.toDistribution (f p)) (S.stable.toDistribution (f p))
          (gu (f p)) (gs (f p)) (stableGraph (f p))
          (hGraphCentered (f p)).2.2.2 (hGraphCentered (f p)).2.1 y'
        change max (ν (f p) (stableGraph (f p) y').val) (ν (f p) y'.val) ≤
          (θ + ε) * max (ν p (stableGraph p y).val) (ν p y.val) at hnorm
        change max (ν p (stableGraph p y).val) (ν p y.val) = ν p y.val at hsrc
        change max (ν (f p) (stableGraph (f p) y').val) (ν (f p) y'.val) =
          ν (f p) y'.val at htgt
        rw [hsrc, htgt] at hnorm
        exact hnorm
      refine ⟨y', hgauge, ?_, ?_⟩
      · exact (hgauge.trans (mul_le_of_le_one_left (hνnonneg p y.val) hεrate.le)).trans_lt hy
      · have hAgree := (hAgreement ⟨p, mem_univ p⟩ (merge p (stableGraph p y, y))
          (by change ν p (merge p (stableGraph p y, y)) ≤ b
              rw [hStableGauge]
              exact hy.le.trans hPlaqueAgreement)).2.2.2.2
        have hmergeEq := congrArg (merge (f p)) hy'
        change merge (f p) (stableGraph (f p) y', y') =
          merge (f p) ((merge (f p)).symm (extension ⟨p, mem_univ p⟩
            (merge p (stableGraph p y, y)))) at hmergeEq
        rw [ContinuousLinearEquiv.apply_symm_apply] at hmergeEq
        change f (ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p y, y))) =
          ExponentialLift.riemannianExp gMetric (f p) (merge (f p) (stableGraph (f p) y', y'))
        rw [hmergeEq]
        exact hAgree.symm
    let StableDisc := Sigma fun p : X ↦
      {y : S.stable.toDistribution p // ν p y.val < plaqueRadius}
    let stableStep (z : StableDisc) : StableDisc :=
      ⟨f z.1, ⟨(hStableTrap z.1 z.2.val z.2.property).choose,
        (hStableTrap z.1 z.2.val z.2.property).choose_spec.2.1⟩⟩
    have hStableUniform (ε' : ENNReal) (hε' : 0 < ε') :
        ∃ N : ℕ, ∀ n ≥ N, ∀ p : X, ∀ y : S.stable.toDistribution p,
          ν p y.val < plaqueRadius → edist ((f : X → X)^[n] p)
            ((f : X → X)^[n] (stablePlaque p y)) < ε' := by
      have hu := exponential_trapped_orbit_uniform gMetric
        (fun z : StableDisc ↦ z.1)
        (fun z ↦ merge z.1 (stableGraph z.1 z.2.val, z.2.val))
        (fun z ↦ ν z.1 z.2.val.val) stableStep f
        (fun _ ↦ rfl)
        (fun z ↦ (hStableTrap z.1 z.2.val z.2.property).choose_spec.2.2.symm)
        hm⁻¹ (θ + ε) (inv_pos.mpr hmpos) (add_nonneg hθ.le hεpos.le) hεrate
        (fun z ↦ show ExponentialLift.metricNorm gMetric z.1
          (merge z.1 (stableGraph z.1 z.2.val, z.2.val)) ≤ hm⁻¹ * ν z.1 z.2.val.val from by
          rw [inv_mul_eq_div]
          apply (le_div_iff₀ hmpos).mpr
          have hh := hνlowerMetric ⟨z.1, mem_univ z.1⟩
            (merge z.1 (stableGraph z.1 z.2.val, z.2.val))
          change hm * ExponentialLift.metricNorm gMetric z.1
            (merge z.1 (stableGraph z.1 z.2.val, z.2.val)) ≤
              ν z.1 (merge z.1 (stableGraph z.1 z.2.val, z.2.val)) at hh
          simpa only [hStableGauge, mul_comm] using hh) (fun z ↦ (hStableTrap z.1 z.2.val z.2.property).choose_spec.1)
        plaqueRadius ε' hε'
      obtain ⟨N, hN⟩ := hu
      exact ⟨N, fun n hn p y hy ↦ hN n hn (⟨p, ⟨y, hy⟩⟩ : StableDisc) hy.le⟩
    have hStableAsymptotic (p : X) (y : S.stable.toDistribution p)
        (hy : ν p y.val < plaqueRadius) :
        Tendsto (fun n ↦ edist ((f : X → X)^[n] p)
          ((f : X → X)^[n] (stablePlaque p y))) atTop (𝓝 0) := by
      apply ENNReal.tendsto_nhds_zero.mpr
      intro ε' hε'
      obtain ⟨N, hN⟩ := hStableUniform ε' hε'
      exact eventually_atTop.mpr ⟨N, fun n hn ↦ (hN n hn p y hy).le⟩
    have hStableGraphContinuous := @jointFiberContDiff_total_continuous X X _ _
      (fun p ↦ S.stable.toDistribution p) (fun p ↦ S.unstable.toDistribution p)
      gs ss gu su _ _ splitAtlas.second splitAtlas.first id continuous_id
      1 stableGraph hStableC1
    have hUnstableGraphContinuous := @jointFiberContDiff_total_continuous X X _ _
      (fun p ↦ S.unstable.toDistribution p) (fun p ↦ S.stable.toDistribution p)
      gu su gs ss _ _ splitAtlas.first splitAtlas.second id continuous_id
      1 unstableGraph hUnstableC1
    obtain ⟨hjetSmall, hjetDen1, hjetDen2, _, _, hjetContract, hjetSlope,
      hjetInverse, _, _, _, hjetStrongImage, hjetStrongPreimage, _⟩ :=
        hjetThreshold ε hεpos.le hεjet
    let θN : NNReal := ⟨θ, hθ.le⟩
    have hGraphsRegular (r : ℕ) (hr : 1 ≤ r) :
        JointFiberContDiff splitAtlas.first splitAtlas.second id r unstableGraph ∧
        JointFiberContDiff splitAtlas.second splitAtlas.first id r stableGraph := by
      have hh := parameter_graph_fixed_graph_regularity r hr 1 splitAtlas f.toHomeomorph
        Tu Ts G (hGreg r) hGzero (fun p ↦ (hGderiv p).fderiv)
        θN θN η hTu hTs hjetSmall hjetContract hjetSlope.le hjetInverse
        (fun h ↦ (hjetStrongImage h).trans_le (min_le_left _ _))
        (fun h ↦ (hjetStrongPreimage h).trans_le (min_le_left _ _))
        hGlipschitz unstableGraph stableGraph
        (fun p ↦ ⟨(hGraphCentered p).1, (hGraphCentered p).2.2.1⟩)
        (fun p ↦ ⟨(hGraphCentered p).2.1, (hGraphCentered p).2.2.2⟩)
        hUnstableGraphContinuous hStableGraphContinuous hUnstableInvariant hStableInvariant
      exact ⟨hh.2.2.1 le_rfl, hh.2.2.2 le_rfl⟩
    have hStableGraphSmooth (p : X) : ContDiff ℝ ∞ (stableGraph p) := by
      apply contDiff_infty.mpr
      intro n
      exact ((hGraphsRegular (n + 1) (by omega)).2.1 p).of_le (by exact_mod_cast Nat.le_succ n)
    have hStablePairContinuous : Continuous (fun z : Sigma (fun p ↦ S.stable.toDistribution p) ↦
        (⟨z.1, (stableGraph z.1 z.2, z.2)⟩ : Sigma (fun p ↦
          S.unstable.toDistribution p × S.stable.toDistribution p))) :=
      continuous_induced_rng.mpr (hStableGraphContinuous.prodMk continuous_id)
    have hStablePlaqueContinuous : ContinuousOn
        (fun z : Sigma (fun p ↦ S.stable.toDistribution p) ↦ stablePlaque z.1 z.2)
        {z | ν z.1 z.2.val < plaqueRadius} := by
      exact (riemannian_exponential_local_addition gMetric).2.2.1.continuousOn.comp
        (hmerge.comp hStablePairContinuous).continuousOn (fun z hz ↦
          (hExpLog z.1 (mem_univ z.1) _
            (hSmallMetric z.1 _ ((hStableGauge z.1 z.2).symm ▸ hz))).1)
    have hStablePlaqueC1 (p : X) :
        letI := gs p
        letI := ss p
        ContMDiffOn 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) 1
          (stablePlaque p) {y | ν p y.val < plaqueRadius} := by
      letI := gs p
      letI := ss p
      letI := gu p
      letI := su p
      have hψ : ContDiff ℝ 1 (fun y : S.stable.toDistribution p ↦
          merge p (stableGraph p y, y)) :=
        (merge p).contDiff.comp ((hStableC1.1 p).prodMk contDiff_id)
      exact exponential_fibreMap_contMDiffOn gMetric p _ 1 (by simp) hψ _
        (fun y hy ↦ (hExpLog p (mem_univ p) _
          (hSmallMetric p _ ((hStableGauge p y).symm ▸ hy))).1)
    have hStablePlaqueSmooth (p : X) :
        letI := gs p
        letI := ss p
        ContMDiffOn 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) ∞
          (stablePlaque p) {y | ν p y.val < plaqueRadius} := by
      letI := gs p
      letI := ss p
      letI := gu p
      letI := su p
      have hψ : ContDiff ℝ ∞ (fun y : S.stable.toDistribution p ↦
          merge p (stableGraph p y, y)) :=
        (merge p).contDiff.comp ((hStableGraphSmooth p).prodMk contDiff_id)
      exact exponential_fibreMap_contMDiffOn gMetric p _ ∞ (by simp) hψ _
        (fun y hy ↦ (hExpLog p (mem_univ p) _
          (hSmallMetric p _ ((hStableGauge p y).symm ▸ hy))).1)
    let stableCoordinate (p q : X) : S.stable.toDistribution p :=
      ((merge p).symm (localLog p q)).2
    let exponentialChartC1 (p : X) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X 1 :=
      { (exponentialChart p).toPartialEquiv with
        open_source := (exponentialChart p).open_source
        open_target := (exponentialChart p).open_target
        contMDiffOn_toFun := (exponentialChart p).contMDiffOn_toFun.of_le (by simp)
        contMDiffOn_invFun := (exponentialChart p).contMDiffOn_invFun.of_le (by simp) }
    let stableModel (p : X) :
        (S.stable.toDistribution p × S.unstable.toDistribution p) ≃L[ℝ] E :=
      ((ContinuousLinearEquiv.prodComm ℝ _ _).trans (merge p)).trans
        (tangentSpaceCastModel 𝓘(ℝ, E) p)
    have hStablePlaqueImmersion (p : X) (y : S.stable.toDistribution p)
        (hy : ν p y.val < plaqueRadius) :
        letI := gs p
        letI := ss p
        Manifold.IsImmersionAt 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) 1 (stablePlaque p) y := by
      letI := gs p
      letI := ss p
      letI := gu p
      letI := su p
      have hsource : stableModel p (y, stableGraph p y) ∈ (exponentialChartC1 p).source := by
        change ExponentialLift.metricNorm gMetric p
          ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm
            ((tangentSpaceCastModel 𝓘(ℝ, E) p) (merge p (stableGraph p y, y)))) < ρLog
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact hSmallLogMetric p _ ((hStableGauge p y).symm ▸ hy)
      have hh := graph_param_immersion 1 (exponentialChartC1 p) (stableModel p)
        (stableGraph p) (hStableC1.1 p) y hsource
      have hfun : (fun v : S.stable.toDistribution p ↦
          exponentialChartC1 p (stableModel p (v, stableGraph p v))) = stablePlaque p := by
        funext v
        change ExponentialLift.riemannianExp gMetric p
          ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm
            ((tangentSpaceCastModel 𝓘(ℝ, E) p) (merge p (stableGraph p v, v)))) =
          ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p v, v))
        rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hfun ▸ hh
    have hStableCoordinateSmooth (p : X) :
        letI := gs p
        letI := ss p
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, S.stable.toDistribution p) ∞
          (stableCoordinate p) {q | (p, q) ∈ logDomain} := by
      letI := gs p
      letI := ss p
      let C : E →L[ℝ] S.stable.toDistribution p :=
        (ContinuousLinearMap.snd ℝ _ _).comp ((merge p).symm.toContinuousLinearMap.comp
          (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap)
      have hc := C.contDiff.contMDiff.comp_contMDiffOn (hLogSmooth p)
      convert hc using 1
      ext q
      simp only [C, stableCoordinate, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_snd,
        ContinuousLinearEquiv.coe_coe, Function.comp_def,
        ContinuousLinearEquiv.symm_apply_apply]
      rfl
    have hStableCoordinateInverse (p : X) (y : S.stable.toDistribution p)
        (hy : ν p y.val < plaqueRadius) : stableCoordinate p (stablePlaque p y) = y := by
      change ((merge p).symm (localLog p (ExponentialLift.riemannianExp gMetric p
        (merge p (stableGraph p y, y))))).2 = y
      rw [(hLogInverse p _ (hSmallLogMetric p _ ((hStableGauge p y).symm ▸ hy))).2,
        ContinuousLinearEquiv.symm_apply_apply]
    have hStableDiscOpen (p : X) :
        IsOpen {y : S.stable.toDistribution p | ν p y.val < plaqueRadius} :=
      isOpen_lt (hcS.comp (splitAtlas.second.fibre_inducing p).continuous) continuous_const
    have hStablePlaqueDerivativeZero (p : X) (v : S.stable.toDistribution p) :
        letI := gs p
        letI := ss p
        mfderiv 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) (stablePlaque p) 0 v = v.val := by
      letI := gs p
      letI := ss p
      letI := gu p
      letI := su p
      have ht : HasFDerivAt (stableGraph p)
          (0 : S.stable.toDistribution p →L[ℝ] S.unstable.toDistribution p) 0 := by
        have hh := ((hStableC1.1 p).differentiable (by simp) 0).hasFDerivAt
        rwa [(hGraphTangent p).2] at hh
      have hp := ht.prodMk (hasFDerivAt_id (0 : S.stable.toDistribution p))
      let C := (tangentSpaceCastModel 𝓘(ℝ, E) p).toContinuousLinearMap.comp
        (merge p).toContinuousLinearMap
      have hc := C.hasFDerivAt.comp 0 hp
      have hh := exponential_fibreMap_mfderiv_zero gMetric p
        (fun y : S.stable.toDistribution p ↦ merge p (stableGraph p y, y))
        (by rw [(hGraphCentered p).2.1]; exact (merge p).map_zero) _ hc v
      apply hh.trans
      change (0 : TangentSpace 𝓘(ℝ, E) p) + v.val = v.val
      exact zero_add _
    have hStablePlaqueRestrictionContinuous (p : X) : Continuous
        (fun y : {y : S.stable.toDistribution p // ν p y.val < plaqueRadius} ↦
          stablePlaque p y.val) := by
      exact hStablePlaqueContinuous.comp_continuous
        ((splitAtlas.second.fibre_inducing p).continuous.comp continuous_subtype_val) (fun y ↦ y.property)
    obtain ⟨_, _, stableCaptureRadius, hStableCaptureRadius, hStableCapture⟩ :=
      hStableCharacterization le_rfl
    obtain ⟨_, _, unstableCaptureRadius, hUnstableCaptureRadius, hUnstableCapture⟩ :=
      hUnstableCharacterization le_rfl
    let captureRadius := min plaqueRadius (min stableCaptureRadius unstableCaptureRadius) / 2
    have hCaptureRadius : 0 < captureRadius :=
      half_pos (lt_min hPlaqueRadius (lt_min hStableCaptureRadius hUnstableCaptureRadius))
    have hCapturePlaque : captureRadius < plaqueRadius :=
      (half_lt_self (lt_min hPlaqueRadius (lt_min hStableCaptureRadius hUnstableCaptureRadius))).trans_le (min_le_left _ _)
    have hCaptureGraph : captureRadius < stableCaptureRadius :=
      (half_lt_self (lt_min hPlaqueRadius (lt_min hStableCaptureRadius hUnstableCaptureRadius))).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))
    obtain ⟨captureDistance, hCaptureDistance, hlogSmall⟩ := hLocalLog captureRadius hCaptureRadius
    let relativeCoordinates (z : X × X) : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p) :=
      ⟨z.1, (merge z.1).symm (localLog z.1 z.2)⟩
    let splitDynamics (z : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p)) : Sigma (fun p ↦
        S.unstable.toDistribution p × S.stable.toDistribution p) := ⟨f z.1, G z.1 z.2⟩
    have hRelativeStep (p q : X) (hpq : edist p q < captureDistance)
        (hfpq : edist (f p) (f q) < captureDistance) :
        splitDynamics (relativeCoordinates (p, q)) = relativeCoordinates (f p, f q) := by
      have hsmall := (hlogSmall p q hpq).1.trans hCapturePlaque
      have hnextsmall := (hlogSmall (f p) (f q) hfpq).1.trans hCapturePlaque
      have hAgree := (hAgreement ⟨p, mem_univ p⟩ (localLog p q)
        (show ν p (localLog p q) ≤ b from hsmall.le.trans hPlaqueAgreement)).2.2.2.1
      have hnextInv := (hExpLog (f p) (mem_univ (f p))
        (localLog (f p) (f q)) (hSmallMetric (f p) _ hnextsmall)).2
      change extension ⟨p, mem_univ p⟩ (localLog p q) =
        logarithm (f p) (f (ExponentialLift.riemannianExp gMetric p (localLog p q))) at hAgree
      rw [(hlogSmall p q hpq).2] at hAgree
      rw [(hlogSmall (f p) (f q) hfpq).2] at hnextInv
      dsimp only [splitDynamics, relativeCoordinates]
      apply congrArg (fun v : S.unstable.toDistribution (f p) × S.stable.toDistribution (f p) ↦
        (⟨f p, v⟩ : Sigma (fun p ↦ S.unstable.toDistribution p × S.stable.toDistribution p)))
      change (merge (f p)).symm (extension ⟨p, mem_univ p⟩
        (merge p ((merge p).symm (localLog p q)))) =
          (merge (f p)).symm (localLog (f p) (f q))
      rw [ContinuousLinearEquiv.apply_symm_apply, hAgree, hnextInv]
    have hStableLocalCapture (p q : X)
        (hpq : ∀ n : ℕ, edist ((f : X → X)^[n] p) ((f : X → X)^[n] q) < captureDistance) :
        ∃ y : S.stable.toDistribution p, ν p y.val < plaqueRadius ∧ stablePlaque p y = q := by
      let pairs (n : ℕ) := (((f : X → X)^[n] p), ((f : X → X)^[n] q))
      have hstep (n : ℕ) : splitDynamics (relativeCoordinates (pairs n)) =
          relativeCoordinates (pairs (n + 1)) := by
        have hn := hRelativeStep (pairs n).1 (pairs n).2 (hpq n)
          (by simpa only [pairs, Function.iterate_succ_apply'] using hpq (n + 1))
        simpa only [pairs, Function.iterate_succ_apply'] using hn
      have hiter (n : ℕ) : splitDynamics^[n] (relativeCoordinates (p, q)) =
          relativeCoordinates (pairs n) := by
        induction n with
        | zero => rfl
        | succ n ih => rw [Function.iterate_succ_apply', ih, hstep]
      have hnorm (n : ℕ) :
          ν (pairs n).1 (merge (pairs n).1 (relativeCoordinates (pairs n)).2) < captureRadius := by
        simpa only [relativeCoordinates, ContinuousLinearEquiv.apply_symm_apply] using
          (hlogSmall (pairs n).1 (pairs n).2 (hpq n)).1
      have hmem : (relativeCoordinates (p, q)).2 ∈ Set.range (fun y ↦ (stableGraph p y, y)) := by
        apply (hStableCapture p (relativeCoordinates (p, q)).2 ?_).mpr
        · refine ⟨?_, stableCaptureRadius, hStableCaptureRadius, ?_⟩
          · intro n
            change ‖(splitDynamics^[n] (relativeCoordinates (p, q))).2‖ < stableCaptureRadius
            rw [hiter]
            change max (ν (pairs n).1 (relativeCoordinates (pairs n)).2.1.val)
              (ν (pairs n).1 (relativeCoordinates (pairs n)).2.2.val) < stableCaptureRadius
            rw [← hνmerge]
            exact (hnorm n).trans hCaptureGraph
          · intro n
            change ‖(splitDynamics^[n] (relativeCoordinates (p, q))).2‖ ≤ stableCaptureRadius * 1 ^ n
            rw [hiter, one_pow, mul_one]
            change max (ν (pairs n).1 (relativeCoordinates (pairs n)).2.1.val)
              (ν (pairs n).1 (relativeCoordinates (pairs n)).2.2.val) ≤ stableCaptureRadius
            rw [← hνmerge]
            exact ((hnorm n).trans hCaptureGraph).le
        · change max (ν p (relativeCoordinates (p, q)).2.1.val)
            (ν p (relativeCoordinates (p, q)).2.2.val) < stableCaptureRadius
          rw [← hνmerge]
          exact (hnorm 0).trans hCaptureGraph
      obtain ⟨y, hy⟩ := hmem
      have hmergeEq := congrArg (merge p) hy
      change merge p (stableGraph p y, y) =
        merge p ((merge p).symm (localLog p q)) at hmergeEq
      rw [ContinuousLinearEquiv.apply_symm_apply] at hmergeEq
      refine ⟨y, ?_, ?_⟩
      · rw [← hStableGauge, hmergeEq]
        exact (hlogSmall p q (hpq 0)).1.trans hCapturePlaque
      · change ExponentialLift.riemannianExp gMetric p (merge p (stableGraph p y, y)) = q
        rw [hmergeEq]
        exact (hlogSmall p q (hpq 0)).2
    have hStableEventualCapture (p q : X)
        (hpq : Tendsto (fun n : ℕ ↦ edist ((f : X → X)^[n] p)
          ((f : X → X)^[n] q)) atTop (𝓝 0)) :
        ∃ N : ℕ, ∃ y : S.stable.toDistribution ((f : X → X)^[N] p),
          ν _ y.val < plaqueRadius ∧ stablePlaque _ y = (f : X → X)^[N] q := by
      obtain ⟨N, hN⟩ := asymptotic_eventually_close (f : X → X) p q
        captureDistance hCaptureDistance hpq
      exact ⟨N, hStableLocalCapture _ _ hN⟩
    have hStableAsymptoticIff (p q : X) :
        Tendsto (fun n : ℕ ↦ edist ((f : X → X)^[n] p)
          ((f : X → X)^[n] q)) atTop (𝓝 0) ↔
        ∃ N : ℕ, ∃ y : S.stable.toDistribution ((f : X → X)^[N] p),
          ν _ y.val < plaqueRadius ∧ stablePlaque _ y = (f : X → X)^[N] q := by
      constructor
      · exact hStableEventualCapture p q
      · rintro ⟨N, y, hy, heq⟩
        apply (orbitAsymptotic_shift (f : X → X) p q N).mp
        have ht := hStableAsymptotic ((f : X → X)^[N] p) y hy
        rw [heq] at ht
        exact ht
    let stableDisc (p : X) : Opens (S.stable.toDistribution p) :=
      ⟨{y | ν p y.val < plaqueRadius}, hStableDiscOpen p⟩
    have hStableSelfCoherence (p : X) (y₀ : S.stable.toDistribution p)
        (hy₀ : ν p y₀.val < plaqueRadius) :
        ∀ᶠ y in 𝓝 y₀, stablePlaque p y =
          stablePlaque (stablePlaque p y₀) (stableCoordinate (stablePlaque p y₀) (stablePlaque p y)) ∧
          ν (stablePlaque p y₀)
            (stableCoordinate (stablePlaque p y₀) (stablePlaque p y)).val < plaqueRadius := by
      have hu := uniformly_asymptotic_locally_close (f : X → X) f.continuous p
        (fun y : stableDisc p ↦ stablePlaque p y.val) (hStablePlaqueRestrictionContinuous p)
        (fun ε hε ↦ by
          obtain ⟨N, hN⟩ := hStableUniform ε hε
          exact ⟨N, fun n hn y ↦ hN n hn p y.val y.property⟩)
        ⟨y₀, hy₀⟩ captureDistance hCaptureDistance
      have hfactor : ∀ᶠ y : stableDisc p in 𝓝 ⟨y₀, hy₀⟩,
          stablePlaque p y.val = stablePlaque (stablePlaque p y₀)
            (stableCoordinate (stablePlaque p y₀) (stablePlaque p y.val)) ∧
          ν (stablePlaque p y₀)
            (stableCoordinate (stablePlaque p y₀) (stablePlaque p y.val)).val < plaqueRadius := by
        filter_upwards [hu] with y hy
        obtain ⟨z, hz, he⟩ := hStableLocalCapture (stablePlaque p y₀) (stablePlaque p y.val) hy
        have hcoord : stableCoordinate (stablePlaque p y₀) (stablePlaque p y.val) = z := by
          rw [← he]
          exact hStableCoordinateInverse _ _ hz
        rw [hcoord]
        exact ⟨he.symm, hz⟩
      have hmap := map_nhds_subtype_coe_eq_nhds (p := fun y : S.stable.toDistribution p ↦ ν p y.val < plaqueRadius) hy₀ ((hStableDiscOpen p).mem_nhds hy₀)
      rw [← hmap]
      exact hfactor
    have hStableRank (p : X) (y : S.stable.toDistribution p)
        (hy : ν p y.val < plaqueRadius) :
        Module.finrank ℝ (S.stable.toDistribution (stablePlaque p y)) =
          Module.finrank ℝ (S.stable.toDistribution p) := by
      have hconvex : Convex ℝ {y : S.stable.toDistribution p | ν p y.val < plaqueRadius} :=
        gauge_sublevel_convex (fun y : S.stable.toDistribution p ↦ ν p y.val)
          (fun y z ↦ hνadd p y.val z.val) (fun a y ↦ hνsmul p a y.val) plaqueRadius
      have hzero : ν p (0 : S.stable.toDistribution p).val < plaqueRadius := by
        simpa only [Submodule.coe_zero, hνzero] using hPlaqueRadius
      have hh := locallyConstant_comp_on_convex
        (fun p ↦ Module.finrank ℝ (S.stable.toDistribution p))
        S.stable.finrank_isLocallyConstant _ hconvex
        (fun y : stableDisc p ↦ stablePlaque p y.val) (hStablePlaqueRestrictionContinuous p)
        ⟨y, hy⟩ ⟨0, hzero⟩
      change Module.finrank ℝ (S.stable.toDistribution (stablePlaque p y)) =
        Module.finrank ℝ (S.stable.toDistribution (stablePlaque p 0)) at hh
      rw [hStablePlaqueZero] at hh
      exact hh
    have hStableRecenterChart (p : X) (y : S.stable.toDistribution p)
        (hy : ν p y.val < plaqueRadius) :
        ∃ e : OpenPartialHomeomorph (S.stable.toDistribution p)
            (S.stable.toDistribution (stablePlaque p y)),
          y ∈ e.source ∧
          (e : S.stable.toDistribution p → S.stable.toDistribution (stablePlaque p y)) =
            stableCoordinate (stablePlaque p y) ∘ stablePlaque p ∧
          e.source ⊆ (stableDisc p : Set _) ∧
          e.target ⊆ (stableDisc (stablePlaque p y) : Set _) ∧
          ∀ v ∈ e.source, stablePlaque p v = stablePlaque (stablePlaque p y) (e v) := by
      let q := stablePlaque p y
      let k := stableCoordinate q ∘ stablePlaque p
      have hk0 : k y = 0 := by
        change ((merge q).symm (localLog q q)).2 = 0
        rw [(hLogDiagonal q).2, map_zero]
        rfl
      have hyopen := (hStableDiscOpen p).mem_nhds hy
      have hqzero : ν q (0 : S.stable.toDistribution q).val < plaqueRadius := by
        simpa only [Submodule.coe_zero, hνzero] using hPlaqueRadius
      have hqopen := (hStableDiscOpen q).mem_nhds hqzero
      have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, S.stable.toDistribution q) ∞
          (stableCoordinate q) q :=
        (hStableCoordinateSmooth q).contMDiffAt
          ((logDomain.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds
            (hLogDiagonal q).1)
      have hk : ContMDiffAt 𝓘(ℝ, S.stable.toDistribution p)
          𝓘(ℝ, S.stable.toDistribution q) 1 k y :=
        (hc.of_le (by simp)).comp y ((hStablePlaqueC1 p).contMDiffAt hyopen)
      have hg : MDifferentiableAt 𝓘(ℝ, S.stable.toDistribution q) 𝓘(ℝ, E)
          (stablePlaque q) (k y) := by
        rw [hk0]
        exact ((hStablePlaqueC1 q).contMDiffAt hqopen).mdifferentiableAt (by simp)
      exact local_factorization_open_chart_restrict (stablePlaque p) (stablePlaque q)
        k y (hStableRank p y hy).symm (hStablePlaqueImmersion p y hy) hg hk.contDiffAt
        ((hStableSelfCoherence p y hy).mono (fun _ h ↦ h.1))
        _ (hStableDiscOpen p) hy _ (hStableDiscOpen q) (by rw [hk0]; exact hqzero)
    have hStableOverlapChart (p q : X)
        (y : S.stable.toDistribution p) (z : S.stable.toDistribution q)
        (hy : ν p y.val < plaqueRadius) (hz : ν q z.val < plaqueRadius)
        (heq : stablePlaque p y = stablePlaque q z) :
        ∃ e : OpenPartialHomeomorph (S.stable.toDistribution p) (S.stable.toDistribution q),
          y ∈ e.source ∧ e y = z ∧ e.source ⊆ (stableDisc p : Set _) ∧
          e.target ⊆ (stableDisc q : Set _) ∧
          ∀ v ∈ e.source, stablePlaque p v = stablePlaque q (e v) := by
      have hp := hStableRecenterChart p y hy
      rw [heq] at hp
      obtain ⟨ep, hyp, hep, hpsource, _, hpfactor⟩ := hp
      obtain ⟨eq, hzq, heqmap, hqsource, _, hqfactor⟩ := hStableRecenterChart q z hz
      have hcenter : ep y = eq z := by
        rw [hep, heqmap]
        exact congrArg (stableCoordinate (stablePlaque q z)) heq
      let e := ep.trans eq.symm
      have hysource : y ∈ e.source := by
        refine ⟨hyp, ?_⟩
        change ep y ∈ eq.target
        rw [hcenter]
        exact eq.map_source hzq
      refine ⟨e, hysource, ?_, ?_, ?_, ?_⟩
      · change eq.symm (ep y) = z
        rw [hcenter, eq.left_inv hzq]
      · intro v hv
        exact hpsource hv.1
      · intro v hv
        exact hqsource hv.1
      · intro v hv
        have hlast : e v ∈ eq.source := eq.map_target hv.2
        have heval : eq (e v) = ep v := eq.right_inv hv.2
        exact (hpfactor v hv.1).trans ((congrArg (stablePlaque (stablePlaque q z))
          heval.symm).trans (hqfactor (e v) hlast).symm)
    have hStableRankForward (p : X) :
        Module.finrank ℝ (S.stable.toDistribution (f p)) =
          Module.finrank ℝ (S.stable.toDistribution p) :=
      ((f.mfderivToContinuousLinearEquiv (by simp) p).ofSubmodules
        (S.stable.toDistribution p) (S.stable.toDistribution (f p)) (S.stable_map p)).finrank_eq.symm
    have hStableRankIterate (p : X) (n : ℕ) :=
      invariant_iterate_value (f : X → X) (fun p ↦ Module.finrank ℝ (S.stable.toDistribution p))
        hStableRankForward p n
    have hStableRankClass (p q : X) (hpq : (orbitAsymptoticSetoid (f : X → X)).r p q) :
        Module.finrank ℝ (S.stable.toDistribution p) =
          Module.finrank ℝ (S.stable.toDistribution q) := by
      obtain ⟨n, y, hy, heq⟩ := hStableEventualCapture p q hpq
      have hh := hStableRank ((f : X → X)^[n] p) y hy
      rw [heq, hStableRankIterate, hStableRankIterate] at hh
      exact hh.symm
    let stablePlaqueSet (p : X) : Set X := stablePlaque p '' (stableDisc p : Set _)
    have hStableSetTrap (p : X) : f '' stablePlaqueSet p ⊆ stablePlaqueSet (f p) := by
      rintro q ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨z, _, hz, he⟩ := hStableTrap p y hy
      exact ⟨z, hz, he.symm⟩
    have hStableStagesIncreasing (p : X) (n : ℕ) :=
      transportedPlaque_increasing f.toHomeomorph.toEquiv stablePlaqueSet hStableSetTrap p n
    have hStableStagesExhaustive (p : X) :
        (⋃ n : ℕ, transportedPlaque f.toHomeomorph.toEquiv stablePlaqueSet p n) =
          {q | (orbitAsymptoticSetoid (f : X → X)).r p q} := by
      ext q
      simp only [Set.mem_iUnion, transportedPlaque, Set.mem_preimage, stablePlaqueSet,
        Set.mem_image, Set.mem_ofPred_eq]
      exact (hStableAsymptoticIff p q).symm
    let stableRelation := orbitAsymptoticSetoid (f : X → X)
    let stableIndex := Quotient stableRelation
    let stableLabel : X → stableIndex := Quotient.mk stableRelation
    let stableLeaf (i : stableIndex) := {q : X // stableLabel q = i}
    let stableRank (i : stableIndex) := Module.finrank ℝ (S.stable.toDistribution i.out)
    have hLeafRank (i : stableIndex) (p : stableLeaf i) :
        stableRank i = Module.finrank ℝ (S.stable.toDistribution p.val) := by
      apply hStableRankClass
      apply Quotient.exact
      exact (Quotient.out_eq i).trans p.property.symm
    have stableModelEquiv (i : stableIndex) (p : stableLeaf i) :
        (Fin (stableRank i) → ℝ) ≃L[ℝ] S.stable.toDistribution p.val :=
      ContinuousLinearEquiv.ofFinrankEq ((Module.finrank_fin_fun ℝ).trans (hLeafRank i p))
    let leafPlaque (i : stableIndex) (p : stableLeaf i) (v : S.stable.toDistribution p.val) :
        stableLeaf i := if hv : ν p.val v.val < plaqueRadius then
          ⟨stablePlaque p.val v, (Quotient.sound (hStableAsymptotic p.val v hv)).symm.trans p.property⟩
        else p
    have hLeafPlaque (i : stableIndex) (p : stableLeaf i) (v : S.stable.toDistribution p.val)
        (hv : ν p.val v.val < plaqueRadius) : (leafPlaque i p v).val = stablePlaque p.val v := by
      simp only [leafPlaque, dite_eq_left hv]
    let stableLeafChart (i : stableIndex) (p : stableLeaf i) :
        PartialEquiv (stableLeaf i) (Fin (stableRank i) → ℝ) := {
      toFun := fun q ↦ (stableModelEquiv i p).symm (stableCoordinate p.val q.val)
      invFun := fun u ↦ leafPlaque i p (stableModelEquiv i p u)
      source := {q | ∃ v : S.stable.toDistribution p.val,
        ν p.val v.val < plaqueRadius ∧ stablePlaque p.val v = q.val}
      target := {u | ν p.val (stableModelEquiv i p u).val < plaqueRadius}
      map_source' := by
        rintro q ⟨v, hv, heq⟩
        change ν p.val ((stableModelEquiv i p)
          ((stableModelEquiv i p).symm (stableCoordinate p.val q.val))).val < plaqueRadius
        rw [ContinuousLinearEquiv.apply_symm_apply, ← heq, hStableCoordinateInverse p.val v hv]
        exact hv
      map_target' := by
        intro u hu
        exact ⟨stableModelEquiv i p u, hu, (hLeafPlaque i p _ hu).symm⟩
      left_inv' := by
        rintro q ⟨v, hv, heq⟩
        apply Subtype.ext
        change (leafPlaque i p ((stableModelEquiv i p)
          ((stableModelEquiv i p).symm (stableCoordinate p.val q.val)))).val = q.val
        rw [ContinuousLinearEquiv.apply_symm_apply, ← heq, hStableCoordinateInverse p.val v hv,
          hLeafPlaque i p v hv]
      right_inv' := by
        intro u hu
        change (stableModelEquiv i p).symm
          (stableCoordinate p.val (leafPlaque i p (stableModelEquiv i p u)).val) = u
        rw [hLeafPlaque i p _ hu, hStableCoordinateInverse p.val _ hu,
          ContinuousLinearEquiv.symm_apply_apply] }
    have hStableLeafChartCenter (i : stableIndex) (p : stableLeaf i) :
        p ∈ (stableLeafChart i p).source := by
      refine ⟨0, ?_, hStablePlaqueZero p.val⟩
      simpa only [Submodule.coe_zero, hνzero] using hPlaqueRadius
    have hStableLeafTransition (i : stableIndex) (p q : stableLeaf i)
        (u : Fin (stableRank i) → ℝ)
        (hu : u ∈ ((stableLeafChart i p).symm.trans (stableLeafChart i q)).source) :
        ∃ e : OpenPartialHomeomorph (Fin (stableRank i) → ℝ) (Fin (stableRank i) → ℝ),
          u ∈ e.source ∧ e.source ⊆ ((stableLeafChart i p).symm.trans (stableLeafChart i q)).source ∧
          EqOn (fun v ↦ ((stableLeafChart i p).symm.trans (stableLeafChart i q)) v) e e.source := by
      have hup : ν p.val (stableModelEquiv i p u).val < plaqueRadius := hu.1
      obtain ⟨z, hz, heq⟩ := hu.2
      change stablePlaque q.val z = (leafPlaque i p (stableModelEquiv i p u)).val at heq
      rw [hLeafPlaque i p _ hup] at heq
      obtain ⟨e₀, hue₀, _, he₀source, he₀target, he₀factor⟩ :=
        hStableOverlapChart p.val q.val (stableModelEquiv i p u) z hup hz heq.symm
      let e := ((stableModelEquiv i p).toHomeomorph.transOpenPartialHomeomorph e₀).transHomeomorph
        (stableModelEquiv i q).symm.toHomeomorph
      have heSource (v : Fin (stableRank i) → ℝ) : v ∈ e.source ↔ stableModelEquiv i p v ∈ e₀.source := Iff.rfl
      have heMap (v : Fin (stableRank i) → ℝ) :
          e v = (stableModelEquiv i q).symm (e₀ (stableModelEquiv i p v)) := rfl
      refine ⟨e, (heSource u).mpr hue₀, ?_, ?_⟩
      · intro v hv
        have hv₀ := (heSource v).mp hv
        have hpv := he₀source hv₀
        refine ⟨hpv, e₀ (stableModelEquiv i p v), he₀target (e₀.map_source hv₀), ?_⟩
        change stablePlaque q.val (e₀ (stableModelEquiv i p v)) =
          (leafPlaque i p (stableModelEquiv i p v)).val
        rw [hLeafPlaque i p _ hpv]
        exact (he₀factor _ hv₀).symm
      · intro v hv
        have hv₀ := (heSource v).mp hv
        have hpv := he₀source hv₀
        have hqv := he₀target (e₀.map_source hv₀)
        change (stableModelEquiv i q).symm
          (stableCoordinate q.val (leafPlaque i p (stableModelEquiv i p v)).val) = e v
        rw [hLeafPlaque i p _ hpv, he₀factor _ hv₀,
          hStableCoordinateInverse q.val _ hqv, heMap]
    have hStableLeafTransitionOpen (i : stableIndex) (p q : stableLeaf i) :
        IsOpen ((stableLeafChart i p).symm.trans (stableLeafChart i q)).source := by
      apply isOpen_iff_mem_nhds.mpr
      intro u hu
      obtain ⟨e, hue, hesub, _⟩ := hStableLeafTransition i p q u hu
      exact Filter.mem_of_superset (e.open_source.mem_nhds hue) hesub
    have hStableLeafTransitionContinuous (i : stableIndex) (p q : stableLeaf i) :
        ContinuousOn ((stableLeafChart i p).symm.trans (stableLeafChart i q))
          ((stableLeafChart i p).symm.trans (stableLeafChart i q)).source := by
      intro u hu
      obtain ⟨e, hue, _, heq⟩ := hStableLeafTransition i p q u hu
      have hc := e.continuousAt hue
      have hsame : ((stableLeafChart i p).symm.trans (stableLeafChart i q)) =ᶠ[𝓝 u] e :=
        Filter.mem_of_superset (e.open_source.mem_nhds hue) heq
      exact (hc.congr hsame.symm).continuousWithinAt
    let stableChartCore (i : stableIndex) : ChartedSpaceCore (Fin (stableRank i) → ℝ) (stableLeaf i) := {
      atlas := Set.range (stableLeafChart i)
      chartAt := stableLeafChart i
      mem_chart_source := hStableLeafChartCenter i
      chart_mem_atlas := fun p ↦ Set.mem_range_self p
      open_source := by
        rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
        exact hStableLeafTransitionOpen i p q
      continuousOn_toFun := by
        rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
        exact hStableLeafTransitionContinuous i p q }
    letI stableLeafTop (i : stableIndex) : TopologicalSpace (stableLeaf i) :=
      (stableChartCore i).toTopologicalSpace
    letI stableLeafCharts (i : stableIndex) : ChartedSpace (Fin (stableRank i) → ℝ) (stableLeaf i) :=
      (stableChartCore i).toChartedSpace
    have hStableLeafInclusionContinuous (i : stableIndex) :
        Continuous (fun p : stableLeaf i ↦ p.val) := by
      apply continuous_iff_continuousAt.mpr
      intro p
      let c := (stableChartCore i).openPartialHomeomorph (stableLeafChart i p) (Set.mem_range_self p)
      have hpc : p ∈ c.source := hStableLeafChartCenter i p
      have hc0 : c p = 0 := by
        change (stableModelEquiv i p).symm (((merge p.val).symm (localLog p.val p.val)).2) = 0
        rw [(hLogDiagonal p.val).2, map_zero]
        exact (stableModelEquiv i p).symm.map_zero
      have hzero : ν p.val (0 : S.stable.toDistribution p.val).val < plaqueRadius := by
        simpa only [Submodule.coe_zero, hνzero] using hPlaqueRadius
      have hpcont : ContinuousAt (stablePlaque p.val) (stableModelEquiv i p (c p)) := by
        rw [hc0, map_zero]
        exact ((hStablePlaqueC1 p.val).contMDiffAt
          ((hStableDiscOpen p.val).mem_nhds hzero)).continuousAt
      have hmodel : ContinuousAt (fun q : stableLeaf i ↦ stableModelEquiv i p (c q)) p :=
        (stableModelEquiv i p).continuous.continuousAt.comp (c.continuousAt hpc)
      have hc : ContinuousAt (fun q : stableLeaf i ↦
          stablePlaque p.val (stableModelEquiv i p (c q))) p := hpcont.comp (f := fun q : stableLeaf i ↦ stableModelEquiv i p (c q)) hmodel
      have heq : (fun q : stableLeaf i ↦ stablePlaque p.val (stableModelEquiv i p (c q))) =ᶠ[𝓝 p]
          (fun q : stableLeaf i ↦ q.val) := by
        filter_upwards [c.open_source.mem_nhds hpc] with q hq
        obtain ⟨v, hv, he⟩ := hq
        change stablePlaque p.val ((stableModelEquiv i p)
          ((stableModelEquiv i p).symm (stableCoordinate p.val q.val))) = q.val
        rw [ContinuousLinearEquiv.apply_symm_apply, ← he, hStableCoordinateInverse p.val v hv]
      exact hc.congr heq
    letI stableLeafHausdorff (i : stableIndex) : T2Space (stableLeaf i) :=
      T2Space.of_injective_continuous Subtype.val_injective (hStableLeafInclusionContinuous i)
    have hStableLiftContinuous {V : Type v} [TopologicalSpace V]
        (i : stableIndex) (P : V → stableLeaf i) (p : X)
        (hP : Continuous (fun v ↦ (P v).val))
        (huniform : ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ v : V,
          edist ((f : X → X)^[n] p) ((f : X → X)^[n] (P v).val) < ε) : Continuous P := by
      apply continuous_iff_continuousAt.mpr
      intro v₀
      let c := (stableChartCore i).openPartialHomeomorph
        (stableLeafChart i (P v₀)) (Set.mem_range_self (P v₀))
      have hcenter : P v₀ ∈ c.source := hStableLeafChartCenter i (P v₀)
      have hcoord : ContinuousAt (stableCoordinate (P v₀).val) (P v₀).val :=
        ((hStableCoordinateSmooth (P v₀).val).contMDiffAt
          ((logDomain.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds
            (hLogDiagonal (P v₀).val).1)).continuousAt
      have hcoords : ContinuousAt (fun v ↦ stableCoordinate (P v₀).val (P v).val) v₀ :=
        hcoord.comp (f := fun v ↦ (P v).val) hP.continuousAt
      have hcP : ContinuousAt (fun v ↦ c (P v)) v₀ :=
        (stableModelEquiv i (P v₀)).symm.continuous.continuousAt.comp hcoords
      have hinverse : ContinuousAt (fun v ↦ c.symm (c (P v))) v₀ :=
        (c.symm.continuousAt (c.map_source hcenter)).comp (f := fun v ↦ c (P v)) hcP
      have hclose := uniformly_asymptotic_locally_close (f : X → X) f.continuous p
        (fun v ↦ (P v).val) hP huniform v₀ captureDistance hCaptureDistance
      have heq : (fun v ↦ c.symm (c (P v))) =ᶠ[𝓝 v₀] P := by
        filter_upwards [hclose] with v hv
        apply c.left_inv
        exact hStableLocalCapture (P v₀).val (P v).val hv
      exact hinverse.congr heq
    let stableStageMap (i : stableIndex) (n : ℕ)
        (y : stableDisc ((f : X → X)^[n] i.out)) : stableLeaf i :=
      ⟨((f.symm : X → X)^[n]) (stablePlaque ((f : X → X)^[n] i.out) y.val), by
        apply Eq.trans _ (Quotient.out_eq i)
        apply Eq.symm
        apply Quotient.sound
        apply (hStableAsymptoticIff i.out _).mpr
        refine ⟨n, y.val, y.property, ?_⟩
        exact ((f.toHomeomorph.toEquiv.right_inv.iterate n)
          (stablePlaque ((f : X → X)^[n] i.out) y.val)).symm⟩
    have hStableStageAmbientContinuous (i : stableIndex) (n : ℕ) :
        Continuous (fun y ↦ (stableStageMap i n y).val) :=
      (f.symm.continuous.iterate n).comp (hStablePlaqueRestrictionContinuous _)
    have hStableStageUniform (i : stableIndex) (n : ℕ) (ε' : ENNReal) (hε' : 0 < ε') :
        ∃ N : ℕ, ∀ m ≥ N, ∀ y : stableDisc ((f : X → X)^[n] i.out),
          edist ((f : X → X)^[m] i.out) ((f : X → X)^[m] (stableStageMap i n y).val) < ε' := by
      obtain ⟨N, hN⟩ := hStableUniform ε' hε'
      refine ⟨N + n, ?_⟩
      intro m hm y
      have hmn : n ≤ m := by omega
      have hNm : N ≤ m - n := by omega
      have hmEq : m = (m - n) + n := by omega
      change edist ((f : X → X)^[m] i.out)
        ((f : X → X)^[m] (((f.symm : X → X)^[n])
          (stablePlaque ((f : X → X)^[n] i.out) y.val))) < ε'
      have hcancel (q : X) : (f : X → X)^[n] ((f.symm : X → X)^[n] q) = q :=
        (f.toHomeomorph.toEquiv.right_inv.iterate n) q
      rw [hmEq, Function.iterate_add_apply, Function.iterate_add_apply, hcancel]
      exact hN (m - n) hNm _ y.val y.property
    have hStableStageContinuous (i : stableIndex) (n : ℕ) : Continuous (stableStageMap i n) :=
      hStableLiftContinuous i (stableStageMap i n) i.out (hStableStageAmbientContinuous i n)
        (hStableStageUniform i n)
    have hStableStageCover (i : stableIndex) :
        (⋃ n : ℕ, Set.range (stableStageMap i n)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      have hrel : stableRelation.r i.out q.val :=
        Quotient.exact ((Quotient.out_eq i).trans q.property.symm)
      obtain ⟨n, y, hy, heq⟩ := hStableEventualCapture i.out q.val hrel
      apply Set.mem_iUnion.mpr
      refine ⟨n, ⟨⟨y, hy⟩, ?_⟩⟩
      apply Subtype.ext
      change ((f.symm : X → X)^[n]) (stablePlaque ((f : X → X)^[n] i.out) y) = q.val
      rw [heq]
      exact (f.toHomeomorph.toEquiv.left_inv.iterate n) q.val
    have hStableDiscZero (p : X) : (0 : S.stable.toDistribution p) ∈ stableDisc p := by
      change ν p (0 : S.stable.toDistribution p).val < plaqueRadius
      simpa only [Submodule.coe_zero, hνzero] using hPlaqueRadius
    have hStableDiscConvex (p : X) : Convex ℝ (stableDisc p : Set (S.stable.toDistribution p)) :=
      gauge_sublevel_convex (fun y : S.stable.toDistribution p ↦ ν p y.val)
        (fun y z ↦ hνadd p y.val z.val) (fun a y ↦ hνsmul p a y.val) plaqueRadius
    letI stableDiscConnected (p : X) : ConnectedSpace (stableDisc p) :=
      isConnected_iff_connectedSpace.mp ((hStableDiscConvex p).isConnected ⟨0, hStableDiscZero p⟩)
    have hStableStageRangeConnected (i : stableIndex) (n : ℕ) :
        IsConnected (Set.range (stableStageMap i n)) := isConnected_range (hStableStageContinuous i n)
    have hStableLeafConnected (i : stableIndex) : ConnectedSpace (stableLeaf i) := by
      let root : stableLeaf i := ⟨i.out, Quotient.out_eq i⟩
      have hroot (n : ℕ) : root ∈ Set.range (stableStageMap i n) := by
        refine ⟨⟨0, hStableDiscZero _⟩, ?_⟩
        apply Subtype.ext
        change (f.symm : X → X)^[n] (stablePlaque ((f : X → X)^[n] i.out) 0) = i.out
        rw [hStablePlaqueZero]
        exact (f.toHomeomorph.toEquiv.left_inv.iterate n) i.out
      have hh := isPreconnected_iUnion
        (show (⋂ n : ℕ, Set.range (stableStageMap i n)).Nonempty from
          ⟨root, Set.mem_iInter.mpr hroot⟩)
        (fun n ↦ (hStableStageRangeConnected i n).2)
      rw [hStableStageCover] at hh
      exact connectedSpace_iff_univ.mpr ⟨⟨root, Set.mem_univ root⟩, hh⟩
    have hStableLeafSecondCountable (i : stableIndex) : SecondCountableTopology (stableLeaf i) := by
      have hL : IsLindelof (Set.univ : Set (stableLeaf i)) := by
        rw [← hStableStageCover i]
        exact isLindelof_iUnion (fun n ↦ isLindelof_range (hStableStageContinuous i n))
      obtain ⟨C, hC, hcover⟩ := hL.elim_countable_subcover
        (fun p : stableLeaf i ↦ (chartAt (Fin (stableRank i) → ℝ) p).source)
        (fun p ↦ (chartAt (Fin (stableRank i) → ℝ) p).open_source)
        (by intro p _; exact Set.mem_iUnion.mpr ⟨p, mem_chart_source _ p⟩)
      exact ChartedSpace.secondCountable_of_countable_cover (Fin (stableRank i) → ℝ)
        (Set.eq_univ_iff_forall.mpr (fun p ↦ hcover (Set.mem_univ p))) hC
    have hStableLeafAtlas (i : stableIndex)
        (e : OpenPartialHomeomorph (stableLeaf i) (Fin (stableRank i) → ℝ))
        (he : e ∈ atlas (Fin (stableRank i) → ℝ) (stableLeaf i)) :
        ∃ p : stableLeaf i, e.toPartialEquiv = stableLeafChart i p := by
      change e ∈ ⋃ (a : PartialEquiv (stableLeaf i) (Fin (stableRank i) → ℝ))
        (ha : a ∈ (stableChartCore i).atlas), {(stableChartCore i).openPartialHomeomorph a ha} at he
      obtain ⟨a, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨ha, he⟩ := Set.mem_iUnion.mp he
      obtain ⟨p, rfl⟩ := ha
      refine ⟨p, ?_⟩
      have hh : e = (stableChartCore i).openPartialHomeomorph (stableLeafChart i p) (Set.mem_range_self p) :=
        Set.mem_singleton_iff.mp he
      rw [hh]
      rfl
    have stableLeafSmooth (i : stableIndex) :
        IsManifold 𝓘(ℝ, Fin (stableRank i) → ℝ) ∞ (stableLeaf i) := by
      have htransition (p q : stableLeaf i) :
          ContDiffOn ℝ ∞ ((stableLeafChart i p).symm.trans (stableLeafChart i q))
            ((stableLeafChart i p).symm.trans (stableLeafChart i q)).source := by
        let U := ((stableLeafChart i p).symm.trans (stableLeafChart i q)).source
        have hP : ContMDiffOn 𝓘(ℝ, Fin (stableRank i) → ℝ) 𝓘(ℝ, E) ∞
            (fun u ↦ stablePlaque p.val (stableModelEquiv i p u)) U :=
          (hStablePlaqueSmooth p.val).comp (stableModelEquiv i p).contDiff.contMDiff.contMDiffOn (fun u hu ↦ hu.1)
        have hmaps : MapsTo (fun u ↦ stablePlaque p.val (stableModelEquiv i p u)) U
            {v | (q.val, v) ∈ logDomain} := by
          intro u hu
          obtain ⟨z, hz, heq⟩ := hu.2
          change stablePlaque q.val z = (leafPlaque i p (stableModelEquiv i p u)).val at heq
          rw [hLeafPlaque i p _ hu.1] at heq
          change (q.val, stablePlaque p.val (stableModelEquiv i p u)) ∈ logDomain
          rw [← heq]
          exact (hLogInverse q.val _ (hSmallLogMetric q.val _ ((hStableGauge q.val z).symm ▸ hz))).1
        have hC := ((hStableCoordinateSmooth q.val)).comp hP hmaps
        have hB := (stableModelEquiv i q).symm.contDiff.contMDiff.comp_contMDiffOn hC
        have heq : EqOn ((stableLeafChart i p).symm.trans (stableLeafChart i q))
            (fun u ↦ (stableModelEquiv i q).symm
              (stableCoordinate q.val (stablePlaque p.val (stableModelEquiv i p u)))) U := by
          intro u hu
          change (stableModelEquiv i q).symm
            (stableCoordinate q.val (leafPlaque i p (stableModelEquiv i p u)).val) = _
          rw [hLeafPlaque i p _ hu.1]
        exact hB.contDiffOn.congr heq
      apply isManifold_of_contDiffOn
      intro e e' he he'
      obtain ⟨p, hp⟩ := hStableLeafAtlas i e he
      obtain ⟨q, hq⟩ := hStableLeafAtlas i e' he'
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.id_comp, Function.comp_id, preimage_id, range_id, inter_univ]
      change ContDiffOn ℝ ∞ (e.toPartialEquiv.symm.trans e'.toPartialEquiv)
        (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source
      rw [hp, hq]
      exact htransition p q
    have stableLeafC1 (i : stableIndex) : IsManifold 𝓘(ℝ, Fin (stableRank i) → ℝ) 1 (stableLeaf i) :=
      IsManifold.of_le (n := ∞) (by simp)
    have hStableLeafInclusionImmersion (i : stableIndex) :
        Manifold.IsImmersion 𝓘(ℝ, Fin (stableRank i) → ℝ) 𝓘(ℝ, E) ∞
          (fun p : stableLeaf i ↦ p.val) := by
      have hall : Manifold.IsImmersionOfComplement (S.unstable.toDistribution i.out)
          𝓘(ℝ, Fin (stableRank i) → ℝ) 𝓘(ℝ, E) ∞ (fun p : stableLeaf i ↦ p.val) := by
        intro p
        have hdimp := (stableModel p.val).finrank_eq
        have hdimroot := (stableModel i.out).finrank_eq
        simp only [Module.finrank_prod] at hdimp hdimroot
        have hrank := hLeafRank i p
        change Module.finrank ℝ (S.stable.toDistribution i.out) =
          Module.finrank ℝ (S.stable.toDistribution p.val) at hrank
        have U : S.unstable.toDistribution i.out ≃L[ℝ] S.unstable.toDistribution p.val :=
          ContinuousLinearEquiv.ofFinrankEq (by omega)
        let A := stableModelEquiv i p
        let e := (A.prodCongr U).trans (stableModel p.val)
        let g := U.symm ∘ stableGraph p.val ∘ A
        have hg : ContDiff ℝ ∞ g := U.symm.contDiff.comp ((hStableGraphSmooth p.val).comp A.contDiff)
        let φ := exponentialChart p.val
        let straighten := graphStraighteningDiffeomorph e g ∞ hg
        let b := (φ.symm.trans straighten.toPartialDiffeomorph).toOpenPartialHomeomorph
        let c := chartAt (Fin (stableRank i) → ℝ) p
        have hβformula (v : Fin (stableRank i) → ℝ) : stablePlaque p.val (A v) = φ (e (v, g v)) := by
          change ExponentialLift.riemannianExp gMetric p.val
            (merge p.val (stableGraph p.val (A v), A v)) =
            ExponentialLift.riemannianExp gMetric p.val
              ((tangentSpaceCastModel 𝓘(ℝ, E) p.val).symm
                ((tangentSpaceCastModel 𝓘(ℝ, E) p.val)
                  (merge p.val (U (U.symm (stableGraph p.val (A v))), A v))))
          rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
        have hsmall (v : Fin (stableRank i) → ℝ) (hv : v ∈ c.target) : e (v, g v) ∈ φ.source := by
          change ExponentialLift.metricNorm gMetric p.val
            ((tangentSpaceCastModel 𝓘(ℝ, E) p.val).symm
              ((tangentSpaceCastModel 𝓘(ℝ, E) p.val)
                (merge p.val (U (U.symm (stableGraph p.val (A v))), A v)))) < ρLog
          rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
          exact hSmallLogMetric p.val _ ((hStableGauge p.val (A v)).symm ▸ hv)
        have hsource : c.source ⊆ (fun q : stableLeaf i ↦ q.val) ⁻¹' b.source := by
          rintro q ⟨z, hz, heq⟩
          refine ⟨?_, Set.mem_univ _⟩
          change (p.val, q.val) ∈ logDomain
          rw [← heq]
          exact (hLogInverse p.val _ (hSmallLogMetric p.val _ ((hStableGauge p.val z).symm ▸ hz))).1
        apply Manifold.IsImmersionAtOfComplement.mk_of_charts e c b
        · exact mem_chart_source _ p
        · exact hsource (mem_chart_source _ p)
        · exact IsManifold.chart_mem_maximalAtlas p
        · apply b.mem_maximalAtlas_of_contMDiffOn
          · exact (φ.symm.trans straighten.toPartialDiffeomorph).contMDiffOn_toFun
          · exact (φ.symm.trans straighten.toPartialDiffeomorph).contMDiffOn_invFun
        · exact hsource
        · intro v hv
          have hv' : v ∈ c.target := by
            simpa only [OpenPartialHomeomorph.extend_target, mfld_simps] using hv
          change straighten (φ.symm (leafPlaque i p (A v)).val) = e (v, 0)
          rw [hLeafPlaque i p _ hv', hβformula]
          have hφ : φ.symm.toPartialEquiv (φ.toPartialEquiv (e (v, g v))) = e (v, g v) :=
            φ.left_inv (hsmall v hv')
          rw [hφ]
          change e ((e.symm (e (v, g v))).1,
            (e.symm (e (v, g v))).2 - g (e.symm (e (v, g v))).1) = e (v, 0)
          simp
      exact hall.isImmersion
    have hStableLeafTangent (i : stableIndex) (p : stableLeaf i) :
        (mfderiv 𝓘(ℝ, Fin (stableRank i) → ℝ) 𝓘(ℝ, E)
          (fun q : stableLeaf i ↦ q.val) p).range = S.stable.toDistribution p.val := by
      let c := chartAt (Fin (stableRank i) → ℝ) p
      let A := stableModelEquiv i p
      let k : stableLeaf i → S.stable.toDistribution p.val := fun q ↦ A (c q)
      have hpc : p ∈ c.source := mem_chart_source _ p
      have hk0 : k p = 0 := by
        change (stableModelEquiv i p) ((stableModelEquiv i p).symm
          (((merge p.val).symm (localLog p.val p.val)).2)) = 0
        rw [ContinuousLinearEquiv.apply_symm_apply, (hLogDiagonal p.val).2, map_zero]
        rfl
      have hc : ContMDiffAt 𝓘(ℝ, Fin (stableRank i) → ℝ)
          𝓘(ℝ, Fin (stableRank i) → ℝ) 1 c p :=
        contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) hpc
      have hk : MDifferentiableAt 𝓘(ℝ, Fin (stableRank i) → ℝ)
          𝓘(ℝ, S.stable.toDistribution p.val) k p :=
        (A.contDiff.contMDiff.contMDiffAt.comp p hc).mdifferentiableAt (by simp)
      have hp : MDifferentiableAt 𝓘(ℝ, S.stable.toDistribution p.val) 𝓘(ℝ, E)
          (stablePlaque p.val) (k p) := by
        rw [hk0]
        exact ((hStablePlaqueC1 p.val).contMDiffAt
          ((stableDisc p.val).isOpen.mem_nhds (hStableDiscZero p.val))).mdifferentiableAt (by simp)
      have heq : (fun q : stableLeaf i ↦ q.val) =ᶠ[𝓝 p] stablePlaque p.val ∘ k := by
        filter_upwards [c.open_source.mem_nhds hpc] with q hq
        obtain ⟨z, hz, he⟩ := hq
        change q.val = stablePlaque p.val ((stableModelEquiv i p)
          ((stableModelEquiv i p).symm (stableCoordinate p.val q.val)))
        rw [ContinuousLinearEquiv.apply_symm_apply, ← he, hStableCoordinateInverse p.val z hz]
      have hle : (mfderiv 𝓘(ℝ, Fin (stableRank i) → ℝ) 𝓘(ℝ, E)
          (fun q : stableLeaf i ↦ q.val) p).range ≤ S.stable.toDistribution p.val := by
        rintro w ⟨v, rfl⟩
        have hd := congrArg (fun D : TangentSpace 𝓘(ℝ, Fin (stableRank i) → ℝ) p →L[ℝ]
          TangentSpace 𝓘(ℝ, E) p.val ↦ D v)
          (heq.mfderiv_eq (I := 𝓘(ℝ, Fin (stableRank i) → ℝ)) (I' := 𝓘(ℝ, E)))
        have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, Fin (stableRank i) → ℝ))
          (I' := 𝓘(ℝ, S.stable.toDistribution p.val)) (I'' := 𝓘(ℝ, E))
          (f := k) (g := stablePlaque p.val) p hp hk v
        have hvalue := hd.trans hcomp
        rw [hk0] at hvalue
        have hzero := hStablePlaqueDerivativeZero p.val
          (mfderiv 𝓘(ℝ, Fin (stableRank i) → ℝ) 𝓘(ℝ, S.stable.toDistribution p.val) k p v)
        have hfinal := hvalue.trans hzero
        exact Eq.mpr (congrArg (fun v : TangentSpace 𝓘(ℝ, E) p.val ↦
          v ∈ S.stable.toDistribution p.val) hfinal) (Subtype.property _)
      apply Submodule.eq_of_le_of_finrank_eq hle
      have hImm := hStableLeafInclusionImmersion i
      exact (LinearMap.finrank_range_of_inj (hImm.mfderiv_injective (by simp) p)).trans
        ((Module.finrank_fin_fun ℝ).trans (hLeafRank i p))
    let stableNativeLeaf (i : stableIndex) :
        NativeLeaf (r := stableRank i) S.stable.toDistribution (stableLeaf i) := {
      inclusion := Subtype.val
      injective := Subtype.val_injective
      immersion := hStableLeafInclusionImmersion i
      connected := hStableLeafConnected i
      hausdorff := stableLeafHausdorff i
      countable := hStableLeafSecondCountable i
      tangent := hStableLeafTangent i }
    let stablePartition : LeafPartition S.stable.toDistribution stableIndex stableLeaf stableRank := {
      leaf := stableNativeLeaf
      cover := fun p ↦ ⟨stableLabel p, ⟨p, rfl⟩, rfl⟩
      disjoint := by
        intro i j p q heq
        exact p.property.symm.trans ((congrArg stableLabel heq).trans q.property) }
    let stableIdentification : DistanceLeafIdentification stablePartition f edist := {
      label := stableLabel
      equality := by
        intro x
        ext y
        change (∃ q : stableLeaf (stableLabel x), q.val = y) ↔ stableRelation.r y x
        constructor
        · rintro ⟨q, rfl⟩
          exact Quotient.exact q.property
        · intro hy
          exact ⟨⟨y, Quotient.sound hy⟩, rfl⟩ }
    let stablePermutation : stableIndex ≃ stableIndex :=
      Quotient.congr f.toHomeomorph.toEquiv (fun p q ↦ by
        change (orbitAsymptoticSetoid (f : X → X)).r p q ↔
          (orbitAsymptoticSetoid (f : X → X)).r (f p) (f q)
        simpa only [Function.iterate_one] using (orbitAsymptotic_shift (f : X → X) p q 1).symm)
    let stableTransport (i : stableIndex) : stableLeaf i ≃ stableLeaf (stablePermutation i) := {
      toFun := fun p ↦ ⟨f p.val, congrArg stablePermutation p.property⟩
      invFun := fun q ↦ ⟨f.symm q.val, by
        apply stablePermutation.injective
        change stableLabel (f (f.symm q.val)) = stablePermutation i
        rw [f.apply_symm_apply]
        exact q.property⟩
      left_inv := by intro p; apply Subtype.ext; exact f.symm_apply_apply p.val
      right_inv := by intro q; apply Subtype.ext; exact f.apply_symm_apply q.val }
    have hStableCommutingMapContinuous (i j : stableIndex) (T : stableLeaf i → stableLeaf j)
        (e : X → X) (he : Continuous e) (hcomm : Function.Commute e (f : X → X))
        (hT : ∀ q, (T q).val = e q.val) : Continuous T := by
      apply continuous_iff_continuousAt.mpr
      intro p
      let Q : stableDisc p.val → stableLeaf j := fun y ↦ T (leafPlaque i p y.val)
      have hQambient : Continuous (fun y : stableDisc p.val ↦ (Q y).val) := by
        apply (he.comp (hStablePlaqueRestrictionContinuous p.val)).congr
        intro y
        exact ((hT (leafPlaque i p y.val)).trans (congrArg e (hLeafPlaque i p y.val y.property))).symm
      have hQuniform (ε' : ENNReal) (hε' : 0 < ε') :
          ∃ N : ℕ, ∀ n ≥ N, ∀ y : stableDisc p.val,
            edist ((f : X → X)^[n] (e p.val)) ((f : X → X)^[n] (Q y).val) < ε' := by
        obtain ⟨δ', hδ', hδbound⟩ := EMetric.uniformContinuous_iff.mp
          (CompactSpace.uniformContinuous_of_continuous he) ε' hε'
        obtain ⟨N, hN⟩ := hStableUniform δ' hδ'
        refine ⟨N, ?_⟩
        intro n hn y
        have hh := hδbound (hN n hn p.val y.val y.property)
        have hc (z : X) : e ((f : X → X)^[n] z) = (f : X → X)^[n] (e z) :=
          hcomm.iterate_right n z
        rw [hc, hc] at hh
        have hy : (Q y).val = e (stablePlaque p.val y.val) :=
          (hT (leafPlaque i p y.val)).trans (congrArg e (hLeafPlaque i p y.val y.property))
        rwa [hy]
      have hQ : Continuous Q := hStableLiftContinuous j Q (e p.val) hQambient hQuniform
      let c := chartAt (Fin (stableRank i) → ℝ) p
      let vmap (q : c.source) : stableDisc p.val :=
        ⟨stableModelEquiv i p (c q.val), by
          obtain ⟨y, hy, heq⟩ := q.property
          change ν p.val ((stableModelEquiv i p)
            ((stableModelEquiv i p).symm (stableCoordinate p.val q.val.val))).val < plaqueRadius
          rw [ContinuousLinearEquiv.apply_symm_apply, ← heq, hStableCoordinateInverse p.val y hy]
          exact hy⟩
      have hvmap : Continuous vmap := by
        apply Continuous.subtype_mk
        exact (stableModelEquiv i p).continuous.comp
          (c.continuousOn.comp_continuous continuous_subtype_val (fun q ↦ q.property))
      have hrest : Continuous (fun q : c.source ↦ T q.val) := by
        apply (hQ.comp hvmap).congr
        intro q
        change T (c.symm (c q.val)) = T q.val
        rw [c.left_inv q.property]
      have hOn : ContinuousOn T c.source := continuousOn_iff_continuous_domRestrict.mpr hrest
      exact hOn.continuousAt (c.open_source.mem_nhds (mem_chart_source _ p))
    have hStableTransportContinuous (i : stableIndex) : Continuous (stableTransport i) :=
      hStableCommutingMapContinuous i (stablePermutation i) (stableTransport i)
        f f.continuous (fun _ ↦ rfl) (fun _ ↦ rfl)
    have hStableTransportInverseContinuous (i : stableIndex) :
        Continuous (stableTransport i).symm :=
      hStableCommutingMapContinuous (stablePermutation i) i (stableTransport i).symm
        f.symm f.symm.continuous (fun x ↦ by simp) (fun _ ↦ rfl)
    let stableLeafDiffeomorph (i : stableIndex) :
        Diffeomorph 𝓘(ℝ, Fin (stableRank i) → ℝ)
          𝓘(ℝ, Fin (stableRank (stablePermutation i)) → ℝ)
          (stableLeaf i) (stableLeaf (stablePermutation i)) ∞ := {
      toEquiv := stableTransport i
      contMDiff_toFun := by
        apply (ContMDiff.iff_comp_isImmersion (stableNativeLeaf (stablePermutation i)).immersion).mpr
        exact ⟨hStableTransportContinuous i,
          f.contMDiff.comp (stableNativeLeaf i).immersion.contMDiff⟩
      contMDiff_invFun := by
        apply (ContMDiff.iff_comp_isImmersion (stableNativeLeaf i).immersion).mpr
        exact ⟨hStableTransportInverseContinuous i,
          f.symm.contMDiff.comp (stableNativeLeaf (stablePermutation i)).immersion.contMDiff⟩ }
    let stableInvariance : LeafDynamicalInvariance stablePartition f := {
      permutation := stablePermutation
      transport := stableLeafDiffeomorph
      intertwining := fun _ _ ↦ rfl }
    let stableCenteredChart (x : X) :=
      chartAt (Fin (stableRank (stableLabel x)) → ℝ) (⟨x, rfl⟩ : stableLeaf (stableLabel x))
    let stableSourceDisc (x : X) : Opens (Fin (stableRank (stableLabel x)) → ℝ) :=
      ⟨(stableCenteredChart x).target, (stableCenteredChart x).open_target⟩
    let stableNativePlaque (x : X) : Opens (stableLeaf (stableLabel x)) :=
      ⟨(stableCenteredChart x).source, (stableCenteredChart x).open_source⟩
    let stableNativeChart (x : X) :
        Diffeomorph 𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ)
          (stableSourceDisc x) (stableNativePlaque x) ∞ := {
      toEquiv := (stableCenteredChart x).toHomeomorphSourceTarget.symm.toEquiv
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff _ _).mp
        exact contMDiffOn_chart_symm.comp_contMDiff contMDiff_subtype_val (fun v ↦ v.property)
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff _ _).mp
        change ContMDiff _ _ ∞ (fun q : stableNativePlaque x ↦ (stableCenteredChart x) q.val)
        exact (contMDiffOn_chart (I := 𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ))
          (x := (⟨x, rfl⟩ : stableLeaf (stableLabel x)))).comp_contMDiff
            contMDiff_subtype_val (fun q ↦ q.property) }
    let stableSourceMap (x : X) (v : stableSourceDisc x) : X :=
      ((stableNativeChart x v).val).val
    have hStableSourceFormula (x : X) (v : stableSourceDisc x) :
        stableSourceMap x v = stablePlaque x (stableModelEquiv (stableLabel x) ⟨x, rfl⟩ v.val) :=
      hLeafPlaque (stableLabel x) ⟨x, rfl⟩ _ v.property
    have hStableSourceZero (x : X) : (0 : Fin (stableRank (stableLabel x)) → ℝ) ∈
        stableSourceDisc x := by
      change ν x ((stableModelEquiv (stableLabel x) ⟨x, rfl⟩) 0).val < plaqueRadius
      simpa only [map_zero, Submodule.coe_zero, hνzero] using hPlaqueRadius
    let stableSourceCenter (x : X) : stableSourceDisc x := ⟨0, hStableSourceZero x⟩
    have hStableSourceCentered (x : X) : stableSourceMap x (stableSourceCenter x) = x := by
      rw [hStableSourceFormula]
      simpa [stableSourceCenter] using hStablePlaqueZero x
    have hStableSourceConnected (x : X) :
        IsConnected (stableSourceDisc x : Set (Fin (stableRank (stableLabel x)) → ℝ)) := by
      have hc := (hStableDiscConvex x).linear_preimage
        (stableModelEquiv (stableLabel x) ⟨x, rfl⟩).toLinearMap
      exact hc.isConnected ⟨0, hStableSourceZero x⟩
    have hStableSourceRange (x : X) : Set.range (stableSourceMap x) = stablePlaqueSet x := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨_, v.property, (hStableSourceFormula x v).symm⟩
      · rintro ⟨v, hv, rfl⟩
        let A := stableModelEquiv (stableLabel x) ⟨x, rfl⟩
        have hu : A.symm v ∈ stableSourceDisc x := by
          change ν x (A (A.symm v)).val < plaqueRadius
          rwa [A.apply_symm_apply]
        refine ⟨⟨A.symm v, hu⟩, ?_⟩
        rw [hStableSourceFormula]
        exact congrArg (stablePlaque x) (A.apply_symm_apply v)
    have hStableSourceTrapped (x : X) : f '' Set.range (stableSourceMap x) ⊆
        Set.range (stableSourceMap (f x)) := by
      rw [hStableSourceRange, hStableSourceRange]
      exact hStableSetTrap x
    have hStableSourceImmersion (x : X) : Manifold.IsImmersion
        𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ) 𝓘(ℝ, E) ∞ (stableSourceMap x) :=
      by
      let A := stableModelEquiv (stableLabel x) ⟨x, rfl⟩
      let e := (A.prodCongr (ContinuousLinearEquiv.refl ℝ (S.unstable.toDistribution x))).trans
        (stableModel x)
      let g := stableGraph x ∘ A
      let φ := exponentialChart x
      let straighten := graphStraighteningDiffeomorph e g ∞ ((hStableGraphSmooth x).comp A.contDiff)
      let b := (φ.symm.trans straighten.toPartialDiffeomorph).toOpenPartialHomeomorph
      have hformula (v : Fin (stableRank (stableLabel x)) → ℝ) :
          stablePlaque x (A v) = φ (e (v, g v)) := by
        change ExponentialLift.riemannianExp gMetric x (merge x (stableGraph x (A v), A v)) =
          ExponentialLift.riemannianExp gMetric x ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm
            ((tangentSpaceCastModel 𝓘(ℝ, E) x) (merge x (stableGraph x (A v), A v))))
        rw [ContinuousLinearEquiv.symm_apply_apply]
      have hsmall (v : stableSourceDisc x) : e (v.val, g v.val) ∈ φ.source := by
        change ExponentialLift.metricNorm gMetric x ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm
          ((tangentSpaceCastModel 𝓘(ℝ, E) x) (merge x (stableGraph x (A v.val), A v.val)))) < ρLog
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact hSmallLogMetric x _ ((hStableGauge x _).symm ▸ v.property)
      have hall : Manifold.IsImmersionOfComplement (S.unstable.toDistribution x)
          𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ) 𝓘(ℝ, E) ∞ (stableSourceMap x) := by
        intro v
        let c := chartAt (Fin (stableRank (stableLabel x)) → ℝ) v
        have hcval (w : stableSourceDisc x) : c w = w.val := rfl
        have hsource : c.source ⊆ stableSourceMap x ⁻¹' b.source := by
          intro w _
          refine ⟨?_, Set.mem_univ _⟩
          change (x, stableSourceMap x w) ∈ logDomain
          rw [hStableSourceFormula]
          exact (hLogInverse x _ (hSmallLogMetric x _
            ((hStableGauge x _).symm ▸ w.property))).1
        apply Manifold.IsImmersionAtOfComplement.mk_of_charts e c b
        · exact mem_chart_source _ v
        · exact hsource (mem_chart_source _ v)
        · exact IsManifold.chart_mem_maximalAtlas v
        · exact b.mem_maximalAtlas_of_contMDiffOn
            (φ.symm.trans straighten.toPartialDiffeomorph).contMDiffOn_toFun
            (φ.symm.trans straighten.toPartialDiffeomorph).contMDiffOn_invFun
        · exact hsource
        · intro z hz
          have hz' : z ∈ c.target := by
            simpa only [OpenPartialHomeomorph.extend_target, mfld_simps] using hz
          have heval : (c.symm z).val = z := c.right_inv hz'
          change straighten (φ.symm (stableSourceMap x (c.symm z))) = e (z, 0)
          rw [hStableSourceFormula, hformula]
          have hφ := φ.left_inv (hsmall (c.symm z))
          change φ.symm.toPartialEquiv (φ.toPartialEquiv (e ((c.symm z).val, g (c.symm z).val))) = _ at hφ
          rw [hφ, heval]
          change e ((e.symm (e (z, g z))).1,
            (e.symm (e (z, g z))).2 - g (e.symm (e (z, g z))).1) = e (z, 0)
          simp
      exact hall.isImmersion
    have hStableSourceEmbedding (x : X) : IsEmbedding (stableSourceMap x) := by
      let U : Opens X := ⟨{q | (x, q) ∈ logDomain},
        logDomain.isOpen.preimage (continuous_const.prodMk continuous_id)⟩
      have hmaps (v : stableSourceDisc x) : stableSourceMap x v ∈ U := by
        rw [hStableSourceFormula]
        exact (hLogInverse x _ (hSmallLogMetric x _
          ((hStableGauge x _).symm ▸ v.property))).1
      let P : stableSourceDisc x → U := fun v ↦ ⟨stableSourceMap x v, hmaps v⟩
      let C : U → Fin (stableRank (stableLabel x)) → ℝ := fun q ↦
        (stableModelEquiv (stableLabel x) ⟨x, rfl⟩).symm (stableCoordinate x q.val)
      have hP : Continuous P := (hStableSourceImmersion x).contMDiff.continuous.subtype_mk hmaps
      have hC : Continuous C := (stableModelEquiv (stableLabel x) ⟨x, rfl⟩).symm.continuous.comp
        ((hStableCoordinateSmooth x).continuousOn.comp_continuous continuous_subtype_val
          (fun q ↦ q.property))
      have hcomp : C ∘ P = (Subtype.val : stableSourceDisc x → _) := by
        funext v
        change (stableModelEquiv (stableLabel x) ⟨x, rfl⟩).symm
          (stableCoordinate x (stableSourceMap x v)) = v.val
        rw [hStableSourceFormula, hStableCoordinateInverse x _ v.property,
          ContinuousLinearEquiv.symm_apply_apply]
      have hEmb : IsEmbedding P := IsEmbedding.of_comp hP hC
        (hcomp.symm ▸ IsEmbedding.subtypeVal)
      exact (IsEmbedding.subtypeVal (p := fun q : X ↦ q ∈ U)).comp hEmb
    have hStableSourceSmoothEmbedding (x : X) : Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ) 𝓘(ℝ, E) ∞ (stableSourceMap x) :=
      ⟨hStableSourceImmersion x, hStableSourceEmbedding x⟩
    let stableIteratePermutation (n : ℕ) : stableIndex ≃ stableIndex :=
      Quotient.congr (realIterate 𝓘(ℝ, E) f n).toEquiv (fun p q ↦ by
        change stableRelation.r p q ↔ stableRelation.r ((f : X → X)^[n] p) ((f : X → X)^[n] q)
        exact (orbitAsymptotic_shift (f : X → X) p q n).symm)
    let stableIterateTransport (n : ℕ) (i : stableIndex) :
        stableLeaf i ≃ stableLeaf (stableIteratePermutation n i) := {
      toFun := fun p ↦ ⟨(f : X → X)^[n] p.val, congrArg (stableIteratePermutation n) p.property⟩
      invFun := fun q ↦ ⟨(f.symm : X → X)^[n] q.val, by
        apply (stableIteratePermutation n).injective
        change stableLabel ((f : X → X)^[n] ((f.symm : X → X)^[n] q.val)) = _
        rw [show (f : X → X)^[n] ((f.symm : X → X)^[n] q.val) = q.val from
          f.right_inv.iterate n q.val]
        exact q.property⟩
      left_inv := by intro p; apply Subtype.ext; exact f.left_inv.iterate n p.val
      right_inv := by intro q; apply Subtype.ext; exact f.right_inv.iterate n q.val }
    let stableIterateDiffeomorph (n : ℕ) (i : stableIndex) :
        Diffeomorph 𝓘(ℝ, Fin (stableRank i) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableIteratePermutation n i)) → ℝ)
          (stableLeaf i) (stableLeaf (stableIteratePermutation n i)) ∞ := {
      toEquiv := stableIterateTransport n i
      contMDiff_toFun := by
        apply (ContMDiff.iff_comp_isImmersion (stableNativeLeaf (stableIteratePermutation n i)).immersion).mpr
        refine ⟨hStableCommutingMapContinuous i _ _ _ (f.continuous.iterate n)
          ((Function.Commute.refl (f : X → X)).iterate_left n) (fun _ ↦ rfl), ?_⟩
        exact (f.contMDiff.iterate n).comp (stableNativeLeaf i).immersion.contMDiff
      contMDiff_invFun := by
        apply (ContMDiff.iff_comp_isImmersion (stableNativeLeaf i).immersion).mpr
        have hc : Function.Commute (f.symm : X → X) (f : X → X) := fun p ↦ by simp
        refine ⟨hStableCommutingMapContinuous _ i _ _ (f.symm.continuous.iterate n)
          (hc.iterate_left n) (fun _ ↦ rfl), ?_⟩
        exact (f.symm.contMDiff.iterate n).comp
          (stableNativeLeaf (stableIteratePermutation n i)).immersion.contMDiff }
    let stableForwardDiffeomorph (x : X) (n : ℕ) :
        Diffeomorph 𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel ((f : X → X)^[n] x))) → ℝ)
          (stableLeaf (stableLabel x)) (stableLeaf (stableLabel ((f : X → X)^[n] x))) ∞ :=
      stableIterateDiffeomorph n (stableLabel x)
    let stableStage (x : X) (n : ℕ) : Opens (stableLeaf (stableLabel x)) :=
      ⟨stableForwardDiffeomorph x n ⁻¹'
        (stableNativePlaque ((f : X → X)^[n] x) : Set (stableLeaf (stableLabel ((f : X → X)^[n] x)))),
        (stableNativePlaque ((f : X → X)^[n] x)).isOpen.preimage
          (stableForwardDiffeomorph x n).continuous⟩
    let stableStageRestriction (x : X) (n : ℕ) :
        Diffeomorph 𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel ((f : X → X)^[n] x))) → ℝ)
          (stableStage x n) (stableNativePlaque ((f : X → X)^[n] x)) ∞ := {
      toEquiv := {
        toFun := fun p ↦ ⟨stableForwardDiffeomorph x n p.val, p.property⟩
        invFun := fun q ↦ ⟨(stableForwardDiffeomorph x n).symm q.val, by
          change stableForwardDiffeomorph x n
            ((stableForwardDiffeomorph x n).symm q.val) ∈ stableNativePlaque ((f : X → X)^[n] x)
          rw [Diffeomorph.apply_symm_apply]
          exact q.property⟩
        left_inv := by intro p; apply Subtype.ext; exact Diffeomorph.symm_apply_apply _ _
        right_inv := by intro q; apply Subtype.ext; exact Diffeomorph.apply_symm_apply _ _ }
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff _ _).mp
        exact (stableForwardDiffeomorph x n).contMDiff.comp contMDiff_subtype_val
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff _ _).mp
        exact (stableForwardDiffeomorph x n).symm.contMDiff.comp contMDiff_subtype_val }
    let stableStageChart (x : X) (n : ℕ) :
        Diffeomorph 𝓘(ℝ, Fin (stableRank (stableLabel ((f : X → X)^[n] x))) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ)
          (stableSourceDisc ((f : X → X)^[n] x)) (stableStage x n) ∞ :=
      (stableNativeChart ((f : X → X)^[n] x)).trans (stableStageRestriction x n).symm
    have hStableStageFactorization (x : X) (n : ℕ) (v : stableSourceDisc ((f : X → X)^[n] x)) :
        (stableStageChart x n v).val.val =
          (f.symm : X → X)^[n] (stableSourceMap ((f : X → X)^[n] x) v) := rfl
    have hStableStageZero (x : X) : stableStage x 0 = stableNativePlaque x := by
      ext p
      rfl
    have hStableStageMembership (x : X) (n : ℕ) (q : stableLeaf (stableLabel x)) :
        q ∈ stableStage x n ↔ q.val ∈ transportedPlaque f.toHomeomorph.toEquiv stablePlaqueSet x n :=
      Iff.rfl
    have hStableStageIncreasing (x : X) (n : ℕ) :
        (stableStage x n : Set (stableLeaf (stableLabel x))) ⊆ stableStage x (n + 1) := by
      intro q hq
      exact (hStableStageMembership x (n + 1) q).mpr
        (hStableStagesIncreasing x n ((hStableStageMembership x n q).mp hq))
    have hStableStageExhaustive (x : X) :
        (⋃ n, (stableStage x n : Set (stableLeaf (stableLabel x)))) = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro q
      have hrel : stableRelation.r x q.val := stableRelation.symm (Quotient.exact q.property)
      have hm : q.val ∈ ⋃ n, transportedPlaque f.toHomeomorph.toEquiv stablePlaqueSet x n := by
        rw [hStableStagesExhaustive]
        exact hrel
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
      exact Set.mem_iUnion.mpr ⟨n, (hStableStageMembership x n q).mpr hn⟩
    have hStableStageImage (x : X) (n : ℕ) :
        (fun q : stableLeaf (stableLabel x) ↦ q.val) '' (stableStage x n : Set _) =
          (f.symm : X → X)^[n] '' Set.range (stableSourceMap ((f : X → X)^[n] x)) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        let v := (stableStageChart x n).symm ⟨q, hq⟩
        refine ⟨stableSourceMap ((f : X → X)^[n] x) v, Set.mem_range_self v, ?_⟩
        rw [← hStableStageFactorization]
        exact congrArg (fun z : stableStage x n ↦ z.val.val)
          ((stableStageChart x n).apply_symm_apply ⟨q, hq⟩)
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        exact ⟨(stableStageChart x n v).val, (stableStageChart x n v).property,
          hStableStageFactorization x n v⟩
    have hStableStageTopology (x : X) (W : Set (stableLeaf (stableLabel x))) :
        IsOpen W ↔ ∀ n, IsOpen ((Subtype.val : stableStage x n → _) ⁻¹' W) := by
      rw [isOpen_iff_of_cover (fun n ↦ (stableStage x n).isOpen) (hStableStageExhaustive x)]
      apply forall_congr'
      intro n
      rw [← Subtype.image_preimage_val]
      exact (stableStage x n).isOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.symm
    have hStableOpenLeafImmersion (i : stableIndex) (U : Opens (stableLeaf i)) :
        Manifold.IsImmersion 𝓘(ℝ, Fin (stableRank i) → ℝ) 𝓘(ℝ, E) ∞
          (fun p : U ↦ p.val.val) := by
      let h := (stableNativeLeaf i).immersion
      refine ⟨h.complement, inferInstance, inferInstance, ?_⟩
      intro p
      let hc := h.isImmersionOfComplement_complement p.val
      let a := hc.domChart.subtypeRestr (s := U) ⟨p⟩
      have ha : a ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (stableRank i) → ℝ) ∞ U := by
        apply a.mem_maximalAtlas_of_contMDiffOn
        · have hv : ContMDiff 𝓘(ℝ, Fin (stableRank i) → ℝ)
              𝓘(ℝ, Fin (stableRank i) → ℝ) ∞ (Subtype.val : U → stableLeaf i) :=
            contMDiff_subtype_val
          have hh := (contMDiffOn_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas).comp
              (hv.contMDiffOn (s := a.source)) (fun q hq ↦ by
                rw [show a.source = (Subtype.val : U → stableLeaf i) ⁻¹' hc.domChart.source
                  from hc.domChart.subtypeRestr_source ⟨p⟩] at hq
                exact hq)
          exact hh.congr (fun z hz ↦ rfl)
        · have hi := (contMDiffOn_symm_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas).mono
            (hc.domChart.subtypeRestr_target_subset (s := U) ⟨p⟩)
          have hi' : ContMDiffOn 𝓘(ℝ, Fin (stableRank i) → ℝ)
              𝓘(ℝ, Fin (stableRank i) → ℝ) ∞ (Subtype.val ∘ a.symm) a.target :=
            hi.congr (fun z hz ↦ hc.domChart.subtypeRestr_symm_apply ⟨p⟩ hz)
          intro z hz
          exact (ContMDiffWithinAt.subtypeVal_comp_iff U a.symm a.target z).mp (hi' z hz)
      apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
        (hc.continuousAt.comp continuous_subtype_val.continuousAt) hc.equiv a hc.codChart
        (by
          rw [show a.source = (Subtype.val : U → stableLeaf i) ⁻¹' hc.domChart.source
            from hc.domChart.subtypeRestr_source ⟨p⟩]
          exact hc.mem_domChart_source)
        hc.mem_codChart_source ha hc.codChart_mem_maximalAtlas
      intro z hz
      have hz' : z ∈ a.target := by
        simpa only [OpenPartialHomeomorph.extend_target, mfld_simps] using hz
      have hzbase : z ∈ (hc.domChart.extend 𝓘(ℝ, Fin (stableRank i) → ℝ)).target := by
        simpa only [OpenPartialHomeomorph.extend_target, mfld_simps] using
          hc.domChart.subtypeRestr_target_subset (s := U) ⟨p⟩ hz'
      have hh := hc.writtenInCharts hzbase
      have hinv : (a.symm z).val = hc.domChart.symm z :=
        hc.domChart.subtypeRestr_symm_apply (U := U) ⟨p⟩ hz'
      simpa only [OpenPartialHomeomorph.extend, mfld_simps, Function.comp_def, hinv] using hh
    have hStableStageEmbedding (x : X) (n : ℕ) : Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin (stableRank (stableLabel x)) → ℝ) 𝓘(ℝ, E) ∞
        (fun q : stableStage x n ↦ q.val.val) := by
      refine ⟨hStableOpenLeafImmersion _ _, ?_⟩
      have he := ((realIterate 𝓘(ℝ, E) f.symm n).toHomeomorph.isEmbedding.comp
        (hStableSourceEmbedding ((f : X → X)^[n] x))).comp
        (stableStageChart x n).symm.toHomeomorph.isEmbedding
      have hfun : ((realIterate 𝓘(ℝ, E) f.symm n) ∘
          stableSourceMap ((f : X → X)^[n] x)) ∘ (stableStageChart x n).symm =
          (fun q : stableStage x n ↦ q.val.val) := by
        funext q
        change (f.symm : X → X)^[n] (stableSourceMap ((f : X → X)^[n] x)
          ((stableStageChart x n).symm q)) = q.val.val
        rw [← hStableStageFactorization, Diffeomorph.apply_symm_apply]
      exact hfun ▸ he
    let stableSourceStages : NativeSourcePlaqueStages
        (fun i ↦ (stablePartition.leaf i).inclusion) stableLabel f stableSourceDisc stableSourceMap := {
      label_capture := fun _ q ↦ q.property
      center := stableSourceCenter
      center_zero := fun _ ↦ rfl
      sourceDisc_connected := hStableSourceConnected
      nativePlaque := stableNativePlaque
      nativeChart := stableNativeChart
      native_factorization := fun _ _ ↦ rfl
      centered := hStableSourceCentered
      source_embedding := hStableSourceSmoothEmbedding
      trapped := hStableSourceTrapped
      stage := stableStage
      stage_zero := hStableStageZero
      stageChart := stableStageChart
      stage_factorization := hStableStageFactorization
      stage_image := hStableStageImage
      increasing := hStableStageIncreasing
      exhaustive := hStableStageExhaustive
      stage_embedding := hStableStageEmbedding
      topology_generated := hStableStageTopology }
    have hStablePlaqueTangent (p : X) (y : S.stable.toDistribution p)
        (hy : ν p y.val < plaqueRadius) :
        (mfderiv 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) (stablePlaque p) y).range =
          S.stable.toDistribution (stablePlaque p y) := by
      let q := stablePlaque p y
      let k := stableCoordinate q ∘ stablePlaque p
      have hk0 : k y = 0 := by
        change ((merge q).symm (localLog q q)).2 = 0
        rw [(hLogDiagonal q).2, map_zero]
        rfl
      have hyopen := (hStableDiscOpen p).mem_nhds hy
      have hqzero : ν q (0 : S.stable.toDistribution q).val < plaqueRadius := by
        simpa only [Submodule.coe_zero, hνzero] using hPlaqueRadius
      have hqopen := (hStableDiscOpen q).mem_nhds hqzero
      have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, S.stable.toDistribution q) ∞
          (stableCoordinate q) q :=
        (hStableCoordinateSmooth q).contMDiffAt
          ((logDomain.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds
            (hLogDiagonal q).1)
      have hk : ContMDiffAt 𝓘(ℝ, S.stable.toDistribution p)
          𝓘(ℝ, S.stable.toDistribution q) 1 k y :=
        (hc.of_le (by simp)).comp y ((hStablePlaqueC1 p).contMDiffAt hyopen)
      have hg : MDifferentiableAt 𝓘(ℝ, S.stable.toDistribution q) 𝓘(ℝ, E)
          (stablePlaque q) (k y) := by
        rw [hk0]
        exact ((hStablePlaqueC1 q).contMDiffAt hqopen).mdifferentiableAt (by simp)
      have hle := mfderiv_range_le_of_local_factorization (stablePlaque p) (stablePlaque q)
        k y hg (hk.mdifferentiableAt (by simp))
        ((hStableSelfCoherence p y hy).mono (fun _ h ↦ h.1))
      rw [hk0] at hle
      have hzeroRange :
          (mfderiv 𝓘(ℝ, S.stable.toDistribution q) 𝓘(ℝ, E) (stablePlaque q) 0).range =
            S.stable.toDistribution q := by
        ext v
        constructor
        · rintro ⟨w, rfl⟩
          exact Eq.mpr (congrArg (fun v : TangentSpace 𝓘(ℝ, E) q ↦
            v ∈ S.stable.toDistribution q) (hStablePlaqueDerivativeZero q w)) w.property
        · intro hv
          exact ⟨⟨v, hv⟩, hStablePlaqueDerivativeZero q ⟨v, hv⟩⟩
      rw [hzeroRange] at hle
      apply Submodule.eq_of_le_of_finrank_eq hle
      exact (LinearMap.finrank_range_of_inj
        ((hStablePlaqueImmersion p y hy).mfderiv_injective (by simp))).trans
          (hStableRank p y hy).symm
  
    let stableFamilyFrame (x : X) (p : (as'.chart x).baseSet) :
        (Fin (as'.rank x) → ℝ) ≃L[ℝ] S.stable.toDistribution p.val :=
      (EuclideanSpace.equiv (Fin (as'.rank x)) ℝ).symm.trans
        (as'.coordinates x p.val p.property).symm
    have hStableFamilyFrameContinuous (x : X) : Continuous
        (fun z : (as'.chart x).baseSet × (Fin (as'.rank x) → ℝ) ↦
          (⟨z.1.val, stableFamilyFrame x z.1 z.2⟩ :
            Sigma fun p ↦ S.stable.toDistribution p)) := by
      exact (atlas_frame_continuous as' x).comp
        (continuous_fst.prodMk
          ((EuclideanSpace.equiv (Fin (as'.rank x)) ℝ).symm.continuous.comp continuous_snd))
    have hStableFamilyLocalDomain (x : X) :
        ∃ (U : Opens (as'.chart x).baseSet) (R : ℝ),
          (⟨x, as'.mem_baseSet x⟩ : (as'.chart x).baseSet) ∈ U ∧ 0 < R ∧
          ∀ (p : U) (v : Fin (as'.rank x) → ℝ), v ∈ Metric.ball 0 R →
            ν p.val.val (stableFamilyFrame x p.val v).val < plaqueRadius ∧
            stablePlaque p.val.val (stableFamilyFrame x p.val v) ∈
              (extChartAt 𝓘(ℝ, E) x).source := by
      let b : (as'.chart x).baseSet := ⟨x, as'.mem_baseSet x⟩
      let J (z : (as'.chart x).baseSet × (Fin (as'.rank x) → ℝ)) :=
        (⟨z.1.val, stableFamilyFrame x z.1 z.2⟩ :
          Sigma fun p ↦ S.stable.toDistribution p)
      let O : Set ((as'.chart x).baseSet × (Fin (as'.rank x) → ℝ)) :=
        {z | ν z.1.val (stableFamilyFrame x z.1 z.2).val < plaqueRadius}
      have hO : IsOpen O := isOpen_lt (hcS.comp (hStableFamilyFrameContinuous x)) continuous_const
      have hb : (b, 0) ∈ O := by
        change ν x (stableFamilyFrame x b 0).val < plaqueRadius
        rw [map_zero, Submodule.coe_zero, hνzero]
        exact hPlaqueRadius
      have hP : ContinuousAt (fun z ↦ stablePlaque (J z).1 (J z).2) (b, 0) :=
        ((hStablePlaqueContinuous.comp (hStableFamilyFrameContinuous x).continuousOn
          (fun z hz ↦ hz) : ContinuousOn
            (fun z ↦ stablePlaque (J z).1 (J z).2) O).continuousAt (hO.mem_nhds hb))
      have hP0 : stablePlaque (J (b, 0)).1 (J (b, 0)).2 = x := by
        change stablePlaque x (stableFamilyFrame x b 0) = x
        rw [map_zero, hStablePlaqueZero]
      obtain ⟨U, hU, hbU, R, hR, hUR⟩ := exists_local_product_ball_g4 b 0
        (fun z ↦ ν z.1.val (stableFamilyFrame x z.1 z.2).val)
        (fun z ↦ stablePlaque (J z).1 (J z).2) plaqueRadius
        (extChartAt 𝓘(ℝ, E) x).source
        (hcS.comp (hStableFamilyFrameContinuous x)).continuousAt hP hb
        (isOpen_extChartAt_source x) (by rw [hP0]; exact mem_extChartAt_source x)
      exact ⟨⟨U, hU⟩, R, hbU, hR, fun p v hv ↦ hUR p.val p.property v hv⟩
    have hStableReparamDerivative (p : X) (d : ℕ)
        (A : (Fin d → ℝ) ≃L[ℝ] S.stable.toDistribution p)
        (v : Fin d → ℝ) (hv : ν p (A v).val < plaqueRadius) :
        mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) (fun w ↦ stablePlaque p (A w)) v =
          (mfderiv 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E) (stablePlaque p) (A v)).comp
            A.toContinuousLinearMap := by
      exact mfderiv_linear_plaque_reparam A (stablePlaque p) v
        (((hStablePlaqueSmooth p).contMDiffAt
          ((hStableDiscOpen p).mem_nhds hv)).mdifferentiableAt (by simp))
    have hStableReparamEmbedding (p : X) (d : ℕ)
        (A : (Fin d → ℝ) ≃L[ℝ] S.stable.toDistribution p)
        (R : ℝ) (hR : ∀ v ∈ Metric.ball 0 R, ν p (A v).val < plaqueRadius) :
        IsEmbedding (fun v : Metric.ball (0 : Fin d → ℝ) R ↦ stablePlaque p (A v.val)) := by
      let B := stableModelEquiv (stableLabel p) ⟨p, rfl⟩
      let L := A.trans B.symm
      let Q : Metric.ball (0 : Fin d → ℝ) R → stableSourceDisc p := fun v ↦
        ⟨L v.val, by
          change ν p (B (B.symm (A v.val))).val < plaqueRadius
          rw [B.apply_symm_apply]
          exact hR v.val v.property⟩
      have hQ : Continuous Q :=
        (L.continuous.comp continuous_subtype_val).subtype_mk _
      have heQ : IsEmbedding Q := IsEmbedding.of_comp hQ continuous_subtype_val
        (L.toHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal)
      have hfun : stableSourceMap p ∘ Q =
          (fun v : Metric.ball (0 : Fin d → ℝ) R ↦ stablePlaque p (A v.val)) := by
        funext v
        rw [Function.comp_apply, hStableSourceFormula]
        exact congrArg (stablePlaque p) (B.apply_symm_apply (A v.val))
      exact hfun ▸ ((hStableSourceEmbedding p).comp heQ)
    let stableReparamPlaque (p : X) (d : ℕ)
        (A : (Fin d → ℝ) ≃L[ℝ] S.stable.toDistribution p)
        (R : ℝ) (hRpos : 0 < R)
        (hR : ∀ v ∈ Metric.ball 0 R, ν p (A v).val < plaqueRadius) :
        NativeEmbeddedPlaque 𝓘(ℝ, E) (V := Fin d → ℝ) S.stable.toDistribution p := {
      domain := Metric.ball 0 R
      domain_open := Metric.isOpen_ball
      zero_mem := Metric.mem_ball_self hRpos
      param := fun v ↦ stablePlaque p (A v)
      centered := by rw [map_zero, hStablePlaqueZero]
      smooth := (hStablePlaqueSmooth p).comp A.contDiff.contMDiff.contMDiffOn hR
      embedded := hStableReparamEmbedding p d A R hR
      immersed := by
        intro v hv
        rw [hStableReparamDerivative p d A v (hR v hv)]
        exact ((hStablePlaqueImmersion p (A v) (hR v hv)).mfderiv_injective (by simp)).comp
          A.injective
      tangent := by
        set_option backward.isDefEq.respectTransparency false in
        intro v hv
        rw [hStableReparamDerivative p d A v (hR v hv)]
        change LinearMap.range ((mfderiv 𝓘(ℝ, S.stable.toDistribution p) 𝓘(ℝ, E)
          (stablePlaque p) (A v)).toLinearMap.comp A.toLinearMap) = _
        rw [LinearMap.range_comp_of_range_eq_top _ A.toLinearEquiv.range]
        exact hStablePlaqueTangent p (A v) (hR v hv) }
  
    -- Restrict the source chart to the common framed ball. This retains the
    -- intrinsic smooth chart, rather than only the ambient embedded parametrization.
    let stableReparamReceiving (p : X) (d : ℕ)
        (A : (Fin d → ℝ) ≃L[ℝ] S.stable.toDistribution p) (R : ℝ) :
        Opens (stableLeaf (stableLabel p)) :=
      let B := stableModelEquiv (stableLabel p) ⟨p, rfl⟩
      let L := A.trans B.symm
      let c := stableCenteredChart p
      ⟨c.source ∩ c ⁻¹' (L.symm ⁻¹' Metric.ball 0 R),
        c.isOpen_inter_preimage (Metric.isOpen_ball.preimage L.symm.continuous)⟩
    let stableReparamChart (p : X) (d : ℕ)
        (A : (Fin d → ℝ) ≃L[ℝ] S.stable.toDistribution p)
        (R : ℝ) (hR : ∀ v ∈ Metric.ball 0 R, ν p (A v).val < plaqueRadius) :
        Diffeomorph 𝓘(ℝ, Fin d → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel p)) → ℝ)
          (⟨Metric.ball 0 R, Metric.isOpen_ball⟩ : Opens (Fin d → ℝ))
          (stableReparamReceiving p d A R) ∞ := by
      let B := stableModelEquiv (stableLabel p) ⟨p, rfl⟩
      let L := A.trans B.symm
      let c := stableCenteredChart p
      have hsmall (v : Metric.ball (0 : Fin d → ℝ) R) : L v.val ∈ c.target := by
        change ν p (B (B.symm (A v.val))).val < plaqueRadius
        rw [B.apply_symm_apply]
        exact hR v.val v.property
      exact {
        toEquiv := {
          toFun := fun v ↦ ⟨c.symm (L v.val), by
            change c.symm (L v.val) ∈ c.source ∩ c ⁻¹' (L.symm ⁻¹' Metric.ball 0 R)
            refine ⟨c.map_target (hsmall v), ?_⟩
            change L.symm (c (c.symm (L v.val))) ∈ Metric.ball 0 R
            rw [c.right_inv (hsmall v), L.symm_apply_apply]
            exact v.property⟩
          invFun := fun q ↦ ⟨L.symm (c q.val), q.property.2⟩
          left_inv := by
            intro v
            apply Subtype.ext
            exact (congrArg L.symm (c.right_inv (hsmall v))).trans (L.symm_apply_apply v.val)
          right_inv := by
            intro q
            apply Subtype.ext
            change c.symm (L (L.symm (c q.val))) = q.val
            rw [L.apply_symm_apply]
            exact c.left_inv q.property.1 }
        contMDiff_toFun := by
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact contMDiffOn_chart_symm.comp_contMDiff
            (L.contDiff.contMDiff.comp contMDiff_subtype_val) hsmall
        contMDiff_invFun := by
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact L.symm.contDiff.contMDiff.comp
            ((contMDiffOn_chart (I := 𝓘(ℝ, Fin (stableRank (stableLabel p)) → ℝ))
              (x := (⟨p, rfl⟩ : stableLeaf (stableLabel p)))).comp_contMDiff
                contMDiff_subtype_val (fun q ↦ q.property.1)) }
    have hStableReparamFactorization (p : X) (d : ℕ)
        (A : (Fin d → ℝ) ≃L[ℝ] S.stable.toDistribution p)
        (R : ℝ) (hR : ∀ v ∈ Metric.ball 0 R, ν p (A v).val < plaqueRadius)
        (v : Metric.ball (0 : Fin d → ℝ) R) :
        ((stableReparamChart p d A R hR v).val).val = stablePlaque p (A v.val) := by
      change (leafPlaque (stableLabel p) ⟨p, rfl⟩
        ((stableModelEquiv (stableLabel p) ⟨p, rfl⟩)
          ((stableModelEquiv (stableLabel p) ⟨p, rfl⟩).symm (A v.val)))).val = _
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hLeafPlaque (stableLabel p) ⟨p, rfl⟩ (A v.val) (hR v.val v.property)

    choose stableFamilyPatch stableFamilyRadius hStableFamilyCenter
      hStableFamilyRadius hStableFamilySmall using hStableFamilyLocalDomain
    let stableFamilyDomain (x : X) : Opens X :=
      ⟨Subtype.val '' (stableFamilyPatch x : Set (as'.chart x).baseSet),
        (as'.chart x).open_baseSet.isOpenMap_subtype_val _ (stableFamilyPatch x).isOpen⟩
    have hStableFamilyCenterMem (x : X) : x ∈ stableFamilyDomain x :=
      ⟨⟨x, as'.mem_baseSet x⟩, hStableFamilyCenter x, rfl⟩
    let stableFamilyBase (x : X) (p : stableFamilyDomain x) : (as'.chart x).baseSet :=
      ⟨p.val, by rcases p.property with ⟨q, hq, heq⟩; exact heq ▸ q.property⟩
    have hStableFamilyBaseMem (x : X) (p : stableFamilyDomain x) :
        stableFamilyBase x p ∈ stableFamilyPatch x := by
      rcases p.property with ⟨q, hq, heq⟩
      have he : stableFamilyBase x p = q := Subtype.ext heq.symm
      rw [he]
      exact hq
    let stableFamilyLinearFrame (x : X) (p : stableFamilyDomain x) :=
      stableFamilyFrame x (stableFamilyBase x p)
    have hStableFamilyLinearFrameContinuous (x : X) : Continuous
        (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          (⟨z.1.val, (stableFamilyLinearFrame x z.1 z.2).val⟩ : TangentBundle 𝓘(ℝ, E) X)) := by
      have hb : Continuous (stableFamilyBase x) := continuous_subtype_val.subtype_mk _
      have hc := (hStableFamilyFrameContinuous x).comp (hb.prodMap continuous_id)
      exact (show Continuous (fun z : Sigma fun p ↦ S.stable.toDistribution p ↦
        (⟨z.1, z.2.val⟩ : TangentBundle 𝓘(ℝ, E) X)) from continuous_induced_dom).comp hc
    have hStableFamilySmallAmbient (x : X) (p : stableFamilyDomain x)
        (v : Fin (as'.rank x) → ℝ) (hv : v ∈ Metric.ball 0 (stableFamilyRadius x)) :
        ν p.val (stableFamilyLinearFrame x p v).val < plaqueRadius ∧
          stablePlaque p.val (stableFamilyLinearFrame x p v) ∈
            (extChartAt 𝓘(ℝ, E) x).source :=
      hStableFamilySmall x ⟨stableFamilyBase x p, hStableFamilyBaseMem x p⟩ v hv
    let stableFamilyPlaque (x : X) (p : stableFamilyDomain x) :
        NativeEmbeddedPlaque 𝓘(ℝ, E) (V := Fin (as'.rank x) → ℝ)
          S.stable.toDistribution p.val :=
      stableReparamPlaque p.val (as'.rank x) (stableFamilyLinearFrame x p)
        (stableFamilyRadius x) (hStableFamilyRadius x)
        (fun v hv ↦ (hStableFamilySmallAmbient x p v hv).1)
    have hStableFamilyJointContinuous (x : X) : Continuous
        (fun z : stableFamilyDomain x × Metric.ball (0 : Fin (as'.rank x) → ℝ)
          (stableFamilyRadius x) ↦ (stableFamilyPlaque x z.1).param z.2.val) := by
      have hb : Continuous (stableFamilyBase x) := continuous_subtype_val.subtype_mk _
      have hc := (hStableFamilyFrameContinuous x).comp
        (hb.prodMap (continuous_subtype_val (p := fun v : Fin (as'.rank x) → ℝ ↦
          v ∈ Metric.ball 0 (stableFamilyRadius x))))
      exact hStablePlaqueContinuous.comp_continuous hc
        (fun z ↦ (hStableFamilySmallAmbient x z.1 z.2.val z.2.property).1)
    have hStableFamilyCoordinateSmooth (x : X) (p : stableFamilyDomain x) :
        ContDiffOn ℝ ∞
          (fun v ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p).param v))
          (Metric.ball (0 : Fin (as'.rank x) → ℝ) (stableFamilyRadius x)) := by
      rw [← contMDiffOn_iff_contDiffOn]
      exact (contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := x)).comp (stableFamilyPlaque x p).smooth
        (fun v hv ↦ by
          change stablePlaque p.val (stableFamilyLinearFrame x p v) ∈ (chartAt E x).source
          simpa only [extChartAt_source] using (hStableFamilySmallAmbient x p v hv).2)

    have hStableFamilyGraphJetEvaluation (x : X) (m : ℕ)
        (w : Fin m → (Fin (as'.rank x) → ℝ)) : Continuous
        (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          (⟨z.1.val, iteratedFDeriv ℝ m
            (fun v ↦ stableGraph z.1.val (stableFamilyLinearFrame x z.1 v)) z.2 w⟩ :
              Sigma fun p ↦ S.unstable.toDistribution p)) := by
      have hb : Continuous (stableFamilyBase x) := continuous_subtype_val.subtype_mk _
      have hf := (hStableFamilyFrameContinuous x).comp (hb.prodMap continuous_id)
      have hw (i : Fin m) : Continuous
          (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
            (⟨z.1.val, stableFamilyLinearFrame x z.1 (w i)⟩ :
              Sigma fun p ↦ S.stable.toDistribution p)) :=
        (hStableFamilyFrameContinuous x).comp
          ((hb.comp continuous_fst).prodMk continuous_const)
      have hj := parameter_graph_joint_jet_evaluation_continuous as' au id continuous_id
        stableGraph (m + 1) m (Nat.le_succ m) ((hGraphsRegular (m + 1) (by omega)).2)
        (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦ z.1.val)
        (continuous_subtype_val.comp continuous_fst)
        (fun z ↦ stableFamilyLinearFrame x z.1 z.2) hf
        (fun z i ↦ stableFamilyLinearFrame x z.1 (w i)) hw
      apply hj.congr
      intro z
      congr 1
      have he := (stableFamilyLinearFrame x z.1).toContinuousLinearMap.iteratedFDeriv_comp_right
        (hStableGraphSmooth z.1.val) z.2 (i := m) (by simp)
      exact congrArg (fun L ↦ L w) he.symm

    have hStableFamilyFrameJetEvaluation (x : X) (m : ℕ)
        (w : Fin m → (Fin (as'.rank x) → ℝ)) : Continuous
        (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          (⟨z.1.val, iteratedFDeriv ℝ m
            (stableFamilyLinearFrame x z.1) z.2 w⟩ :
              Sigma fun p ↦ S.stable.toDistribution p)) := by
      have hb : Continuous (stableFamilyBase x) := continuous_subtype_val.subtype_mk _
      rcases m with _ | m
      · simp only [iteratedFDeriv_zero_apply]
        convert (hStableFamilyFrameContinuous x).comp (hb.prodMap continuous_id) using 1
        rfl
      · rcases m with _ | m
        · have hc := (hStableFamilyFrameContinuous x).comp
            ((hb.comp (continuous_fst (X := stableFamilyDomain x)
              (Y := Fin (as'.rank x) → ℝ))).prodMk (continuous_const (y := w 0)))
          apply hc.congr
          intro z
          congr 1
          simp only [iteratedFDeriv_succ_apply_right, iteratedFDeriv_zero_apply,
            ContinuousLinearEquiv.fderiv]
          rfl
        · have hc := parameter_graph_atlas_zero_continuous as'
            (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦ z.1.val)
            (continuous_subtype_val.comp continuous_fst)
          apply hc.congr
          intro z
          congr 1
          simp [iteratedFDeriv_succ_apply_right, ContinuousLinearEquiv.fderiv,
            iteratedFDeriv_succ_const]
    let stableFamilyLift (x : X) (p : stableFamilyDomain x)
        (v : Fin (as'.rank x) → ℝ) : TangentSpace 𝓘(ℝ, E) p.val :=
      merge p.val (stableGraph p.val (stableFamilyLinearFrame x p v),
        stableFamilyLinearFrame x p v)
    have hStableFamilyLiftSmooth (x : X) (p : stableFamilyDomain x) :
        ContDiff ℝ ∞ (stableFamilyLift x p) :=
      (merge p.val).contDiff.comp
        (((hStableGraphSmooth p.val).comp (stableFamilyLinearFrame x p).contDiff).prodMk
          (stableFamilyLinearFrame x p).contDiff)
    have hStableFamilyLiftJetEvaluation (x : X) (m : ℕ)
        (w : Fin m → (Fin (as'.rank x) → ℝ)) : Continuous
        (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          (⟨z.1.val, iteratedFDeriv ℝ m (stableFamilyLift x z.1) z.2 w⟩ :
            TangentBundle 𝓘(ℝ, E) X)) := by
      set_option backward.isDefEq.respectTransparency true in
      have hpair : Continuous
          (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
            (⟨z.1.val,
              (iteratedFDeriv ℝ m (fun v ↦ stableGraph z.1.val
                (stableFamilyLinearFrame x z.1 v)) z.2 w,
                iteratedFDeriv ℝ m (stableFamilyLinearFrame x z.1) z.2 w)⟩ :
                  Sigma fun p ↦ S.unstable.toDistribution p × S.stable.toDistribution p)) :=
        continuous_induced_rng.mpr
          ((hStableFamilyGraphJetEvaluation x m w).prodMk
            (hStableFamilyFrameJetEvaluation x m w))
      have hc := hmerge.comp hpair
      apply hc.congr
      intro z
      dsimp only [Function.comp_apply]
      congr 1
      symm
      change iteratedFDeriv ℝ m
        ((merge z.1.val).toContinuousLinearMap ∘
          (fun v ↦ (stableGraph z.1.val (stableFamilyLinearFrame x z.1 v),
            stableFamilyLinearFrame x z.1 v))) z.2 w = _
      have hleft := (merge z.1.val).iteratedFDeriv_comp_left
        (f := fun v ↦ (stableGraph z.1.val (stableFamilyLinearFrame x z.1 v),
          stableFamilyLinearFrame x z.1 v)) (x := z.2) (i := m)
      have hprod : iteratedFDeriv ℝ m
          (fun v ↦ (stableGraph z.1.val (stableFamilyLinearFrame x z.1 v),
            stableFamilyLinearFrame x z.1 v)) z.2 =
          (iteratedFDeriv ℝ m
            (fun v ↦ stableGraph z.1.val (stableFamilyLinearFrame x z.1 v)) z.2).prod
            (iteratedFDeriv ℝ m (stableFamilyLinearFrame x z.1) z.2) := by
        apply iteratedFDeriv_prodMk (n := ∞) (i := m)
        · exact ((hStableGraphSmooth z.1.val).comp
            (stableFamilyLinearFrame x z.1).contDiff).contDiffAt
        · exact (stableFamilyLinearFrame x z.1).contDiff.contDiffAt
        · simp
      exact (congrArg (fun L ↦ L w) hleft).trans
        (congrArg (fun L ↦ merge z.1.val (L w)) hprod)

    let stableFamilyTangentCoordinates (x y : X) (p : stableFamilyDomain x)
        (v : Fin (as'.rank x) → ℝ) : E :=
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearMapAt ℝ p.val
        (stableFamilyLift x p v)
    have hStableFamilyTangentCoordinatesSmooth (x y : X) (p : stableFamilyDomain x) :
        ContDiff ℝ ∞ (stableFamilyTangentCoordinates x y p) :=
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearMapAt ℝ p.val).contDiff.comp
        (hStableFamilyLiftSmooth x p)
    have hStableFamilyTangentCoordinateJets (x y : X) (m : ℕ) :
        ContinuousOn (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          iteratedFDeriv ℝ m (stableFamilyTangentCoordinates x y z.1) z.2)
          {z | z.1.val ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).baseSet} := by
      let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) y
      rw [continuousOn_iff_continuous_domRestrict]
      apply parameter_graph_multilinear_continuous_of_eval
      intro w
      have hj := (hStableFamilyLiftJetEvaluation x m w).comp
        (continuous_subtype_val (p := fun z : stableFamilyDomain x ×
          (Fin (as'.rank x) → ℝ) ↦ z.1.val ∈ e.baseSet))
      have hc := (e.continuousOn.comp_continuous hj
        (fun z ↦ e.mem_source.mpr z.property)).snd
      apply hc.congr
      intro z
      have he := (e.continuousLinearMapAt ℝ z.val.1.val).iteratedFDeriv_comp_left
        ((hStableFamilyLiftSmooth x z.val.1).contDiffAt (x := z.val.2)) (i := m) (by simp)
      change (e ⟨z.val.1.val, iteratedFDeriv ℝ m
        (stableFamilyLift x z.val.1) z.val.2 w⟩).2 = _
      rw [← e.continuousLinearMapAt_apply_of_mem ℝ z.property]
      exact (congrArg (fun L ↦ L w) he).symm

    have hExponentialCoordinateSmooth (x : X) (q : TangentBundle 𝓘(ℝ, E) X)
        (hq : q ∈ riemannianExponentialDomain gMetric)
        (hx : riemannianExponential gMetric q ∈ (extChartAt 𝓘(ℝ, E) x).source) :
        ContDiffAt ℝ ∞
          ((extChartAt 𝓘(ℝ, E) x) ∘ riemannianExponential gMetric ∘
            (extChartAt (𝓘(ℝ, E)).tangent q).symm)
          (extChartAt (𝓘(ℝ, E)).tangent q q) := by
      rw [← contMDiffAt_iff_contDiffAt]
      have hExp := (riemannianExponential_open_smooth gMetric).2.contMDiffAt
        ((riemannianExponential_open_smooth gMetric).1.mem_nhds hq)
      have hχ := (contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := x) (n := ∞)).contMDiffAt
        ((chartAt E x).open_source.mem_nhds (by simpa only [extChartAt_source] using hx))
      have hc := (contMDiffOn_extChartAt_symm (I := (𝓘(ℝ, E)).tangent) (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target q).mem_nhds
          ((extChartAt (𝓘(ℝ, E)).tangent q).map_source (mem_extChartAt_source q)))
      have he := hχ.comp q hExp
      have he' : ContMDiffAt (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞
          ((extChartAt 𝓘(ℝ, E) x) ∘ riemannianExponential gMetric)
          ((extChartAt (𝓘(ℝ, E)).tangent q).symm (extChartAt (𝓘(ℝ, E)).tangent q q)) := by
        simpa only [(extChartAt (𝓘(ℝ, E)).tangent q).left_inv (mem_extChartAt_source q)] using he
      exact he'.comp (extChartAt (𝓘(ℝ, E)).tangent q q) hc

    let stableFamilyChartCoordinates (x y : X) (p : stableFamilyDomain x)
        (v : Fin (as'.rank x) → ℝ) : E × E :=
      (chartAt E y p.val, stableFamilyTangentCoordinates x y p v)
    have hStableFamilyChartCoordinatesSmooth (x y : X) (p : stableFamilyDomain x) :
        ContDiff ℝ ∞ (stableFamilyChartCoordinates x y p) :=
      contDiff_const.prodMk (hStableFamilyTangentCoordinatesSmooth x y p)
    have hStableFamilyChartCoordinateJets (x y : X) (m : ℕ) :
        ContinuousOn (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          iteratedFDeriv ℝ m (stableFamilyChartCoordinates x y z.1) z.2)
          {z | z.1.val ∈ (chartAt E y).source} := by
      have hopen : IsOpen {z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) |
          z.1.val ∈ (chartAt E y).source} :=
        (chartAt E y).open_source.preimage (continuous_subtype_val.comp continuous_fst)
      apply continuousOn_parametric_jet_prodMk
        (fun p : stableFamilyDomain x ↦ fun _ : Fin (as'.rank x) → ℝ ↦ chartAt E y p.val)
        (stableFamilyTangentCoordinates x y) _ hopen m
        (fun _ ↦ contDiff_const.contDiffOn)
        (fun p ↦ (hStableFamilyTangentCoordinatesSmooth x y p).of_le (by simp) |>.contDiffOn)
      · rcases m with _ | m
        · have hb : ContinuousOn (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
              chartAt E y z.1.val) {z | z.1.val ∈ (chartAt E y).source} :=
            (chartAt E y).continuousOn.comp
              (continuous_subtype_val.comp continuous_fst).continuousOn (fun z hz ↦ hz)
          have hc := (continuousMultilinearCurryFin0 ℝ (Fin (as'.rank x) → ℝ) E).symm.continuous
            |>.comp_continuousOn hb
          apply hc.congr
          intro z hz
          ext w
          simp only [iteratedFDeriv_zero_apply, continuousMultilinearCurryFin0_symm_apply_apply,
            Function.comp_apply]
        · simpa only [iteratedFDeriv_succ_const, Pi.zero_apply] using
            (continuous_const (y := (0 : ContinuousMultilinearMap ℝ
              (fun _ : Fin (m + 1) ↦ Fin (as'.rank x) → ℝ) E))).continuousOn
      · exact hStableFamilyTangentCoordinateJets x y m

    have hStableFamilyChartCoordinates_eq (x y : X) (p : stableFamilyDomain x)
        (hp : p.val ∈ (chartAt E y).source) (v : Fin (as'.rank x) → ℝ) :
        stableFamilyChartCoordinates x y p v =
          extChartAt (𝓘(ℝ, E)).tangent (⟨y, 0⟩ : TangentBundle 𝓘(ℝ, E) X)
            ⟨p.val, stableFamilyLift x p v⟩ := by
      let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) y
      change (chartAt E y p.val, e.continuousLinearMapAt ℝ p.val (stableFamilyLift x p v)) =
        (chartAt E y (e ⟨p.val, stableFamilyLift x p v⟩).1,
          (e ⟨p.val, stableFamilyLift x p v⟩).2)
      rw [show (e ⟨p.val, stableFamilyLift x p v⟩).1 = p.val from rfl]
      exact congrArg (fun v ↦ (chartAt E y p.val, v))
        (e.continuousLinearMapAt_apply_of_mem ℝ hp _)

    have hStableFamilyCoordinateJets (x : X) (m : ℕ) :
        ContinuousOn (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          iteratedFDeriv ℝ m
            (fun v ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param v)) z.2)
          (univ ×ˢ Metric.ball 0 (stableFamilyRadius x)) := by
      intro z₀ hz₀
      let q₀ : TangentBundle 𝓘(ℝ, E) X := ⟨z₀.1.val, stableFamilyLift x z₀.1 z₀.2⟩
      let c := extChartAt (𝓘(ℝ, E)).tangent q₀
      let H := stableFamilyChartCoordinates x z₀.1.val
      let G := (extChartAt 𝓘(ℝ, E) x) ∘ riemannianExponential gMetric ∘ c.symm
      let O : Set (stableFamilyDomain x × (Fin (as'.rank x) → ℝ)) :=
        {z | z.1.val ∈ (chartAt E z₀.1.val).source}
      have hO : IsOpen O :=
        (chartAt E z₀.1.val).open_source.preimage (continuous_subtype_val.comp continuous_fst)
      have hzO : z₀ ∈ O := mem_chart_source E z₀.1.val
      have hcoords (p : stableFamilyDomain x) (hp : p.val ∈ (chartAt E z₀.1.val).source)
          (v : Fin (as'.rank x) → ℝ) : H p v = c ⟨p.val, stableFamilyLift x p v⟩ := by
        exact hStableFamilyChartCoordinates_eq x z₀.1.val p hp v
      have hcO : ContinuousOn (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
          H z.1 z.2) O := by
        have hc := (continuous_eval_const (0 : Fin 0 → (Fin (as'.rank x) → ℝ))).comp_continuousOn
          (hStableFamilyChartCoordinateJets x z₀.1.val 0)
        simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hc
      have hq : q₀ ∈ riemannianExponentialDomain gMetric := by
        apply (hExpLog z₀.1.val (mem_univ _) _ (hSmallMetric z₀.1.val _ ?_)).1
        change ν z₀.1.val
          (merge z₀.1.val (stableGraph z₀.1.val (stableFamilyLinearFrame x z₀.1 z₀.2),
            stableFamilyLinearFrame x z₀.1 z₀.2)) < plaqueRadius
        rw [hStableGauge]
        exact (hStableFamilySmallAmbient x z₀.1 z₀.2 hz₀.2).1
      have hxq : riemannianExponential gMetric q₀ ∈ (extChartAt 𝓘(ℝ, E) x).source :=
        (hStableFamilySmallAmbient x z₀.1 z₀.2 hz₀.2).2
      have hG : ContDiffAt ℝ ∞ G (H z₀.1 z₀.2) := by
        rw [hcoords z₀.1 hzO z₀.2]
        exact hExponentialCoordinateSmooth x q₀ hq hxq
      obtain ⟨U₀, hU₀, hG₀⟩ := hG.contDiffOn (m := (m : ℕ∞ω)) (by simp) (by simp)
      obtain ⟨U, hUU₀, hU, hHU⟩ := mem_nhds_iff.mp hU₀
      let Ω := O ∩ (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦
        H z.1 z.2) ⁻¹' U
      have hΩ : IsOpen Ω := hcO.isOpen_inter_preimage hO hU
      have hzΩ : z₀ ∈ Ω := ⟨hzO, hHU⟩
      have hcomp := continuousAt_spatial_jet_comp_finite H G Ω hΩ U hU m
        (fun p ↦ ((hStableFamilyChartCoordinatesSmooth x z₀.1.val p).of_le (by simp)).contDiffOn)
        (hG₀.mono hUU₀) (fun z hz ↦ hz.2) z₀ hzΩ
        (hcO.continuousAt (hO.mem_nhds hzO))
        (fun k hk ↦ (hStableFamilyChartCoordinateJets x z₀.1.val k).continuousAt
          (hO.mem_nhds hzO))
      have hsame (p : stableFamilyDomain x) (hp : p.val ∈ (chartAt E z₀.1.val).source) :
          G ∘ H p = fun v ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p).param v) := by
        funext v
        dsimp only [Function.comp_apply, G]
        rw [hcoords p hp v]
        have hs : (⟨p.val, stableFamilyLift x p v⟩ : TangentBundle 𝓘(ℝ, E) X) ∈ c.source := by
          rw [extChartAt_source]
          exact (TangentBundle.mem_chart_source_iff _ _).mpr hp
        rw [c.left_inv hs]
        rfl
      apply (hcomp.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [hO.mem_nhds hzO] with z hz
      rw [hsame z.1 hz]

    have hStableFamilyCoordinateContinuous (x : X) : Continuous
        (fun z : stableFamilyDomain x × Metric.ball (0 : Fin (as'.rank x) → ℝ)
          (stableFamilyRadius x) ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param z.2.val)) :=
      (continuousOn_extChartAt (I := 𝓘(ℝ, E)) x).comp_continuous
        (hStableFamilyJointContinuous x)
        (fun z ↦ (hStableFamilySmallAmbient x z.1 z.2.val z.2.property).2)
    have hStableFamilyJointDerivative (x : X) : Continuous
        (fun z : stableFamilyDomain x × Metric.ball (0 : Fin (as'.rank x) → ℝ)
          (stableFamilyRadius x) ↦ fderiv ℝ
            (fun v ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param v)) z.2.val) := by
      have hj := (hStableFamilyCoordinateJets x 1).comp_continuous
        (continuous_id.prodMap continuous_subtype_val) (fun z ↦ ⟨mem_univ _, z.2.property⟩)
      have hc := (continuousMultilinearCurryFin1 ℝ (Fin (as'.rank x) → ℝ) E).continuous.comp hj
      apply hc.congr
      intro z
      ext v
      simp only [Function.comp_apply, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
      rfl
    have hStableFamilyCompactC1 (x : X) (K : Set (Fin (as'.rank x) → ℝ))
        (hK : IsCompact K) (hKR : K ⊆ Metric.ball 0 (stableFamilyRadius x))
        (p₀ : stableFamilyDomain x) (ε : ℝ) (hε : 0 < ε) :
        ∃ N : Set (stableFamilyDomain x), IsOpen N ∧ p₀ ∈ N ∧ ∀ p ∈ N, ∀ v ∈ K,
          ‖extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p).param v) -
            extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p₀).param v)‖ < ε ∧
          ‖fderiv ℝ (fun u ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p).param u)) v -
            fderiv ℝ (fun u ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p₀).param u)) v‖ < ε := by
      set_option backward.isDefEq.respectTransparency true in
      set_option synthInstance.maxHeartbeats 200000 in
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      let j : K → Metric.ball (0 : Fin (as'.rank x) → ℝ) (stableFamilyRadius x) :=
        fun v ↦ ⟨v.val, hKR v.property⟩
      have hj : Continuous j := continuous_subtype_val.subtype_mk _
      let J : C(stableFamilyDomain x × K, E × ((Fin (as'.rank x) → ℝ) →L[ℝ] E)) := {
        toFun := fun z ↦
          (extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param z.2.val),
            fderiv ℝ (fun u ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param u)) z.2.val)
        continuous_toFun :=
          ((hStableFamilyCoordinateContinuous x).comp (continuous_id.prodMap hj)).prodMk
            ((hStableFamilyJointDerivative x).comp (continuous_id.prodMap hj)) }
      let O : Set (stableFamilyDomain x × K) :=
        {z | ‖J z - J (p₀, z.2)‖ < ε}
      have hO : IsOpen O := isOpen_lt
        (J.continuous.sub (J.continuous.comp (continuous_const.prodMk continuous_snd))).norm
        continuous_const
      have hbase : ({p₀} : Set (stableFamilyDomain x)) ×ˢ (Set.univ : Set K) ⊆ O := by
        rintro ⟨p, v⟩ ⟨hp, _⟩
        have hp' : p = p₀ := hp
        subst p
        simpa only [O, mem_ofPred_eq, sub_self, norm_zero] using hε
      obtain ⟨U, V, hU, _, hpU, hKV, hUV⟩ :=
        generalized_tube_lemma isCompact_singleton isCompact_univ hO hbase
      refine ⟨U, hU, hpU (mem_singleton p₀), ?_⟩
      intro p hp v hv
      let vk : K := ⟨v, hv⟩
      have hpt : (p, vk) ∈ U ×ˢ V := ⟨hp, hKV (Set.mem_univ vk)⟩
      have hn : ‖J (p, vk) - J (p₀, vk)‖ < ε := hUV hpt
      have hfst := (norm_fst_le (J (p, vk) - J (p₀, vk))).trans_lt hn
      have hsnd := (norm_snd_le (J (p, vk) - J (p₀, vk))).trans_lt hn
      exact ⟨hfst, hsnd⟩
    let stableFamily (x : X) :
        NativePlaqueFamily 𝓘(ℝ, E) (V := Fin (as'.rank x) → ℝ) S.stable.toDistribution x := {
      centerDomain := stableFamilyDomain x
      centerDomain_open := (stableFamilyDomain x).isOpen
      center_mem := hStableFamilyCenterMem x
      radius := stableFamilyRadius x
      radius_pos := hStableFamilyRadius x
      plaque := stableFamilyPlaque x
      domain_eq := fun _ ↦ rfl
      frame := stableFamilyLinearFrame x
      frame_continuous := hStableFamilyLinearFrameContinuous x
      receivingAnchor := x
      receiving_domain := fun p v hv ↦ (hStableFamilySmallAmbient x p v hv).2
      jointly_continuous := hStableFamilyJointContinuous x
      coordinate_smooth := hStableFamilyCoordinateSmooth x
      jointly_continuous_derivative := hStableFamilyJointDerivative x
      compact_C1 := hStableFamilyCompactC1 x }

    let stableClosedJet (x : X) (a : ℝ) (haR : a < stableFamilyRadius x) :
        C(stableFamilyDomain x × Metric.closedBall (0 : Fin (as'.rank x) → ℝ) a,
          E × ((Fin (as'.rank x) → ℝ) →L[ℝ] E)) := by
      let j : Metric.closedBall (0 : Fin (as'.rank x) → ℝ) a →
          Metric.ball (0 : Fin (as'.rank x) → ℝ) (stableFamilyRadius x) :=
        fun v ↦ ⟨v.val, Metric.mem_ball.mpr ((Metric.mem_closedBall.mp v.property).trans_lt haR)⟩
      have hj : Continuous j := continuous_subtype_val.subtype_mk _
      exact {
        toFun := fun z ↦
          (extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param z.2.val),
            fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param v)) z.2.val)
        continuous_toFun :=
          ((hStableFamilyCoordinateContinuous x).comp (continuous_id.prodMap hj)).prodMk
            ((hStableFamilyJointDerivative x).comp (continuous_id.prodMap hj)) }
    let stableFiniteFamily (x : X) :
        FiniteC1NativePlaqueFamily stablePartition x (as'.rank x) := {
      family := stableFamily x
      label := fun p ↦ stableLabel p.val
      receivingPlaque := fun p ↦ stableReparamReceiving p.val (as'.rank x)
        (stableFamilyLinearFrame x p) (stableFamilyRadius x)
      chart := fun p ↦ stableReparamChart p.val (as'.rank x)
        (stableFamilyLinearFrame x p) (stableFamilyRadius x)
        (fun v hv ↦ (hStableFamilySmallAmbient x p v hv).1)
      factorization := fun p v ↦
        (hStableReparamFactorization p.val (as'.rank x)
          (stableFamilyLinearFrame x p) (stableFamilyRadius x)
          (fun v hv ↦ (hStableFamilySmallAmbient x p v hv).1) v).symm
      closedJet := fun a _ haR ↦ (stableClosedJet x a haR).curry
      closedJet_eval := fun _ _ _ _ _ ↦ rfl
      closedJet_continuous := fun a _ haR ↦ (stableClosedJet x a haR).curry.continuous
      compact_center_image := fun a _ haR _ hK ↦
        hK.image (stableClosedJet x a haR).curry.continuous }
    let stableFamilies : SelectedFiniteC1NativePlaqueFamilies stablePartition := {
      dimension := as'.rank
      family := stableFiniteFamily }
    let stableCoherent : SelectedFiniteOrderNativePlaqueFamilies stablePartition := {
      dimension := fun _ ↦ as'.rank
      family := fun _ ↦ stableFiniteFamily
      coherence := fun N x ↦ {
        coordinate := fun p v ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p).param v)
        coordinate_eq := fun _ _ _ ↦ rfl
        coordinate_smooth := hStableFamilyCoordinateSmooth x
        jointly_continuous_derivatives := by
          intro j hj
          have hc := (hStableFamilyCoordinateJets x j).comp_continuous
            (continuous_id.prodMap continuous_subtype_val) (fun z ↦ ⟨mem_univ _, z.2.property⟩)
          apply hc.congr
          intro z
          exact (iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball z.2.property).symm } }

    let stableFamilyGerm (x : X) :
        SelectedFamilyGermRestriction (L := stableLeaf) stableLabel stableSourceDisc
          stableSourceMap stableSourceStages.center (as'.rank x) (stableFamilyDomain x)
          ⟨Metric.ball 0 (stableFamilyRadius x), Metric.isOpen_ball⟩
          (fun z ↦ (stableFamilyPlaque x z.1).param z.2.val)
          ⟨0, Metric.mem_ball_self (hStableFamilyRadius x)⟩ := by
      let B (p : stableFamilyDomain x) := stableModelEquiv (stableLabel p.val) ⟨p.val, rfl⟩
      let L (p : stableFamilyDomain x) := (stableFamilyLinearFrame x p).trans (B p).symm
      let V (p : stableFamilyDomain x) : Opens (stableSourceDisc p.val) :=
        ⟨{v | (L p).symm v.val ∈ Metric.ball 0 (stableFamilyRadius x)},
          Metric.isOpen_ball.preimage ((L p).symm.continuous.comp continuous_subtype_val)⟩
      let ball : Opens (Fin (as'.rank x) → ℝ) :=
        ⟨Metric.ball 0 (stableFamilyRadius x), Metric.isOpen_ball⟩
      let W (_p : stableFamilyDomain x) : Opens ball := ⊤
      have hV0 (p : stableFamilyDomain x) : stableSourceCenter p.val ∈ V p := by
        change (L p).symm 0 ∈ Metric.ball 0 (stableFamilyRadius x)
        rw [map_zero]
        exact Metric.mem_ball_self (hStableFamilyRadius x)
      let D (p : stableFamilyDomain x) : Diffeomorph
          𝓘(ℝ, Fin (stableRank (stableLabel p.val)) → ℝ)
          𝓘(ℝ, Fin (as'.rank x) → ℝ) (V p) (W p) ∞ := {
        toEquiv := {
          toFun := fun v ↦ ⟨⟨(L p).symm v.val.val, v.property⟩, trivial⟩
          invFun := fun w ↦ ⟨⟨L p w.val.val, by
            change ν p.val (B p ((B p).symm (stableFamilyLinearFrame x p w.val.val))).val < plaqueRadius
            rw [(B p).apply_symm_apply]
            exact (hStableFamilySmallAmbient x p w.val.val w.val.property).1⟩, by
              change (L p).symm (L p w.val.val) ∈ Metric.ball 0 (stableFamilyRadius x)
              rw [(L p).symm_apply_apply]
              exact w.val.property⟩
          left_inv := by
            intro v
            apply Subtype.ext
            apply Subtype.ext
            exact (L p).apply_symm_apply v.val.val
          right_inv := by
            intro w
            apply Subtype.ext
            apply Subtype.ext
            exact (L p).symm_apply_apply w.val.val }
        contMDiff_toFun := by
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact (L p).symm.contDiff.contMDiff.comp
            (contMDiff_subtype_val.comp contMDiff_subtype_val)
        contMDiff_invFun := by
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact (L p).contDiff.contMDiff.comp
            (contMDiff_subtype_val.comp contMDiff_subtype_val) }
      exact {
        sourceInner := V
        familyInner := W
        source_center_mem := hV0
        family_center_mem := fun _ ↦ trivial
        comparison := D
        centered := by
          intro p
          apply Subtype.ext
          change (L p).symm 0 = 0
          exact map_zero _
        same_map := by
          intro p v
          rw [hStableSourceFormula]
          change stablePlaque p.val
            (stableFamilyLinearFrame x p ((stableFamilyLinearFrame x p).symm (B p v.val.val))) = _
          rw [(stableFamilyLinearFrame x p).apply_symm_apply] }
    have hStableSourceOutput : SourceBoundDistanceOutput stablePartition stableFamilies stableCoherent
        f edist := by
      refine ⟨stableLabel, stableSourceDisc, stableSourceMap, stableSourceStages,
        ⟨stableIdentification, rfl⟩, ?_, ?_⟩
      · intro x
        exact ⟨⟨stableFamilyGerm x⟩, fun _ ↦ rfl⟩
      · intro N x
        exact ⟨⟨stableFamilyGerm x⟩, fun _ ↦ rfl⟩

    -- Complete the local family jets, intrinsic chart restrictions, and ambient boxes
    -- for these source plaques. The outer proof applies this same construction to f.symm.
    let centerP (x : X) : stableFamilyDomain x := ⟨x, hStableFamilyCenterMem x⟩
    let Acenter (x : X) := stableFamilyLinearFrame x (centerP x)
    have Bcenter (x : X) : (Fin (au.rank x) → ℝ) ≃L[ℝ] S.unstable.toDistribution x :=
      (EuclideanSpace.equiv (Fin (au.rank x)) ℝ).symm.trans
        (au.coordinates x x (au.mem_baseSet x)).symm
    let productModel (x : X) := ((Acenter x).prodCongr (Bcenter x)).trans (stableModel x)
    let projection (x : X) : E →L[ℝ] (Fin (as'.rank x) → ℝ) :=
      (ContinuousLinearMap.fst ℝ _ _).comp (productModel x).symm.toContinuousLinearMap
    let H (x : X) (p : stableFamilyDomain x) (v : Fin (as'.rank x) → ℝ) :=
      projection x (extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x p).param v) -
        extChartAt 𝓘(ℝ, E) x x)
    let HD (x : X) (z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ)) :=
      (projection x).comp (fderiv ℝ
        (fun v ↦ extChartAt 𝓘(ℝ, E) x ((stableFamilyPlaque x z.1).param v)) z.2)
    have Hzero (x : X) : H x (centerP x) 0 = 0 := by
      change projection x (extChartAt 𝓘(ℝ, E) x
        ((stableFamilyPlaque x (centerP x)).param 0) - extChartAt 𝓘(ℝ, E) x x) = 0
      rw [(stableFamilyPlaque x (centerP x)).centered, sub_self, map_zero]
    have hHcont (x : X) : Continuous (fun z : stableFamilyDomain x ×
        Metric.ball (0 : Fin (as'.rank x) → ℝ) (stableFamilyRadius x) ↦ H x z.1 z.2.val) :=
      (projection x).continuous.comp ((hStableFamilyCoordinateContinuous x).sub continuous_const)
    have hHDcont (x : X) : Continuous (fun z : stableFamilyDomain x ×
        Metric.ball (0 : Fin (as'.rank x) → ℝ) (stableFamilyRadius x) ↦ HD x (z.1, z.2.val)) :=
      continuous_const.clm_comp (hStableFamilyJointDerivative x)
    have hHderiv (x : X) (p : stableFamilyDomain x)
        (v : Fin (as'.rank x) → ℝ) (hv : v ∈ Metric.ball 0 (stableFamilyRadius x)) :
        HasFDerivAt (H x p) (HD x (p, v)) v := by
      exact (projection x).hasFDerivAt.comp v
        ((((hStableFamilyCoordinateSmooth x p).contDiffAt
          (Metric.isOpen_ball.mem_nhds hv)).differentiableAt (by simp)).hasFDerivAt.sub_const _)
    let projectionDomain (x : X) : Set (stableFamilyDomain x × (Fin (as'.rank x) → ℝ)) :=
      Set.univ ×ˢ Metric.ball 0 (stableFamilyRadius x)
    have hProjectionDomain (x : X) : IsOpen (projectionDomain x) :=
      isOpen_univ.prod Metric.isOpen_ball
    have hHcontOn (x : X) : ContinuousOn
        (fun z : stableFamilyDomain x × (Fin (as'.rank x) → ℝ) ↦ H x z.1 z.2)
        (projectionDomain x) :=
      continuousOn_univ_prod_of_subtype_g4 _ _ (hHcont x)
    have hHDcontOn (x : X) : ContinuousOn (HD x) (projectionDomain x) :=
      continuousOn_univ_prod_of_subtype_g4 _ _ (hHDcont x)
    have hHDzero (x : X) : HD x (centerP x, 0) =
        ContinuousLinearMap.id ℝ (Fin (as'.rank x) → ℝ) := by
      let p := centerP x
      let β := (stableFamilyPlaque x p).param
      have hβzero : β 0 = x := (stableFamilyPlaque x p).centered
      have hβd : MDifferentiableAt 𝓘(ℝ, Fin (as'.rank x) → ℝ) 𝓘(ℝ, E) β 0 :=
        ((stableFamilyPlaque x p).smooth.contMDiffAt
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hStableFamilyRadius x)))).mdifferentiableAt
            (by simp)
      have hcd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x) (β 0) := by
        rw [hβzero]
        exact mdifferentiableAt_extChartAt (mem_chart_source E x)
      have hraw : fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) x (β v)) 0 =
          mfderiv 𝓘(ℝ, Fin (as'.rank x) → ℝ) 𝓘(ℝ, E) β 0 := by
        rw [← mfderiv_eq_fderiv]
        rw [show (fun v ↦ extChartAt 𝓘(ℝ, E) x (β v)) =
          (extChartAt 𝓘(ℝ, E) x) ∘ β from rfl, mfderiv_comp 0 hcd hβd,
          hβzero, mfderiv_extChartAt_self]
        rfl
      have hsmall : ν x (Acenter x 0).val < plaqueRadius := by
        rw [map_zero, Submodule.coe_zero, hνzero]
        exact hPlaqueRadius
      have hb : mfderiv 𝓘(ℝ, Fin (as'.rank x) → ℝ) 𝓘(ℝ, E) β 0 =
          (mfderiv 𝓘(ℝ, S.stable.toDistribution x) 𝓘(ℝ, E) (stablePlaque x) 0).comp
            (Acenter x).toContinuousLinearMap := by
        change mfderiv 𝓘(ℝ, Fin (as'.rank x) → ℝ) 𝓘(ℝ, E)
          (fun v ↦ stablePlaque x (Acenter x v)) 0 = _
        rw [hStableReparamDerivative x _ _ 0 hsmall, map_zero]
      apply ContinuousLinearMap.ext
      intro v
      change projection x (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) x (β w)) 0 v) = v
      have hbval : mfderiv 𝓘(ℝ, Fin (as'.rank x) → ℝ) 𝓘(ℝ, E) β 0 v =
          (Acenter x v).val :=
        (congrArg (fun L : (Fin (as'.rank x) → ℝ) →L[ℝ] E ↦ L v) hb).trans
          (hStablePlaqueDerivativeZero x (Acenter x v))
      have hrawval : fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) x (β w)) 0 v =
          (Acenter x v).val :=
        (congrArg (fun L : (Fin (as'.rank x) → ℝ) →L[ℝ] E ↦ L v) hraw).trans hbval
      apply (congrArg (projection x) hrawval).trans
      have he : productModel x (v, 0) = (Acenter x v).val := by
        change tangentSpaceCastModel 𝓘(ℝ, E) x
          (merge x (Bcenter x 0, Acenter x v)) = (Acenter x v).val
        rw [map_zero]
        exact zero_add ((Acenter x v).val)
      change ((productModel x).symm (Acenter x v).val).1 = v
      rw [← he, ContinuousLinearEquiv.symm_apply_apply]
    let regularProjectionDomain (x : X) := projectionDomain x ∩ {z | (HD x z).IsInvertible}
    have hRegularProjectionDomain (x : X) : IsOpen (regularProjectionDomain x) :=
      (hHDcontOn x).isOpen_inter_preimage (hProjectionDomain x)
        ContinuousLinearMap.isOpen_setOfPred_isInvertible
    have hRegularProjectionCenter (x : X) : (centerP x, 0) ∈ regularProjectionDomain x := by
      refine ⟨⟨Set.mem_univ _, Metric.mem_ball_self (hStableFamilyRadius x)⟩, ?_⟩
      change (HD x (centerP x, 0)).IsInvertible
      rw [hHDzero]
      exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    have hHsmooth (x : X) (p : stableFamilyDomain x) :
        ContDiffOn ℝ ∞ (H x p) (Metric.ball 0 (stableFamilyRadius x)) :=
      (projection x).contDiff.comp_contDiffOn
        ((hStableFamilyCoordinateSmooth x p).sub contDiffOn_const)
    have hProjectionInverse (x : X) :=
      Analysis.parametric_c1_inverse_neighborhood_g18 (H x) (HD x)
        (regularProjectionDomain x) (hRegularProjectionDomain x) (centerP x)
        (hRegularProjectionCenter x)
        ((hHcontOn x).mono Set.inter_subset_left) ((hHDcontOn x).mono Set.inter_subset_left)
        (fun z hz ↦ hHderiv x z.1 z.2 hz.1.2) (Hzero x) (hHDzero x)
    choose inversePatch hInversePatch inverseRadius hInverseRadius inverseChart hInverseChart
      hInverseContinuous hInverseDerivativeContinuous hInverseSourceZero hInverseSourceOpen
      using hProjectionInverse
    have hInverseSmooth (x : X) (p : inversePatch x) :
        ContDiffOn ℝ ∞ (inverseChart x p).symm (inverseChart x p).target := by
      intro v hv
      let e := inverseChart x p
      have hy : e.symm v ∈ e.source := e.map_target hv
      have hyreg := (hInverseChart x p).2.2.2.2.2 (e.symm v) hy
      obtain ⟨A, hA⟩ := hyreg.2
      have hd : HasFDerivAt e A.toContinuousLinearMap (e.symm v) := by
        rw [(hInverseChart x p).1, hA]
        exact hHderiv x p.val (e.symm v) hyreg.1.2
      have hc : ContDiffAt ℝ ∞ e (e.symm v) := by
        rw [(hInverseChart x p).1]
        exact (hHsmooth x p.val).contDiffAt (Metric.isOpen_ball.mem_nhds hyreg.1.2)
      exact (e.contDiffAt_symm hv hd hc).contDiffWithinAt
    let ambientChart (x : X) : OpenPartialHomeomorph X
        ((Fin (as'.rank x) → ℝ) × (Fin (au.rank x) → ℝ)) :=
      (chartAt E x).transHomeomorph
        ((Homeomorph.subRight (chartAt E x x)).trans (productModel x).symm.toHomeomorph)
    have hAmbientChartSource (x : X) : (ambientChart x).source = (chartAt E x).source := rfl
    have hAmbientChartCenter (x : X) : ambientChart x x = (0, 0) := by
      change (productModel x).symm (chartAt E x x - chartAt E x x) = (0, 0)
      rw [sub_self, map_zero]
      rfl
    have hAmbientProjection (x : X) (p : stableFamilyDomain x) (v : Fin (as'.rank x) → ℝ) :
        (ambientChart x ((stableFamilyPlaque x p).param v)).1 = H x p v := rfl
    have hAmbientFamilySource (x : X) (p : stableFamilyDomain x) : p.val ∈ (ambientChart x).source := by
      have hs := (hStableFamilySmallAmbient x p 0 (Metric.mem_ball_self (hStableFamilyRadius x))).2
      rw [extChartAt_source] at hs
      change (stableFamilyPlaque x p).param 0 ∈ (chartAt E x).source at hs
      rw [(stableFamilyPlaque x p).centered] at hs
      exact hs
    let inverseBall (x : X) : Opens (Fin (as'.rank x) → ℝ) :=
      ⟨Metric.ball 0 (inverseRadius x / 8), Metric.isOpen_ball⟩
    have hNormalizedChart (x : X) (p : inversePatch x) :
        ∃ U : Opens (stableLeaf (stableLabel p.val.val)),
        ∃ D : Diffeomorph 𝓘(ℝ, Fin (as'.rank x) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel p.val.val)) → ℝ) (inverseBall x) U ∞,
        ∀ v : inverseBall x, (D v).val =
          ((stableFiniteFamily x).chart p.val
            ⟨(inverseChart x p).symm v.val,
              ((hInverseChart x p).2.2.2.2.2 _
                ((inverseChart x p).map_target
                  ((hInverseChart x p).2.2.1.symm ▸ v.property))).1.2⟩).val := by
      set_option backward.isDefEq.respectTransparency true in
      set_option maxHeartbeats 200000 in
      let e := inverseChart x p
      let big : Opens (Fin (as'.rank x) → ℝ) :=
        ⟨Metric.ball 0 (stableFamilyRadius x), Metric.isOpen_ball⟩
      have ht (v : inverseBall x) : v.val ∈ e.target :=
        (hInverseChart x p).2.2.1.symm ▸ v.property
      have hs (v : inverseBall x) : e.symm v.val ∈ big :=
        ((hInverseChart x p).2.2.2.2.2 _ (e.map_target (ht v))).1.2
      let j : inverseBall x → big := fun v ↦ ⟨e.symm v.val, hs v⟩
      let jt : inverseBall x → e.target := fun v ↦ ⟨v.val, ht v⟩
      have hjt : IsOpenEmbedding jt := IsOpenEmbedding.of_comp jt
        e.open_target.isOpenEmbedding_subtypeVal (inverseBall x).isOpen.isOpenEmbedding_subtypeVal
      have hj : IsOpenEmbedding j := IsOpenEmbedding.of_comp j
        big.isOpen.isOpenEmbedding_subtypeVal (e.symm.isOpenEmbedding_restrict.comp hjt)
      have hjm : ContMDiff 𝓘(ℝ, Fin (as'.rank x) → ℝ)
          𝓘(ℝ, Fin (as'.rank x) → ℝ) ∞ j := by
        apply (ContMDiff.subtypeVal_comp_iff big _).mp
        exact (contMDiffOn_iff_contDiffOn.mpr (hInverseSmooth x p)).comp_contMDiff
          contMDiff_subtype_val ht
      let old := (stableFiniteFamily x).chart p.val
      let h : inverseBall x → stableLeaf (stableLabel p.val.val) := fun v ↦ (old (j v)).val
      have hh : IsOpenEmbedding h :=
        ((stableFiniteFamily x).receivingPlaque p.val).isOpen.isOpenEmbedding_subtypeVal.comp
          (old.toHomeomorph.isOpenEmbedding.comp hj)
      let U : Opens (stableLeaf (stableLabel p.val.val)) := ⟨Set.range h, hh.isOpen_range⟩
      have hU (q : U) : q.val ∈ (stableFiniteFamily x).receivingPlaque p.val := by
        obtain ⟨v, hv⟩ := q.property
        exact hv ▸ (old (j v)).property
      let iU : U → (stableFiniteFamily x).receivingPlaque p.val := fun q ↦ ⟨q.val, hU q⟩
      have hiU : ContMDiff 𝓘(ℝ, Fin (stableRank (stableLabel p.val.val)) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel p.val.val)) → ℝ) ∞ iU := by
        apply (ContMDiff.subtypeVal_comp_iff _ _).mp
        exact contMDiff_subtype_val
      have hqsource (q : U) : (old.symm (iU q)).val ∈ e.source := by
        obtain ⟨v, hv⟩ := q.property
        have he : iU q = old (j v) := Subtype.ext hv.symm
        rw [he, old.symm_apply_apply]
        exact e.map_target (ht v)
      have hqtarget (q : U) : e (old.symm (iU q)).val ∈ inverseBall x := by
        change e (old.symm (iU q)).val ∈ Metric.ball 0 (inverseRadius x / 8)
        rw [← (hInverseChart x p).2.2.1]
        exact e.map_source (hqsource q)
      let D : Diffeomorph 𝓘(ℝ, Fin (as'.rank x) → ℝ)
          𝓘(ℝ, Fin (stableRank (stableLabel p.val.val)) → ℝ) (inverseBall x) U ∞ := {
        toEquiv := {
          toFun := fun v ↦ ⟨h v, ⟨v, rfl⟩⟩
          invFun := fun q ↦ ⟨e (old.symm (iU q)).val, hqtarget q⟩
          left_inv := by
            intro v
            apply Subtype.ext
            change e (old.symm (iU ⟨h v, ⟨v, rfl⟩⟩)).val = v.val
            have he : iU ⟨h v, ⟨v, rfl⟩⟩ = old (j v) := rfl
            rw [he, old.symm_apply_apply]
            exact e.right_inv (ht v)
          right_inv := by
            intro q
            apply Subtype.ext
            change (old (j ⟨e (old.symm (iU q)).val, hqtarget q⟩)).val = q.val
            have he : j ⟨e (old.symm (iU q)).val, hqtarget q⟩ = old.symm (iU q) :=
              Subtype.ext (e.left_inv (hqsource q))
            rw [he, old.apply_symm_apply] }
        contMDiff_toFun := by
          apply (ContMDiff.subtypeVal_comp_iff U _).mp
          convert (ContMDiff.subtypeVal_comp_iff
            ((stableFiniteFamily x).receivingPlaque p.val) _).mpr
              (old.contMDiff.comp hjm) using 1; rfl
        contMDiff_invFun := by
          apply (ContMDiff.subtypeVal_comp_iff (inverseBall x) _).mp
          have hold := (ContMDiff.subtypeVal_comp_iff _ _).mpr (old.symm.contMDiff.comp hiU)
          have hmap : ContMDiffOn 𝓘(ℝ, Fin (as'.rank x) → ℝ)
              𝓘(ℝ, Fin (as'.rank x) → ℝ) ∞ e e.source := by
            rw [(hInverseChart x p).1]
            exact contMDiffOn_iff_contDiffOn.mpr ((hHsmooth x p.val).mono
              (fun v hv ↦ ((hInverseChart x p).2.2.2.2.2 v hv).1.2))
          exact hmap.comp_contMDiff hold hqsource }
      exact ⟨U, D, fun _ ↦ rfl⟩
    choose normalizedPlaque normalizedChart hNormalizedChartValue using hNormalizedChart
    have hHcenterContinuous (x : X) : Continuous (fun p : stableFamilyDomain x ↦ H x p 0) := by
      set_option backward.isDefEq.respectTransparency true in
      set_option maxHeartbeats 200000 in
      let z : stableFamilyDomain x →
          Metric.ball (0 : Fin (as'.rank x) → ℝ) (stableFamilyRadius x) :=
        fun _ ↦ ⟨0, Metric.mem_ball_self (hStableFamilyRadius x)⟩
      have hz : Continuous z := continuous_const
      change Continuous ((fun q : stableFamilyDomain x ×
        Metric.ball (0 : Fin (as'.rank x) → ℝ) (stableFamilyRadius x) ↦
          H x q.1 q.2.val) ∘ (fun p ↦ (p, z p)))
      exact (hHcont x).comp ((continuous_id : Continuous (fun p : stableFamilyDomain x ↦ p)).prodMk hz)
    let centerPatch (x : X) : Opens (stableFamilyDomain x) :=
      ⟨(inversePatch x : Set (stableFamilyDomain x)) ∩
        (fun p ↦ H x p 0) ⁻¹' (inverseBall x : Set (Fin (as'.rank x) → ℝ)),
        (inversePatch x).isOpen.inter ((inverseBall x).isOpen.preimage (hHcenterContinuous x))⟩
    have hCenterPatch (x : X) : centerP x ∈ centerPatch x := by
      refine ⟨hInversePatch x, ?_⟩
      change H x (centerP x) 0 ∈ Metric.ball 0 (inverseRadius x / 8)
      rw [Hzero]
      exact Metric.mem_ball_self (div_pos (hInverseRadius x) (by norm_num))
    let normalizedCenters (x : X) : Opens X :=
      ⟨Subtype.val '' (centerPatch x : Set (stableFamilyDomain x)),
        (stableFamilyDomain x).isOpen.isOpenMap_subtype_val _ (centerPatch x).isOpen⟩
    have hNormalizedCenters (x : X) : x ∈ normalizedCenters x :=
      ⟨centerP x, hCenterPatch x, rfl⟩
    have hCenterOld (x : X) (p : normalizedCenters x) : p.val ∈ stableFamilyDomain x := by
      obtain ⟨q, _, hq⟩ := p.property
      exact hq ▸ q.property
    have hCenterSelected (x : X) (p : normalizedCenters x) :
        (⟨p.val, hCenterOld x p⟩ : stableFamilyDomain x) ∈ centerPatch x := by
      obtain ⟨q, hq, he⟩ := p.property
      have hqp : q = ⟨p.val, hCenterOld x p⟩ := Subtype.ext he
      exact hqp ▸ hq
    let centerParameter (x : X) (p : normalizedCenters x) : inversePatch x :=
      ⟨⟨p.val, hCenterOld x p⟩, (hCenterSelected x p).1⟩
    have hCenterParameterContinuous (x : X) : Continuous (centerParameter x) :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _
    have hCenterParameterZero (x : X) (p : normalizedCenters x) :
        (0 : Fin (as'.rank x) → ℝ) ∈ (inverseChart x (centerParameter x p)).source := by
      rw [(hInverseChart x (centerParameter x p)).2.1]
      exact ⟨Metric.mem_ball_self (hInverseRadius x), (hCenterSelected x p).2⟩
    have hNormalizedValue (x : X) (p : inversePatch x) (v : inverseBall x) :
        (stablePartition.leaf (stableLabel p.val.val)).inclusion (normalizedChart x p v) =
          (stableFamilyPlaque x p.val).param ((inverseChart x p).symm v.val) := by
      set_option backward.isDefEq.respectTransparency true in
      set_option maxHeartbeats 200000 in
      change (stablePartition.leaf (stableLabel p.val.val)).inclusion
          (normalizedChart x p v) = _
      rw [hNormalizedChartValue]
      exact ((stableFiniteFamily x).factorization p.val _).symm
    have hNormalizedValuesContinuous (x : X) : Continuous
        (fun z : inversePatch x × inverseBall x ↦
          (stablePartition.leaf (stableLabel z.1.val.val)).inclusion
            (normalizedChart x z.1 z.2)) := by
      set_option backward.isDefEq.respectTransparency true in
      set_option maxHeartbeats 200000 in
      have hi : Continuous (fun z : inversePatch x × inverseBall x ↦
          (inverseChart x z.1).symm z.2.val) :=
        (hInverseContinuous x).comp_continuous
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
          (fun z ↦ ⟨Set.mem_univ _, z.2.property⟩)
      let j : inversePatch x × inverseBall x →
          stableFamilyDomain x × Metric.ball (0 : Fin (as'.rank x) → ℝ)
            (stableFamilyRadius x) := fun z ↦
        (z.1.val, ⟨(inverseChart x z.1).symm z.2.val,
          ((hInverseChart x z.1).2.2.2.2.2 _
            ((inverseChart x z.1).map_target
              ((hInverseChart x z.1).2.2.1.symm ▸ z.2.property))).1.2⟩)
      have hj : Continuous j := (continuous_subtype_val.comp continuous_fst).prodMk
        (hi.subtype_mk _)
      exact ((hStableFamilyJointContinuous x).comp hj).congr
        (fun z ↦ (hNormalizedValue x z.1 z.2).symm)
    let projectedFamily (x : X) :
        ProjectedNativePlaqueFamily stablePartition x (as'.rank x) (au.rank x) := by
      set_option backward.isDefEq.respectTransparency true in
      set_option maxHeartbeats 200000 in
      exact {
      centers := normalizedCenters x
      center_mem := hNormalizedCenters x
      ambientChart := ambientChart x
      centers_source := fun p hp ↦ hAmbientFamilySource x ⟨p, hCenterOld x ⟨p, hp⟩⟩
      chart_center := hAmbientChartCenter x
      radius := inverseRadius x / 8
      radius_pos := div_pos (hInverseRadius x) (by norm_num)
      label := fun p ↦ stableLabel p.val
      plaque := fun p ↦ normalizedPlaque x (centerParameter x p)
      chart := fun p ↦ normalizedChart x (centerParameter x p)
      continuous_values := (hNormalizedValuesContinuous x).comp
        ((hCenterParameterContinuous x).prodMap continuous_id)
      values_source := by
        intro p v
        rw [hNormalizedValue]
        rw [hAmbientChartSource, ← extChartAt_source 𝓘(ℝ, E)]
        exact (hStableFamilySmallAmbient x (centerParameter x p).val _
          ((hInverseChart x (centerParameter x p)).2.2.2.2.2 _
            ((inverseChart x (centerParameter x p)).map_target
              ((hInverseChart x (centerParameter x p)).2.2.1.symm ▸ v.property))).1.2).2
      projection := by
        intro p v
        rw [hNormalizedValue, hAmbientProjection]
        rw [← (hInverseChart x (centerParameter x p)).1]
        exact (inverseChart x (centerParameter x p)).right_inv
          ((hInverseChart x (centerParameter x p)).2.2.1.symm ▸ v.property)
      center_projection_mem := by
        intro p
        have hc : (ambientChart x p.val).1 = H x (centerParameter x p).val 0 := by
          rw [← hAmbientProjection, (stableFamilyPlaque x (centerParameter x p).val).centered]
        rw [hc]
        exact (hCenterSelected x p).2
      centered := by
        intro p
        rw [hNormalizedValue]
        have hc : (ambientChart x p.val).1 = (inverseChart x (centerParameter x p)) 0 := by
          have hcenter : (ambientChart x p.val).1 =
              H x (centerParameter x p).val 0 := by
            calc
              (ambientChart x p.val).1 =
                  (ambientChart x ((stableFamilyPlaque x (centerParameter x p).val).param 0)).1 := by
                    rw [(stableFamilyPlaque x (centerParameter x p).val).centered]
              _ = H x (centerParameter x p).val 0 := hAmbientProjection x _ _
          calc
            (ambientChart x p.val).1 = H x (centerParameter x p).val 0 := hcenter
            _ = (inverseChart x (centerParameter x p)) 0 := by
              rw [(hInverseChart x (centerParameter x p)).1]
        have harg : (inverseChart x (centerParameter x p)).symm
            (ambientChart x p.val).1 = 0 := by
          rw [hc]
          exact (inverseChart x (centerParameter x p)).left_inv
            (hCenterParameterZero x p)
        rw [harg]
        exact (stableFamilyPlaque x (centerParameter x p).val).centered }
    have hNativeBox (x : X) := (projectedFamily x).exists_native_box
    choose boxRadius hBoxRadius nativeBox hNativeBoxCenter using hNativeBox
    let transverse (x : X) := ULift.{u} (Metric.ball (0 : Fin (au.rank x) → ℝ) (boxRadius x))
    have hBoxCover (p : X) : ∃ x, p ∈ (nativeBox x).ambient := ⟨p, hNativeBoxCenter p⟩
    refine ⟨stableIndex, stableLeaf, stableRank, stableLeafTop, stableLeafCharts,
      inferInstance, stablePartition, ?_, ⟨stableInvariance⟩,
      stableFamilies, stableCoherent, hStableSourceOutput⟩
    refine ⟨X, as'.rank, transverse, fun _ ↦ inferInstance, ⟨{
      boxes := nativeBox
      cover := hBoxCover
      topology_generated := by
        intro i W
        constructor
        · intro hW b t h
          have hh (j : stableIndex) (hj : (nativeBox b).label t = j)
              (V : Set (stableLeaf j)) (hV : IsOpen V) :
              IsOpen ((fun v : (nativeBox b).disc ↦
                (hj ▸ ((nativeBox b).chart t v).val : stableLeaf j)) ⁻¹' V) := by
            subst j
            exact hV.preimage (continuous_subtype_val.comp ((nativeBox b).chart t).continuous)
          exact hh i h W hW
        · intro hW
          apply isOpen_iff_mem_nhds.mpr
          intro y hy
          obtain ⟨b, hb⟩ := hBoxCover ((stablePartition.leaf i).inclusion y)
          let c := (nativeBox b).box.symm ⟨(stablePartition.leaf i).inclusion y, hb⟩
          have hc : (stablePartition.leaf ((nativeBox b).label c.2)).inclusion
                ((nativeBox b).chart c.2 c.1) = (stablePartition.leaf i).inclusion y := by
            rw [← (nativeBox b).factorization, Prod.mk.eta]
            exact congrArg Subtype.val ((nativeBox b).box.apply_symm_apply _)
          have hi := stablePartition.disjoint _ _ ((nativeBox b).chart c.2 c.1).val y hc
          have hopen := hW b c.2 hi
          have ho : IsOpen (((fun v : (nativeBox b).disc ↦
              (hi ▸ ((nativeBox b).chart c.2 v).val : stableLeaf i)) ⁻¹' W)) := hopen
          have hnh : IsOpen (W ∩
              (fun z : stableLeaf ((nativeBox b).label c.2) ↦
                (hi ▸ z : stableLeaf i)) ''
              ((nativeBox b).plaque c.2 : Set (stableLeaf ((nativeBox b).label c.2)))) := by
            have hh (j : stableIndex) (hj : (nativeBox b).label c.2 = j)
                (V : Set (stableLeaf j))
                (hV : IsOpen ((fun v : (nativeBox b).disc ↦
                  (hj ▸ ((nativeBox b).chart c.2 v).val : stableLeaf j)) ⁻¹' V)) :
                IsOpen (V ∩ (fun z : stableLeaf ((nativeBox b).label c.2) ↦
                  (hj ▸ z : stableLeaf j)) ''
                  ((nativeBox b).plaque c.2 : Set (stableLeaf ((nativeBox b).label c.2)))) := by
              subst j
              simp only [eq_rec_constant, Set.image_id']
              have hvopen : IsOpen ((Subtype.val : (nativeBox b).plaque c.2 →
                  stableLeaf ((nativeBox b).label c.2)) ⁻¹' V) :=
                (((nativeBox b).chart c.2).toHomeomorph.isOpen_preimage).mp hV
              have hout := ((nativeBox b).plaque c.2).isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hvopen
              convert hout using 1
              ext z
              simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage, Subtype.exists, exists_prop]
              constructor
              · rintro ⟨hz, hzp⟩
                exact ⟨z, hzp, hz, rfl⟩
              · rintro ⟨z, hzp, hz, rfl⟩
                exact ⟨hz, hzp⟩
            exact hh i hi W ho
          have hcast (j : stableIndex) (hj : (nativeBox b).label c.2 = j) :
              (stablePartition.leaf j).inclusion
                (hj ▸ ((nativeBox b).chart c.2 c.1).val) =
              (stablePartition.leaf ((nativeBox b).label c.2)).inclusion
                ((nativeBox b).chart c.2 c.1) := by
            subst j
            rfl
          have hypl : y ∈ W ∩
              (fun z : stableLeaf ((nativeBox b).label c.2) ↦
                (hi ▸ z : stableLeaf i)) ''
                ((nativeBox b).plaque c.2 : Set (stableLeaf ((nativeBox b).label c.2))) := by
            refine ⟨?_, ⟨((nativeBox b).chart c.2 c.1).val,
              ((nativeBox b).chart c.2 c.1).property, ?_⟩⟩
            exact hy
            apply (stablePartition.leaf i).injective
            exact (hcast i hi).trans hc
          exact Filter.mem_of_superset (hnh.mem_nhds hypl) Set.inter_subset_left
        }⟩⟩

  have hinv (P : RealTangentDistribution 𝓘(ℝ, E) X)
      (hP : ∀ x, (P x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap = P (f x))
      (x : X) :
      (P x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x).toLinearMap = P (f.symm x) := by
    have hh := hP (f.symm x)
    rw [f.apply_symm_apply] at hh
    rw [← hh, ← Submodule.map_comp]
    have hi : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x).toLinearMap.comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (f.symm x)).toLinearMap = LinearMap.id := by
      ext v
      have hd := derivative_inverse_forward f (f.symm x) v
      simp only [TangentSpace] at hd ⊢
      rw [f.apply_symm_apply] at hd
      exact hd
    rw [hi, Submodule.map_id]
  let Q : InvariantRealTangentSplitting f.symm := {
    stable := S.unstable
    unstable := S.stable
    isCompl := fun x ↦ (S.isCompl x).symm
    stable_map := hinv _ S.unstable_map
    unstable_map := hinv _ S.stable_map }
  have hQ : BundleAnosovBounds f.symm Q := by
    obtain ⟨C, rate, hC, hr, hr1, hs, hu⟩ := h
    exact ⟨C, rate, hC, hr, hr1, hu, hs⟩
  have hreverse (D : RealTangentDistribution 𝓘(ℝ, E) X)
      (f g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X X ∞)
      (h : HasNativeLamination D f
        (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent g edist)) :
      HasNativeLamination D f.symm
        (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent g edist) := by
    rcases h with ⟨ι,L,r,top,charts,smooth,F,boxes,⟨inv⟩,families,coherent,output⟩
    letI := top
    letI := charts
    letI := smooth
    let reverseTransport (i j : ι) (hi : inv.permutation j = i) :
        Diffeomorph 𝓘(ℝ, Fin (r i) → ℝ) 𝓘(ℝ, Fin (r j) → ℝ) (L i) (L j) ∞ :=
      cast (congrArg (fun k : ι ↦ Diffeomorph 𝓘(ℝ, Fin (r k) → ℝ)
        𝓘(ℝ, Fin (r j) → ℝ) (L k) (L j) ∞) hi) (inv.transport j).symm
    have hreverse (i j : ι) (hi : inv.permutation j = i) (x : L i) :
        (F.leaf j).inclusion (reverseTransport i j hi x) =
          f.symm ((F.leaf i).inclusion x) := by
      subst i
      change (F.leaf j).inclusion ((inv.transport j).symm x) = _
      have hh := inv.intertwining j ((inv.transport j).symm x)
      rw [Diffeomorph.apply_symm_apply] at hh
      exact (congrArg f.symm hh).trans (f.symm_apply_apply _ ) |>.symm
    exact ⟨ι,L,r,top,charts,smooth,F,boxes,⟨{
      permutation := inv.permutation.symm
      transport := fun i ↦ reverseTransport i (inv.permutation.symm i)
        (inv.permutation.apply_symm_apply i)
      intertwining := fun i x ↦ hreverse i (inv.permutation.symm i)
        (inv.permutation.apply_symm_apply i) x }⟩,families,coherent,output⟩
  exact ⟨hforward f S h,
    hreverse S.unstable.toDistribution f.symm f.symm (hforward f.symm Q hQ)⟩

/--
 Independent HPS tensor-norm Anosov global lamination export.

Source: HPS (2.8)--(2.9), (5.1)--(5.5), (6.5)--(6.7), (6B.1)--(6B.4), §7 and (7.5)--(7.6), at the
locations in the distance theorem above. The manifold need not carry any finite ambient Riemannian
distance. In particular no cross-component distance is constructed. Both laminations, their
intrinsic smooth immersed leaves and all local finite-C¹ families are existential outputs. No
asymptotic-set identification or transported-stage union is asserted here, as prescribed by the
independent tensor clause of the current DAG statement.

Proof: Use the same source-selected weighted graph construction and native continuation as below.
The two original-f ambient asymptotic capture/path-length steps GL8--GL9 are unnecessary for this
independent export.

GL1: HPS §5 pp.53,61–62, expanded adaptation to the given splitting. Choose a with λ<a<1 and N≥1
such that Cλ^N<a^N, using geometric decay. On Eˢ define |v|²_s=Σ_{j=0}^{N−1}a^(−2j)‖D(f^j)v‖²,
with each norm taken at f^j(x); on Eᵘ use |w|²_u=Σ_{j=0}^{N−1}a^(−2j)‖D(f^(−j))w‖². These are
continuous positive fibre inner products. Invariance and the chain rule give |Df
v|²_s=a²(|v|²_s−‖v‖²+a^(−2N)‖D(f^N)v‖²)≤a²|v|²_s, and the analogous estimate |Df⁻¹ w|_u≤a|w|_u. On
the full tangent space use the product maximum norm of the two components; the continuous
projections for the complementary splitting and compactness make it uniformly equivalent to the
original norm. Thus Df has stable norm≤a<1 and unstable conorm≥a⁻¹>1 in this auxiliary norm. The
original Riemannian metric, given estimates and distance are not replaced: this norm is used only
for constructing uniform graph domains. If a summand has dimension zero its graph is a point and
the corresponding contraction estimate is vacuous. Source norm construction: HPS (2.8), printed
pp.13–14/PDF17–18, including the finite-sum remark on p.14, and bundle version (2.9),
pp.14–15/PDF18–19. This is the existing finite-sum applicability calculation. Write its one-step
contraction bound as theta<1 below. No iterate replaces the original f.

GL2: HPS first proof of (5.5), printed pp.61–63/PDF65–67, using (5.1)–(5.4), pp.53–61/PDF57–65.
Select the plaque data by this published construction. Apply the exponential/cutoff supplier on
A=M, h=f, T=Df and the GL1 product maximum norm; use the common exponential supplier to retain one
inner agreement domain. The first proof lifts f by H_p(v)=exp_(fp)^(-1)(f(exp_p(v))) and extends
it by averaging with T using a smooth bump on T_M M. Concretely use the already established
smooth-Riemannian squared-norm bump construction G_p=T_p+chi_p(H_p-T_p), with support strictly
inside the H-domain and chi=1 on a smaller common domain; the zero collar makes the patch equal to
T outside that support. Choose its initial first-order error epsilon small enough for the graph
and jet margins in the retained graph suppliers. In particular, for the ACTUAL derivative blocks
of G, alpha_*=sup||(D_vG_11)^(-1)|| is bounded by theta/(1-theta epsilon), and k_*=sup||D_vG_22||
is bounded by theta+epsilon; require BOTH upper bounds<1, as well as the source off-diagonal graph
margins, at this initial choice. These are derivative-block bounds, not an identification with the
fixed T block norms. The actual source cone margins alpha_*^(-1)-3epsilon>1 and k_*+epsilon<1 from
(5.1), pp.59–60, are included in this SAME initial source smallness choice. They concern the
derivative-block constants of this selected G; no fixed-T/core constant is substituted for
alpha_*. No smallness of higher jets is required. The selected G is C-infinity fibrewise: the
fixed smooth local exponential expression, smooth bump and zero collar give every finite-order
fibre derivative, jointly continuous in local frames. Compact frame cores give the corresponding
finite-order uniformity. This is the source smooth-bump construction, not a claim that the old
private cutoff graphs are its exported outputs.

Follow the first proof's parameter section space Z_0(1): centered unit-slope maps over E^u_p, with
weighted metric sup_p sup_(v!=0)||s_p(v)-s'_p(v)||/||v||. The zero family is in the space; its
weighted distances are finite, and the Cauchy argument of (5.2) gives a complete closed carrier.
The image graph transform covers h and is a strict contraction by the estimates of (5.1); the
analogous preimage transform over E^s has the source whole-fibre horizontal fixed-point inverse.
Use the retained parameter graph supplier at rho=1 on THIS selected G and splitting. Its fixed
graph families are Gamma^u_p and Gamma^s_p. The transforms preserve continuous parameter families;
the differentiated closed-jet transform identifies their fibre derivatives and preserves
continuous derivative sections, as in pp.62 and 55–58. Thus the families have the stated
finite-order C^r dependence on fixed local discs. The fixed-point suppliers give existence and
uniqueness on these actual complete metric carriers; no autonomous map G_p:E_p→E_p is substituted
for the moving bundle. Exponentiate the small graph discs in the inner agreement domain to obtain
the SOURCE-SELECTED plaques P^s(p),P^u(p), forward/backward trapped respectively. All subsequent
G, graphs and plaques refer to this choice. The public statement is existential, so no equality
with any superseded private G or old section carrier is needed.

GL3: HPS (5.1) characterization, pp.54,59–60/PDF58,63–64; (5.4), pp.60–61/PDF64–65; and the actual
(5.5) statement/proof, pp.61–62/PDF65–66. The printed inequalities in (5.5) are NONSTRICT: rho>=1
for the unstable branch and rho<=1 for the stable branch. Therefore at rho=1 BOTH source
self-coherence and C^r local characterization apply; the former strict-branch reading and its
auxiliary identification are removed. The word local is essential: bounded distance somewhere on
compact M is not a plaque-membership test. The retained parameter supplier gives coherent forward
or backward G-histories entirely in one small common fibre disc, with norms bounded at rate1.
Choose b_*>0 inside BOTH that local-membership disc and the source-selected exponential/cutoff
agreement disc, and inside the selected plaque radius. In this disc the exact exponential equation
transports these histories to the original f. The source local bounded-orbit characterization
captures their initial points on Gamma^s or Gamma^u; on the graph the strict stable/unstable
graph-return bound q<1 gives contraction. The source proof of self-coherence on p.62 uses this
characterization after recentering at a plaque intersection. Equivalently, the existing
short-plaque-path calculation restricts each intersecting plaque to paths whose f-iterate
endpoints stay in the common domains centered at the intersection point. The rate1 test puts both
restricted pieces on that centered source graph. They have its dimension and are immersions, so
the local inverse theorem makes their images relative open neighborhoods there. Their intersection
is relatively open in each plaque. This is applied only to the actual diffeomorphism and its
inverse, not a disputed general singular endomorphism statement.

Retain the already written tangency calculation for these selected graphs. In their trapped graph
coordinates the forward derivative contracts by q; the graph and exponential first derivatives are
uniformly bounded on the common discs. Every stable plaque tangent vector therefore has forward
derivative bounded by K q^n times its coordinate norm. Its E^u component would grow at least
theta^(-n) under the original invariant splitting, whose projections are uniformly bounded. That
component is zero. Dimensions give tangency exactly E^s at every plaque point. Apply the same
argument to f^(-1) for E^u. Zero-dimensional fibres use the supplier's zero-coordinate case rather
than a minimum over an empty unit sphere.

GL4: HPS (6.1), pp.68–74,94–107/PDF72–78,98–111; (6B.1)–(6B.2), pp.111–113/PDF115–117. Use the
point foliation F_0: its intrinsic manifold V_0 is the disjoint union of singleton points of M.
Each component is a complete, boundaryless zero-manifold; the tangent bundle is zero, the
image/closure is compact M, and f permutes components smoothly. HPS explicitly permits this
nonseparable/disconnected leaf-manifold convention (p.68 examples and p.116), and identifies
normal hyperbolicity of the point foliation with Anosov on p.116. GL1 supplies the normal
stable/unstable splitting for the original f at every finite order. Apply the printed (6.1)
construction to this source datum. Its proof constructs uniform tubular/exponential plaque charts
(pp.94–100), the overflowing image graph transform (pp.101–105), and uses Lipschitz jets,
(6.5)–(6.7), and the Grassmann induction to obtain C^r leaf immersions (pp.105–107). Part(e) is
the strong-family construction already proved in §5, and (6B.4) applies to the selected §5 strong
plaque families themselves. We take these HPS outputs; no old private leaf atlas or cutoff-to-leaf
identification is a premise.

Continue the source plaques by the actual compact-limit argument of (6B.2). Restrict the
exponential graph parametrizations to closed discs lying strictly inside the common embedding
domain. On each closed frame core, compactness and joint continuity of each derivative through
order r give continuity of the family in the C^r supremum topology: use uniform continuity on the
core times the closed disc, for the finitely many derivative orders. Its compact parameter image
is therefore compact in the local C^r embedded-disc topology; the finite union of these images is
precompact. The embedding property holds on the common enlarged open discs because the graph
projection is injective and the exponential chart is an embedding there. This verifies precisely
the finite-r plaque precompactness used by (6B.2). The continuation for different r uses the same
source graph germs, by GL10. If a finite connected union of plaques has been continued and p is a
point on one of them, take approximating connected plaque unions, choose plaques centered at
points converging to p, and use precompactness to extract a convergent centered plaque. This is
exactly the extension step of (6B.2); its limit extends the finite union at p. Cover the boundary
of the initial closed parameter disc by interiors of these centered extensions. It is a compact
boundary covered by relatively open neighborhoods, so choose finitely many extensions. Repeat on
the newly uncovered boundaries, enumerating the finite batches. This produces a countable
connected family {β_j} continuing the initial plaque with no remaining boundary. In the
strong-plaque case self-coherence makes the extension unbranched: intersecting plaque interiors
agree on open pieces, so continuation does not insert a different branch. The source also chooses
approximating plaques p_jn with the property that, for each fixed j, p_jn intersects p_kn only for
k≤K(j), with K(j) independent of n. This bounded overlap property, source (b) on p.113, follows by
choosing extensions only at uncovered boundaries, restricting discs as in source (u) on p.112, and
using the compact family of restricted plaques. It is part of the actual construction; arbitrary
lists of immersions do not have it. The restricted property(u) and bounded-overlap property(b) are
conclusions of this source continuation, not added hypotheses. In the lemma, the approximating
unions are connected in their original intrinsic manifold: a plaque centered at a point tending to
p is appended to that same union, and precompactness extracts its centered limit. The finite-batch
boundary covering and the restricted-disc selection are exactly the mechanism on pp.112–113.
Source §6B completes the resulting leaf immersions; it does not assume the old agent atlas already
complete. Boundary/source-domain guard: the complete BOUNDARYLESS starting input is the point
carrier V_0, not a positive-radius local Wu/Ws disc from (6.1), which can have an outer boundary.
Use the actual (6B.3)/(6B.4) packaging and the (6B.2) strong-plaque boundary-extension/quotient
construction. No open local disc is assumed complete and fed into (6B.1). For point center, weak
and strong stable/unstable dimensions coincide. In (6.1) pp.101–106 the graph return is inverted
only on its restricted X(m-prime epsilon) domain whose image covers X(epsilon), with actual
overflow; no erroneous unstable subset sign from the statement on p.71 is used.

GL5: Apply the following existing quotient-chart argument to the SOURCE-SELECTED strong plaque
continuation of GL4. HPS §6B proof (6B.1), p.113, and Corollary (6B.4), p.114. Form the disjoint
union of the open parameter discs indexed by j. Identify (j,u) and (k,v) when β_j(u)=β_k(v) and
the branches are joined by the overlapping approximating plaques; use the equivalence generated by
these identifications. Let B_x be the connected continuation component. For each point u in the
j-th disc let U_jk be the open overlap domain with the k-th disc. There are only finitely many
relevant k, by source property (b), so U_j(u), the intersection of the U_jk containing u, is an
open neighborhood of u. The maps u′↦[(j,u′)] on these neighborhoods are the source quotient
charts. Unbranchedness makes their transfers β_k⁻¹∘β_j well defined and C^r on the open overlaps;
the quotient construction gives inverses onto their chart images and makes those images open. The
maps b_x([(j,u)])=β_j(u) agree on overlaps, so define a continuous C^r immersion. In the strong
self-coherent case, equal ambient image points are identified: the centered plaque at their common
image agrees locally with both representatives, and the corresponding overlap identifications join
the two representatives. This is the injectivity conclusion of (6B.4), not injectivity inferred
from merely local immersions. Its tangent space at every point is Eˢ or Eᵘ, as stated in (6B.4).
The connected glued component is boundaryless because every plaque boundary encountered in
continuation was covered by centered extensions. Source typography guard: the p.113/PDF117 display
prints beta_j(x)=beta_j(y), while its second chart index and transfer are k. Use equality of the
two actual ambient images beta_j(x)=beta_k(y), as the next printed transfer beta_k^(-1) composed
beta_j requires. This is an index typo, not a different equivalence relation.

GL6: The source manifold assertion on HPS p.113 includes the following elementary topology checks.
Each chart domain is an open subset of a finite-dimensional Euclidean space. Only countably many
original discs occur; their open subcharts have a countable refinement obtained from rational
Euclidean balls. The images of these balls form a countable base for the quotient-chart topology,
hence B_x is second countable. For distinct p,q∈B_x, injectivity of b_x gives distinct image
points in the Hausdorff manifold M. Choose disjoint ambient open neighborhoods and pull them back
by the continuous b_x; these separate p and q, hence B_x is Hausdorff. Connectedness follows
because the initial plaque and every subsequent centered extension join through a nonempty open
overlap; each finite continuation union is connected, and their increasing union is connected.
These checks refer to the intrinsic chart topology. They do not identify it with the ambient
subspace topology, and do not require properness of b_x. HPS p.114/PDF118 also proves that the
continued map is a leaf immersion, using compactness of the restricted plaque family for
pullback-Finsler completeness and its finite-order tangent extension. Its common centered inner
plaque charts and uniform metric comparisons are those established in (6.2) and the proof of
(6.7), pp.72–74 and 86. Use the actual uniform estimates (1),(2) in the proof of (6.7), printed
p.86/PDF90: there is xi>0 such that intrinsic distance from a plaque center below xi puts a point
in its centered plaque, and intrinsic and plaque-coordinate distances have uniform two-sided
comparison. The source proves these estimates by the positive boundary-exit length, not by
summability of an arbitrary Cauchy tail. Fix a sufficiently late Cauchy index p so every
subsequent term has intrinsic distance from p below xi and below the threshold for a closed inner
parameter disc. All these terms then lie in the SAME centered inner plaque; their coordinates are
Cauchy by the lower comparison. The compact closed inner disc supplies a limit, and the upper
comparison gives pullback-metric convergence. Centered continuation plaques are available at every
point, so a chart boundary is not an uncovered leaf boundary. This is the compactness step written
tersely on p.114, not completeness of an arbitrary immersed image or ambient subspace topology.
The source convention allows the disjoint union of connected intrinsic components; each component
has the countable Hausdorff manifold topology proved above.

GL7: HPS (6B.3)–(6B.4), printed p.114/PDF118, and (7.5)–(7.6), pp.127–129/PDF131–133. The point
foliation F_0 from GL4 is a C-infinity foliation of all M and has unique path lifting: a C1 path
with zero tangent is contained in its point leaf. The normally hyperbolic source leaf immersions
and the §5 strong plaque continuation therefore give the printed invariant Ws,Wu; (6B.4) gives
injectively immersed strong laminae tangent E^s,E^u. Follow the actual proof of (7.5)(b). For a
short C1 path x_t tangent to Wu, the strong unstable plaque at x_t meets a stable plaque at x_0 in
a unique point y_t; the source local plaque coordinates give a C1 path y_t tangent to F_0. It
stays in its original point leaf, so x_t stays in the original Wu lamina. The stable argument
reverses time. Part(c) supplies unique path lifting for F_0, and (7.6) concludes that Ws and Wu
are unbranched C1 laminations, with unique path lifting. The source construction identifies their
compatible continuation germs; it is not a conclusion about an arbitrary unrelated graph family.

Use the source definitions exactly: on p.115/PDF119 a continuous foliation is a partition into
connected injectively immersed leaves with ambient C0 product boxes, and an unbranched C^r
lamination is that continuous foliation with coherently immersed C^r leaves. Thus the actual
unbranched-lamination output supplies the ambient boxes; no transversely smooth foliation is
asserted. On p.116/PDF120 its leaf manifold has the intrinsic NON-induced topology. The source
invariance carries the lamina through x onto the one through fx. The original f is used throughout
GL1–GL3, so no iterate-to-original comparison is needed. The eventual-normal-hyperbolicity
argument on p.52/PDF56 is consistent with this scope but is not a hidden hypothesis or alternate
construction.

GL10: HPS (5.1), pp.54–58/PDF58–62; (5.4), pp.60–61/PDF64–65; first proof of (5.5),
pp.61–63/PDF65–67; and the written uniform regularity proof (6.5)–(6.7), pp.80–93/PDF84–97.
Printed (5.4) explicitly permits 1<=r<=infinity. Retain the single source-selected smooth G from
GL2. The actual derivative-block constants alpha_* and k_* have BOTH been made<1 at the initial
first-order choice; hence k_* alpha_*^j<1 and alpha_* k_*^j<1 for every positive j. These are
precisely the all-order strong graph/jet domination inequalities used in (5.1)/(5.4), not an
assertion that fixed T norms equal the actual derivative norms. Higher derivatives need only exist
with the source finite-order continuity/uniformity; they need not be small.

For each finite r, follow the SAME source weighted graph transform and its
differentiable-jet/continuous derivative-section proof. Its C0 fixed section is unique on the
fixed complete centered unit-slope carrier, so the higher-regularity output is the already
selected graph, not a graph on an independently selected global cutoff. The local uniqueness in
(5.4) likewise identifies restrictions of the strong germs. For each finite r, the parameter
version on p.62 gives C^r continuity on common local discs at that order, so the compact
plaque-family/precompactness argument of GL4 applies for that r. Local discs/coordinate charts may
be restricted at a given order; no common lower radius for ALL orders is required. In the
leaf-immersion proof, (6.7) constructs the uniform connection and slope carrier, obtains the
differentiable fixed jets, locates the tangent graph section and inducts on r (pp.85–93); (6.6)
then upgrades the source immersion through the Grassmann construction (pp.83–84), as used in (6.1)
pp.105–107. This is the published regularity mechanism, replacing the old
suspension/section-superposition/Pötzsche/Wells route.

The continuation uses the same unbranched source germs and has the intrinsic topology already
fixed in GL5–GL9. Every finite-order chart transfer is the source plaque inverse composed with a
source plaque chart; its inverse has that regularity on the open overlap. Thus the same connected
intrinsic laminae are smooth, injectively immersed and tangent to the original splitting. The
fixed source G and its fixed C0 graph are unchanged across orders. The source
C-infinity/local-germ argument does not interchange order-dependent cutoffs or assume an all-order
common chart radius. HPS p.128/PDF132 explicitly states that every submanifold tangent to the
source uniquely integrable lamination field lies in a leaf; (7.5)/(7.6) and the local strong-germ
uniqueness therefore bind the finite-order source immersions to the same C1 intrinsic leaves. At
each point their local source plaque charts are the same germs, so the fixed intrinsic topology
receives all finite-order regularity. No arbitrary C1 reparameterization or transverse smoothing
is used. On a stratum where E^s has rank zero the stable plaques and leaves are points; where E^u
has rank zero the unstable plaques and leaves are points; on empty M the lamination is empty and
all point-indexed conclusions are vacuous.
-/
theorem anosov_global_lamination_tensor [FiniteDimensional ℝ E]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (h : Nonempty (TensorAnosovBounds f S g)) :
    HasNativeLamination S.stable.toDistribution f (fun _ _ _ ↦ True) ∧
    HasNativeLamination S.unstable.toDistribution f (fun _ _ _ ↦ True) := by
  classical
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := inferInstance
  have hcont : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := by
    change letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
      IsContinuousRiemannianBundle E
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
    infer_instance
  let : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := hcont
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hb : BundleAnosovBounds f S := by
    exact tensorAnosovBounds_to_bundle f S g h
  obtain ⟨hs, hu⟩ := anosov_global_lamination_distance M f S hb
  constructor
  · rcases hs with ⟨ι, L, r, top, charts, smooth, F, boxes, invariant,
      families, coherent, _⟩
    exact ⟨ι, L, r, top, charts, smooth, F, boxes, invariant, families, coherent, trivial⟩
  · rcases hu with ⟨ι, L, r, top, charts, smooth, F, boxes, invariant,
      families, coherent, _⟩
    exact ⟨ι, L, r, top, charts, smooth, F, boxes, invariant, families, coherent, trivial⟩


end HolomorphicAnosov.HPS
