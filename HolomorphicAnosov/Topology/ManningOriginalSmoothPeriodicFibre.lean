import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Topology.PeriodicPointOfFiniteInvariant
import HolomorphicAnosov.Topology.RestrictedTransitivityOfAmbient
import HolomorphicAnosov.Topology.IntegralToralMapRealLift
import HolomorphicAnosov.Topology.ShortIntegerLatticeVectorZero
import HolomorphicAnosov.Topology.TorusDisplacementHasNormBoundedLift
import HolomorphicAnosov.Topology.ShortToralLiftsExactRecurrence
import HolomorphicAnosov.Topology.IntegralToralMapSub
import HolomorphicAnosov.Topology.IntegralToralMapComp
import HolomorphicAnosov.Topology.IntegralToralMapInjective
import HolomorphicAnosov.Topology.CodingIntegerCovariance
import HolomorphicAnosov.Topology.FactorNaturalCovariance
import HolomorphicAnosov.Topology.FactorIntegerRecurrence
import HolomorphicAnosov.Topology.FactorEqualIntegerOrbits
import HolomorphicAnosov.Topology.FactorPeriodicStride
import HolomorphicAnosov.Topology.ExistsFullLengthMetric
import HolomorphicAnosov.Topology.EdistLtTopOfSameComponent
import HolomorphicAnosov.Topology.OriginalTensorExistsBowenMetric
import HolomorphicAnosov.Topology.SpliceAtInteger
import HolomorphicAnosov.Topology.SymbolicSplicePeriodic
import HolomorphicAnosov.Topology.CodeShiftIterateCoordinate
import HolomorphicAnosov.Topology.PeriodicPointFromClosedCodeFibre
import HolomorphicAnosov.Topology.ToralBiInfiniteExpansivity
import HolomorphicAnosov.Topology.PeriodicFibreFromBowenCoding
import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.Connected.Clopen

/-!
# Periodic points in periodic fibres of the original smooth semiconjugacy

Source: Manning, *There are No New Anosov Diffeomorphisms on Tori* (1974),
Lemma 6, pp.427–428. The original smooth source and basic-set hypotheses are
retained; no standard smooth structure or group law on the source is used.
DAG node: `topo.manning_original_smooth_periodic_fibre_g7`.
-/

namespace HolomorphicAnosov

open Set
open scoped Manifold ContDiff ENNReal Bundle

/-- Extract the literal Bowen coding tuple from the original geometric datum
WHEN the selected metric has the provider's actual full-length compatibility.
Source: Bowen Fact1/Theorem28 pp.726–727/742; Manning Lemma6 Step2. This private
caller adapter does not assert that the parent's LOCAL length identity is global.
The full-length metric must first be constructed separately. The tangent norm is
that of the supplied original tensor, not a comparison with an unrelated norm.
Extend the subbundles arbitrarily by zero OFF the invariant set, preserving their
literal subspace topology and all their original on-set fields. -/
private theorem coding_from_original_datum_full_length
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (htransitive : ∀ P Q : Set M, IsOpen P → IsOpen Q →
      (Λ ∩ P).Nonempty → (Λ ∩ Q).Nonempty →
      ∃ k : ℕ, ∃ x ∈ Λ ∩ P, ((f : M → M)^[k]) x ∈ Q) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨H.originalMetric.toRiemannianMetric⟩
    BowenBasicSetCoding.HasOriginalRiemannianDistance (E := E) (M := M) →
    ∃ (hΛ : ∀ x : M, x ∈ Λ ↔ f x ∈ Λ),
      let F := BowenBasicSetCoding.restrictedDynamics f.toHomeomorph Λ hΛ
      ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (B : Fin N → Fin N → Prop)
        (R : Fin N → Set Λ) (coding : BowenBasicSetCoding.CodeSpace B → Λ),
        (∀ a, {x : Λ | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) ∧
        Continuous coding ∧ Function.Surjective coding ∧
        (∀ a, coding (BowenBasicSetCoding.codeShift B a) = F (coding a)) ∧
        (∀ a b : BowenBasicSetCoding.CodeSpace B, a.val 0 = b.val 0 →
          ∃ c : BowenBasicSetCoding.CodeSpace B,
            (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
            (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
            (∀ j : ℤ, 0 ≤ j → dist ((F ^ j) (coding c)) ((F ^ j) (coding b)) < ε) ∧
            (∀ j : ℤ, j ≤ 0 → dist ((F ^ j) (coding c)) ((F ^ j) (coding a)) < ε)) := by
  classical
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  intro hmetric
  have hΛ : ∀ x : M, x ∈ Λ ↔ f x ∈ Λ := by
    intro x
    constructor
    · intro hx
      exact H.forward_mem hx
    · intro hfx
      simpa using H.backward_mem hfx
  let F := BowenBasicSetCoding.restrictedDynamics f.toHomeomorph Λ hΛ
  let stable : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x) := fun x ↦
    if hx : x ∈ Λ then H.stable.fibre ⟨x, hx⟩ else ⊥
  let unstable : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x) := fun x ↦
    if hx : x ∈ Λ then H.unstable.fibre ⟨x, hx⟩ else ⊥
  have hstable : (fun x : Λ ↦ stable x.val) = H.stable.fibre := by
    funext x
    simp only [stable, dite_eq_left x.property]
  have hunstable : (fun x : Λ ↦ unstable x.val) = H.unstable.fibre := by
    funext x
    simp only [unstable, dite_eq_left x.property]
  have hstablec : BowenBasicSetCoding.IsContinuousDistributionOn Λ stable := by
    unfold BowenBasicSetCoding.IsContinuousDistributionOn
    have hh := H.stable.locally_trivial
    rw [← hstable] at hh
    exact hh
  have hunstablec : BowenBasicSetCoding.IsContinuousDistributionOn Λ unstable := by
    unfold BowenBasicSetCoding.IsContinuousDistributionOn
    have hh := H.unstable.locally_trivial
    rw [← hunstable] at hh
    exact hh
  have hcompl : ∀ x ∈ Λ, IsCompl (stable x) (unstable x) := by
    intro x hx
    simpa only [stable, unstable, dite_eq_left hx] using H.complementary ⟨x, hx⟩
  have hstableinv : ∀ x ∈ Λ,
      (stable x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap = stable (f x) := by
    intro x hx
    simpa only [stable, dite_eq_left hx, dite_eq_left (H.forward_mem hx)] using H.stable_invariant ⟨x, hx⟩
  have hunstableinv : ∀ x ∈ Λ,
      (unstable x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap = unstable (f x) := by
    intro x hx
    simpa only [unstable, dite_eq_left hx, dite_eq_left (H.forward_mem hx)] using H.unstable_invariant ⟨x, hx⟩
  have hnorm : ∀ {x : M} (v : TangentSpace 𝓘(ℝ, E) x),
      hyperbolicRiemannianNorm H.originalMetric v = ‖v‖ := by
    intro x v
    exact (norm_eq_sqrt_real_inner v).symm
  have hstablebound : ∀ (k : ℕ) (x : M), x ∈ Λ → ∀ v ∈ stable x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f : M → M)^[k]) x v‖ ≤ H.C * H.rate ^ k * ‖v‖ := by
    intro k x hx v hv
    have hh := H.stable_estimate k ⟨x, hx⟩ v (by simpa only [stable, dite_eq_left hx] using hv)
    simpa only [hnorm] using hh
  have hunstablebound : ∀ (k : ℕ) (x : M), x ∈ Λ → ∀ v ∈ unstable x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f.symm : M → M)^[k]) x v‖ ≤ H.C * H.rate ^ k * ‖v‖ := by
    intro k x hx v hv
    have hh := H.unstable_estimate k ⟨x, hx⟩ v (by simpa only [unstable, dite_eq_left hx] using hv)
    simpa only [hnorm] using hh
  have hlocal : ∃ U : Set M, IsOpen U ∧ Λ ⊆ U ∧
      Λ = ⋂ j : ℤ, ((f.toHomeomorph ^ j : M ≃ₜ M) : M → M) '' U := by
    refine ⟨H.isolatingNeighborhood, H.isolating_open, H.subset_isolating, ?_⟩
    ext x
    rw [H.locally_maximal]
    simp only [mem_iInter]
    constructor
    · intro hx j
      refine ⟨(f.toHomeomorph ^ (-j)) x, hx (-j), ?_⟩
      rw [← Homeomorph.mul_apply, ← zpow_add]
      simp
    · intro hx j
      obtain ⟨y, hy, heq⟩ := hx (-j)
      change (f.toHomeomorph ^ j) x ∈ H.isolatingNeighborhood
      rw [← heq, ← Homeomorph.mul_apply, ← zpow_add]
      simpa using hy
  have htrans :
      ∀ U V : Set Λ, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ k : ℕ, (((F ^ k : Λ ≃ₜ Λ) : Λ → Λ) '' U ∩ V).Nonempty :=
    restricted_transitivity_of_ambient f.toHomeomorph Λ hΛ htransitive
  refine ⟨hΛ, ?_⟩
  dsimp only
  intro ε hε
  obtain ⟨N, D, hN, hD, δ, hδ, γ, hγ, R, hrect, hdisjoint, hcover, hmarkov,
    coding, hcode, hccont, hcsurj, hcov, hfibre, hlabel, hperiodic, hsplice⟩ :=
    BowenBasicSetCoding.hyperbolic_basic_set_markov_coding f hmetric Λ H.nonempty H.compact hΛ
      stable unstable hstablec hunstablec hcompl hstableinv hunstableinv H.C H.rate
      H.one_le_C H.rate_pos H.rate_lt_one hstablebound hunstablebound hlocal htrans ε hε
  exact ⟨N, BowenBasicSetCoding.transition F R, R, coding, hcode, hccont, hcsurj, hcov, hsplice⟩


/-- A periodic target fibre contains an original source periodic point in the
surjecting hyperbolic basic set; the source period need not be the target period.

The finite-dimensional whole-space real model is boundaryless. The metric-space
instance gives the original topology and original finite distance. Its local
identity with the piecewise-smooth length infimum of the ORIGINAL metric tensor
binds the given compatible Riemannian distance, allowing disconnected source
manifolds. No global distance equality between different components is imposed.
`HyperbolicSetFactOneDatum` is concrete input data: the original continuous stable
and unstable subbundles on Λ, complementarity and invariance, the smooth tensor,
all-natural-iterate C*rate^k derivative bounds, and the isolating open set. No
adapted metric, coding, rectangle, fibre bound or periodic point is assumed.
The ambient-open-set formulation of transitivity is exactly transitivity on the
original subspace Λ. The integer matrix acts by the existing row-coordinate
`integralToralMap`, and its actual complex eigenvalues have modulus different
from one. The semiconjugacy is only continuous, not injective or a conjugacy.
The dimension n=0 is included. Positive integer target/source periods are encoded
by natural numbers with the explicit lower bound one.

Complete current natural-language proof:
Manning, There are No New Anosov Diffeomorphisms on Tori (1974), Lemma6 and its proof pp427–428, using the distinct compact smooth source in Lemmas3–4 p427. The proof uses only the source basic-set Markov coding, semiconjugacy and target hyperbolic canonical coordinates; it does not use a standard smooth structure or group operation on the source. Bowen, Topological entropy and Axiom A, Global analysis partI pp36–37 Proposition6.2, expands the symbolic local-product/finite-type step; Bowen Markov Partitions1970 Lemma27/Theorem28 pp741–742 supply the precise coding prerequisite.

1. Uniform target expansivity
The real hyperbolic splitting makes every bounded all-integer A-orbit zero. Choose e>0 small enough that each torus displacement of distance≤e has a unique representative v of Euclidean norm≤a, where (‖A‖+1)a<1 and a<1/2. If two torus orbits remain e-close at every integer time, their chosen representatives v_j satisfy v_(j+1)−Av_j∈Z^n with norm<1, hence this integer vector is zero. Thus v_j=A^jv_0 is bounded for all j, giving v_0=0. This proves expansivity for g. For n=0 the torus is a singleton and the assertion is automatic. Uniform continuity of h on compact M now gives δ>0 such that d(x,y)<δ implies target distance<e.
Providers: linear.hyperbolic_real_splitting, mathlib.isCompact_uniformContinuousOn_of_continuous.

2. Code the original hyperbolic basic set
For the Lean distance guard, first install the native Riemannian bundle of
H.originalMetric, so every tangent norm is exactly the original tensor norm.
Mathlib's EMetricSpace.ofRiemannianMetric gives the native C¹ path-length extended
metric with the ORIGINAL topology. Its finite-edistance classes are open and
closed. M is the topological disjoint union of those literal classes; give each
its full finite distance, use Metric.Sigma.metricSpace, and pull that metric back
through the fibre homeomorphism. The resulting finite metric retains the original
topology and every finite native extended distance. Each connected component is
contained in a finite-edistance class, so this metric satisfies Bowen's literal
HasOriginalRiemannianDistance. No equality between piecewise-smooth and C¹ infima,
or between the supplied distance and global path distance, is inferred from hd.
The public local hypothesis hd is retained but is unnecessary for this route.
This is a Mathlib implementation of Manning's choice of a compatible Riemannian
metric; no different smooth structure or extra hyperbolicity premise is used.
Compactness makes h uniformly continuous in THIS metric, giving the δ used in
Steps1 and3. Apply Bowen with mesh ε<δ and the unchanged original splitting and
constants. Write π:Σ_B→Λ for its continuous surjection, σ for its shift and
ℓ=h∘π. The set L={a∈Σ_B:ℓ(a)=z} is nonempty by hΛ=T^n and π surjectivity,
closed, compact and σ^q-invariant in both directions because g^qz=z. It need
not be σ-invariant for q>1. All subsequent distance bounds use this same metric;
the conclusion is metric-free, so no comparison with the supplied distance is needed.
Providers: dynamics.bowen_hyperbolic_basic_set_markov_coding_g7,
mathlib.riemannian_metric_space, mathlib.equiv_sigmaFiberEquiv,
mathlib.metric_sigma_disjoint_union_g4, mathlib.embedding_comap_metric_g4,
mathlib.isCompact_iff_compactSpace and the original compactness/covariance leaves.

3. Periodic fibre is closed under guarded block splicing
Group coordinates into q-blocks a_(qk),…,a_(qk+q−1), which is a homeomorphism between full finite-alphabet sequence spaces commuting with σ^q and the one-block shift. For a,b∈L with the same zeroth q-block, splice c from a on j≤0 and b on j≥0. The coding theorem makes c admissible and its image δ-close to the f-orbit of π(b) for j≥0 and π(a) for j≤0. Semiconjugacy and uniform continuity therefore make g^jℓ(c) e-close to g^jz at every integer j. Covariance for negative j follows by applying the positive equation to f⁻¹ and g⁻¹. Expansivity gives ℓ(c)=z, so c∈L. In block coordinates this is exactly concatenation of the past and future at an equal current block. It does not assert that every arbitrary closed invariant subshift contains a periodic code.
Providers: dynamics.bowen_hyperbolic_basic_set_markov_coding_g7, mathlib.isCompact_uniformContinuousOn_of_continuous, mathlib.function_semiconj_iterate_right.

4. Finite graph periodic code, with the omitted source step expanded
Let V be the finite set of q-block symbols occurring in L, and give it an arrow u→v when some element of L has these consecutive blocks. Every finite directed path occurs in an element of L: the one-edge case is its definition; append an edge by shifting its witnessing code so its first symbol is the final symbol of the old path, and splice there. Shift-invariance and the preceding closure preserve L. Every bi-infinite directed path belongs to L: for each N choose a code in L agreeing with it on [−N,N]; compactness supplies a convergent subsequence in L, and every coordinate eventually agrees with the prescribed path, so its limit is that path. For an element of the nonempty L, among |V|+1 consecutive future symbols two agree. The intervening positive-length path is a directed cycle; repeat it bi-infinitely. The previous argument puts this periodic block code in L. This is the finite-type conclusion of Bowen Proposition6.2 pp36–37 with its finite-word induction specialized to the stronger equal-symbol splice property proved here. A transient allowed vertex need not itself be periodic; only one cycle is required.
Providers: mathlib.isCompact_tendsto_subseq, mathlib.isCompact_univ_pi, mathlib.isClosed_isCompact.

5. Project the code and check periods
If the periodic block code has period p≥1, the original code has σ^(qp)a=a. Covariance gives f^(qp)π(a)=π(a), and a∈L gives hπ(a)=z. Put x=π(a),r=qp. All rectangle boundary memberships are retained in the coding theorem; no interior itinerary or one-to-one coding assumption is used. Empty Λ is excluded and zero-dimensional source plaques cause no change to the finite graph argument.
Providers: mathlib.function_semiconj_iterate_right.
-/
theorem manning_original_smooth_periodic_fibre
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (Λ : Set M)
    (H : HyperbolicSetFactOneDatum f Λ)
    (_hd : ∀ x : M, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V,
        ENNReal.ofReal (dist y z) = piecewiseSmoothRiemannianEDist H.originalMetric y z)
    (htransitive : ∀ P Q : Set M, IsOpen P → IsOpen Q →
      (Λ ∩ P).Nonempty → (Λ ∩ Q).Nonempty →
      ∃ k : ℕ, ∃ x ∈ Λ ∩ P, ((f : M → M)^[k]) x ∈ Q)
    (n : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hhyperbolic : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1)
    (h : M → UnitAddTorus (Fin n)) (hcontinuous : Continuous h)
    (hsemiconj : ∀ x : M, h (f x) = integralToralMap A (h x))
    (honto : h '' Λ = Set.univ) :
    ∀ (z : UnitAddTorus (Fin n)) (q : ℕ), 1 ≤ q →
      ((integralToralMap A)^[q]) z = z →
      ∃ x ∈ Λ, h x = z ∧ ∃ r : ℕ, 1 ≤ r ∧ ((f : M → M)^[r]) x = x := by
  classical
  intro z q hq hz
  by_cases hfinite : Λ.Finite
  · have hzimage : z ∈ h '' Λ := by rw [honto]; trivial
    obtain ⟨x, hx, hxh⟩ := hzimage
    obtain ⟨r, hr, hfix⟩ :=
      periodic_point_of_finite_invariant (f : M → M) f.injective Λ hfinite
        H.forward_mem x hx
    exact ⟨x, hx, hxh, r, hr, hfix⟩
  · let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨H.originalMetric.toRiemannianMetric⟩
    let tM : TopologicalSpace M := inferInstance
    obtain ⟨d, ht, hmetric⟩ := original_tensor_exists_bowen_metric (tM := tM) H.originalMetric
    let : MetricSpace M := @MetricSpace.replaceTopology M tM d ht.symm
    obtain ⟨hΛ, hcoding⟩ := coding_from_original_datum_full_length f Λ H htransitive hmetric
    let F := BowenBasicSetCoding.restrictedDynamics f.toHomeomorph Λ hΛ
    have : CompactSpace Λ := isCompact_iff_compactSpace.mp H.compact
    have hcont : Continuous (fun x : Λ ↦ h x.val) :=
      hcontinuous.comp continuous_subtype_val
    have hsem : ∀ x : Λ, h (F x).val = integralToralMap A (h x.val) := by
      intro x
      exact hsemiconj x.val
    have hsurj : Function.Surjective (fun x : Λ ↦ h x.val) := by
      intro y
      have hy : y ∈ h '' Λ := by rw [honto]; trivial
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, hxy⟩
    obtain ⟨x, hx, r, hr, hfix⟩ := periodic_fibre_from_bowen_coding F A hhyperbolic
      (fun x : Λ ↦ h x.val) hcont hsem hsurj hcoding z q hq hz
    have hiter : ∀ k : ℕ, ((F : Λ → Λ)^[k] x).val = ((f : M → M)^[k]) x.val := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact congrArg f ih
    refine ⟨x.val, x.property, hx, r, hr, ?_⟩
    rw [← hiter]
    exact congrArg Subtype.val hfix

end HolomorphicAnosov

















