import HolomorphicAnosov.Topology.Franks.OriginalCoverCorrectionProper
import HolomorphicAnosov.Topology.Franks.NativePointedSemiconjugacy
import HolomorphicAnosov.Topology.Franks.GlobalProductInjectivity
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.PathDecay
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.AsymptoticQuotientIff
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.FullDecaySubmodule
import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRange
import HolomorphicAnosov.Geometry.IntrinsicCoveringPullbackLeaf
import HolomorphicAnosov.Paper.Ghys.InjectivePointedLeafLift
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicZpowRemainder
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import HolomorphicAnosov.Targets.Theorem12Support.RealQuotientTorus
import HolomorphicAnosov.Targets.Theorem12Support.IntegerLatticePreservation
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Convex.Contractible

/-!
# Original-cover global-product geometry

Franks (1969), Lemma 1.6 and §1.8, pp.120–123. All coordinates in this
module are topological covering coordinates; no smooth atlas is transported
through a topological equivalence with a torus.
-/

namespace HolomorphicAnosov.FranksOriginalCover

open scoped ContDiff Manifold _root_.Topology
open Filter

/-! **Source and proof.**  The native hyperbolic splitting theorem uses powers
of the continuous linear equivalence, while the lifted-leaf statements use
function iterates.  The two expressions agree by
`ContinuousLinearEquiv.toLinearEquiv_pow` and `LinearEquiv.pow_apply`.  We
record this harmless adapter explicitly, then transport the `IsCompl`
conclusion of `hyperbolic_decay_space_complement` to the exact submodules used
by the Franks leaf argument.  This is the finite-dimensional hyperbolic
splitting source used in Alves, Theorem 5.5, pp.16--17; no native lamination or
global-product assumption enters the argument. -/
theorem full_decay_submodule_isCompl_of_hyperbolic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V ≃L[ℝ] V)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ →
        ‖μ‖ ≠ 1) :
    IsCompl (fullDecaySubmodule A) (fullDecaySubmodule A.symm) := by
  have hiter (B : V ≃L[ℝ] V) (v : V) (n : ℕ) :
      (B : V → V)^[n] v = (B ^ n) v := by
    have hp := congrArg (fun e : V ≃ₗ[ℝ] V => e v)
      (ContinuousLinearEquiv.toLinearEquiv_pow B n)
    change (B.toLinearEquiv : V → V)^[n] v = (B ^ n).toLinearEquiv v
    have hp' := hp.symm
    rw [LinearEquiv.pow_apply] at hp'
    exact hp'
  have hiter_iff (B : V ≃L[ℝ] V) (v : V) :
      v ∈ fullDecaySubmodule B ↔
        Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 (0 : V)) := by
    constructor
    · intro h
      change Tendsto (fun n : ℕ ↦ (B : V → V)^[n] v) atTop (𝓝 (0 : V)) at h
      exact h.congr (fun n ↦ hiter B v n)
    · intro h
      exact h.congr (fun n ↦ (hiter B v n).symm)
  obtain ⟨S, U, hS, hU, hSU, _⟩ :=
    HolomorphicAnosov.hyperbolic_decay_space_complement A hA
  have hS' : S = fullDecaySubmodule A := by
    ext v
    exact (hS v).trans (hiter_iff A v).symm
  have hU' : U = fullDecaySubmodule A.symm := by
    ext v
    exact (hU v).trans (hiter_iff A.symm v).symm
  rw [← hS', ← hU']
  exact hSU

/-- Stable and unstable decay spaces have zero intersection. -/
theorem full_decay_submodule_disjoint_of_hyperbolic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V ≃L[ℝ] V)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) :
    Disjoint (fullDecaySubmodule A) (fullDecaySubmodule A.symm) :=
  (full_decay_submodule_isCompl_of_hyperbolic A hA).disjoint

/-- Forward asymptotic pairs map to decaying differences in the quotient under
a continuous semiconjugacy. This is the forward compact-uniform-continuity
argument of Franks' affine leaf-image proof. Iterating the semiconjugacy identifies
the quotient orbit with the difference of the two image orbits. Uniform
continuity carries their vanishing distance to vanishing quotient norm.
Unlike the reverse implication, this uses no inverse of the semiconjugacy. -/
theorem asymptotic_quotient_of_continuous_semiconjugacy
    {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace M] [CompactSpace M]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (A : V ≃L[ℝ] V) (f : M ≃ₜ M) (h : C(M, V ⧸ Γ.toAddSubgroup))
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup))
    (x z : M) (vx vz : V)
    (hx : (QuotientAddGroup.mk vx : V ⧸ Γ.toAddSubgroup) = h x)
    (hz : (QuotientAddGroup.mk vz : V ⧸ Γ.toAddSubgroup) = h z)
    (hasym : ForwardAsymptotic f x z) :
    Tendsto (fun n : ℕ ↦ (QuotientAddGroup.mk ((A : V → V)^[n] (vz - vx)) :
      V ⧸ Γ.toAddSubgroup)) atTop (𝓝 0) := by
  let : IsClosed (Γ.toAddSubgroup : Set V) := AddSubgroup.isClosed_of_discreteTopology
  have hi : ∀ (n : ℕ) (w : M) (v : V),
      (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h w →
      h ((f : M → M)^[n] w) = QuotientAddGroup.mk ((A : V → V)^[n] v) := by
    intro n
    induction n with
    | zero => intro w v hv; exact hv.symm
    | succ n ih =>
      intro w v hv
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hc _ _ (ih w v hv).symm
  have hsub : ∀ n : ℕ, (A : V → V)^[n] (vz - vx) =
      (A : V → V)^[n] vz - (A : V → V)^[n] vx := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sub]
  have hd : ∀ n : ℕ, ‖(QuotientAddGroup.mk ((A : V → V)^[n] (vz - vx)) :
      V ⧸ Γ.toAddSubgroup)‖ =
      dist (h ((f : M → M)^[n] z)) (h ((f : M → M)^[n] x)) := by
    intro n
    rw [hi n x vx hx, hi n z vz hz, dist_eq_norm, hsub]
    exact congrArg norm ((QuotientAddGroup.mk' Γ.toAddSubgroup).map_sub _ _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [hd]
  have hh : Tendsto (fun w : M × M ↦ (h w.1, h w.2)) (uniformity M)
      (uniformity (V ⧸ Γ.toAddSubgroup)) :=
    CompactSpace.uniformContinuous_of_continuous h.continuous
  have hs : Tendsto (fun n : ℕ ↦ ((f : M → M)^[n] z, (f : M → M)^[n] x))
      atTop (uniformity M) := tendsto_uniformity_iff_dist_tendsto_zero.mpr hasym
  exact tendsto_uniformity_iff_dist_tendsto_zero.mp (hh.comp hs)

/-- The path-decay argument with a continuous corrected lift.  The upstream
`path_decay` theorem is packaged for a homeomorphism because its converse
affine-image half needs an inverse; the forward argument itself only uses
continuity and the quotient projection identity. -/
theorem path_decay_of_continuous_lift
    {V M Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MetricSpace M] [CompactSpace M]
    [TopologicalSpace Y]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (A : V ≃L[ℝ] V) (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (f : M ≃ₜ M) (h : C(M, V ⧸ Γ.toAddSubgroup))
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup))
    (p : Y → M) (H : C(Y, V))
    (hH : ∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y))
    (y z : Y) (η : Path y z)
    (hη : ∀ t, ForwardAsymptotic f (p y) (p (η t))) :
    H z - H y ∈ fullDecaySubmodule A := by
  classical
  let S := fullDecaySubmodule A
  let : IsClosed (S : Set V) := S.closed_of_finiteDimensional
  let k : unitInterval → V ⧸ S := fun t ↦ S.mkQ (H (η t) - H y)
  have hk : Continuous k :=
    S.continuous_mkQ.comp ((H.continuous.comp η.continuous).sub continuous_const)
  have hcount : (Set.range (fun g : Γ ↦ S.mkQ (g : V))).Countable := Set.countable_range _
  have hrange : Set.range k ⊆ Set.range (fun g : Γ ↦ S.mkQ (g : V)) := by
    rintro _ ⟨t, rfl⟩
    have hq := asymptotic_quotient_of_continuous_semiconjugacy Γ A f h hc (p y) (p (η t))
      (H y) (H (η t)) (hH y) (hH (η t)) (hη t)
    obtain ⟨g, hg⟩ := lattice_capture Γ A hΓ (H (η t) - H y) hq
    refine ⟨g, ?_⟩
    have hm : H (η t) - H y - (g : V) ∈ S := hg
    have hz : S.mkQ (H (η t) - H y - (g : V)) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hm
    exact sub_eq_zero.mp (by simpa only [k, map_sub] using hz) |>.symm
  have hs : (Set.range k).Subsingleton := hcount.isTotallyDisconnected _ hrange
    (isPreconnected_range hk)
  have he := hs (Set.mem_range_self (0 : unitInterval)) (Set.mem_range_self (1 : unitInterval))
  have hz : S.mkQ (H z - H y) = 0 := by
    simpa [k] using he.symm
  exact (Submodule.Quotient.mk_eq_zero S).mp hz

/-! The next helper is the one-sided native leaf statement needed by the
global-product argument.  It uses the actual intrinsic path range and the
quotient decay theorem; it does not assume that the corrected lift is
injective or surjective. -/

/-- Every lifted path in an original asymptotic carrier has corrected-lift
image in the affine full-decay subspace.

The proof is the forward half of Franks' leaf-image argument.  A point in the
marked lifted range comes with a native path whose projection stays in the
same asymptotic carrier.  `path_decay` then puts the difference of its two
corrected-lift coordinates in `fullDecaySubmodule A`, which is exactly the
claimed translated affine image. -/
theorem forward_affine_leaf_image
    {V M Y L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MetricSpace M] [CompactSpace M]
    [TopologicalSpace Y] [TopologicalSpace L] [PathConnectedSpace L]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (A : V ≃L[ℝ] V) (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (f : M ≃ₜ M) (h : C(M, V ⧸ Γ.toAddSubgroup))
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup))
    (p : Y → M) (_hp : IsCoveringMap p) (H : C(Y, V))
    (hH : ∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y))
    (y : Y) (j : L → M) (_hj : Continuous j) (a : L) (_ha : j a = p y)
    (hcarrier : ∀ b, ForwardAsymptotic f (p y) (j b)) :
    H '' liftedIntrinsicLeafRange p j a y ⊆
      (fun v : V ↦ H y + v) '' (fullDecaySubmodule A : Set V) := by
  rintro w ⟨z, hz, rfl⟩
  obtain ⟨b, γ, η, hη⟩ := hz
  have hdec : H z - H y ∈ fullDecaySubmodule A :=
    path_decay_of_continuous_lift Γ A hΓ f h hc p H hH y z η
      (fun t ↦ by simpa only [hη t] using hcarrier (γ t))
  exact ⟨H z - H y, hdec, by abel_nf⟩

/-! The preceding decay argument is stated for the native real quotient.  The
original Franks parent stores its torus model as `UnitAddTorus`; the following
adapter is the exact coordinate bridge used when instantiating that argument.
It is deliberately phrased only with the parent data and the canonical
quotient homeomorphism, so no torus conjugacy is smuggled into the proof. -/

open Theorem12RealQuotientTorus

/-! **Source and proof.**  The source is the coordinate quotient construction
`Targets/Theorem12Support/RealQuotientTorus.lean`, especially
`quotientTorusHomeomorph_matrix`, which proves on representatives that the
integer matrix action descends to the same `UnitAddTorus` action.  Compose the
given model `q` with the inverse of that canonical homeomorphism.  Applying
the homeomorphism to the desired quotient equality reduces it to the supplied
torus conjugacy equation; the representative matrix identity then closes the
calculation.  This is a coordinate change only and introduces no dynamical
assumption. -/
theorem unit_add_torus_quotient_adapter
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M ≃ₜ M) (q : C(M, UnitAddTorus (Fin n)))
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hq : ∀ x, q (f x) = integralToralMap A (q x)) :
    let E := quotientTorusHomeomorph n
    let h : C(M, (Fin n → ℝ) ⧸ (coordinateLattice n).toAddSubgroup) :=
      ⟨fun x ↦ E.symm (q x), E.symm.continuous.comp q.continuous⟩
    let R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
      (FranksMatrix.realAction A).toContinuousLinearEquiv
    (∀ x v, (QuotientAddGroup.mk v : (Fin n → ℝ) ⧸
      (coordinateLattice n).toAddSubgroup) = h x →
      h (f x) = QuotientAddGroup.mk (R v)) := by
  dsimp
  intro x v hv
  let E := quotientTorusHomeomorph n
  have hqx : q x = E (QuotientAddGroup.mk v) := by
    have he := congrArg E hv
    simpa [E] using he.symm
  apply E.injective
  change E (E.symm (q (f x))) = E (QuotientAddGroup.mk
    ((FranksMatrix.realAction A).toContinuousLinearEquiv v))
  rw [E.apply_symm_apply, hq x, hqx]
  have hRA : FranksMatrix.realAction A v =
      (realMatrix A).mulVecLin v := by
    ext i
    rfl
  change integralToralMap A (E (QuotientAddGroup.mk v)) =
    E (QuotientAddGroup.mk (FranksMatrix.realAction A v))
  rw [hRA]
  exact (quotientTorusHomeomorph_matrix A v).symm

/-! **Source and proof.**  Again use the representative formula
`quotientTorusHomeomorph_mk` from `RealQuotientTorus`.  It unfolds to the
coordinate projection, so the parent's projection identity is exactly the
quotient-lift identity required by the decay argument. -/
theorem unit_add_torus_quotient_lift_projection
    {n : ℕ} {P : Type*} [TopologicalSpace P]
    (H : C(P, Fin n → ℝ)) (k : C(P, UnitAddTorus (Fin n)))
    (hproj : ∀ x, coordinateProjection n (H x) = k x) :
    ∀ x, quotientTorusHomeomorph n
      (QuotientAddGroup.mk (H x)) = k x := by
  intro x
  change (fun i ↦ (H x i : UnitAddCircle)) = k x
  exact hproj x

/-! This is the direct consumer-facing form of `forward_affine_leaf_image`.
The coordinate lattice is the standard integer span, whose discreteness,
`IsZLattice` instance, and matrix image equality are the native providers in
`IntegerCoordinateLattice` and `IntegerLatticePreservation`.  The two preceding
adapters supply the quotient model and lift identity, after which the proof is
literally the quotient leaf-decay argument. -/
theorem unit_forward_affine_leaf_image
    {n : ℕ} {M Y L : Type*} [MetricSpace M] [CompactSpace M]
    [TopologicalSpace Y] [TopologicalSpace L] [PathConnectedSpace L]
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (f : M ≃ₜ M) (q : C(M, UnitAddTorus (Fin n)))
    (hq : ∀ x, q (f x) = integralToralMap A (q x))
    (p : Y → M) (hp : IsCoveringMap p)
    (H : C(Y, Fin n → ℝ))
    (hproj : ∀ x, coordinateProjection n (H x) = q (p x))
    (y : Y) (j : L → M) (hj : Continuous j) (a : L) (ha : j a = p y)
    (hcarrier : ∀ b, ForwardAsymptotic f (p y) (j b)) :
    H '' liftedIntrinsicLeafRange p j a y ⊆
      (fun v : Fin n → ℝ ↦ H y + v) ''
        (fullDecaySubmodule ((FranksMatrix.realAction A).toContinuousLinearEquiv) :
          Set (Fin n → ℝ)) := by
  let E := quotientTorusHomeomorph n
  let h : C(M, (Fin n → ℝ) ⧸ (coordinateLattice n).toAddSubgroup) :=
    ⟨fun x ↦ E.symm (q x), E.symm.continuous.comp q.continuous⟩
  let R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (FranksMatrix.realAction A).toContinuousLinearEquiv
  have hmodel := unit_add_torus_quotient_adapter f q A hq
  dsimp only at hmodel
  have hH : ∀ z, (QuotientAddGroup.mk (H z) :
      (Fin n → ℝ) ⧸ (coordinateLattice n).toAddSubgroup) = h (p z) := by
    intro z
    apply E.injective
    rw [quotientTorusHomeomorph_mk]
    have he : E (h (p z)) = q (p z) := by simp [h, E]
    rw [he]
    change coordinateProjection n (H z) = q (p z)
    exact hproj z
  exact forward_affine_leaf_image (coordinateLattice n) R
    (IntegerLatticePreservation.integer_gl_realCLE_image_basis_span A)
    f h hmodel p hp H hH y j hj a ha hcarrier

/-- A simply connected intrinsic leaf has an injective pointed lift whose range
is exactly the marked intrinsic path-lift endpoint set. Source: Hatcher,
Propositions 1.30, 1.33 and 1.34, pp.60--62. First use the unique pointed
covering lift of the inclusion. Paths in the intrinsic leaf give one range
inclusion. Conversely, uniqueness of covering path lifts identifies every
path in the definition of the marked endpoint set with the lifted intrinsic
path. This uses the given intrinsic topology, not the ambient subspace topology,
and requires no injectivity or surjectivity of a semiconjugacy. -/
theorem pointed_leaf_lift_with_range
    {L P M : Type*} [TopologicalSpace L] [TopologicalSpace P] [TopologicalSpace M]
    [SimplyConnectedSpace L] [LocallyPathConnectedSpace L]
    (p : P → M) (hp : IsCoveringMap p) (j : C(L, M))
    (hj : Function.Injective j) (a : L) (y : P) (hy : p y = j a) :
    ∃ l : C(L, P), Function.Injective l ∧ l a = y ∧
      (∀ b, p (l b) = j b) ∧
      Set.range l = liftedIntrinsicLeafRange p j a y := by
  obtain ⟨l, hinj, hproj, hpoint, _⟩ :=
    Ghys.injective_pointed_leaf_lift hp j hj a y hy
  have hbase : l a = y := hpoint a hy.symm
  refine ⟨l, hinj, hbase, hproj, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨b, rfl⟩
    let γ := PathConnectedSpace.somePath a b
    refine ⟨b, γ, (γ.map l.continuous).cast hbase.symm rfl, ?_⟩
    intro t
    exact hproj (γ t)
  · rintro z ⟨b, γ, η, hη⟩
    have heq : (fun t ↦ l (γ t)) = η := hp.eq_of_comp_eq
      (l.continuous.comp γ.continuous) η.continuous
      (by funext t; exact (hproj (γ t)).trans (hη t).symm)
      0 (by simpa only [Path.source] using hbase)
    exact ⟨b, by simpa only [Path.target] using congrFun heq 1⟩

/-- The exact-range lift applied to a real Euclidean intrinsic leaf. Its
Euclidean homeomorphism transports contractibility and local path connectedness;
the lift and range identity then follow from `pointed_leaf_lift_with_range`.
Only the intrinsic leaf coordinates are used, not semiconjugacy coordinates. -/
theorem euclidean_leaf_lift_with_range
    {L P M : Type*} [TopologicalSpace L] [TopologicalSpace P] [TopologicalSpace M]
    {k : ℕ} (e : (Fin k → ℝ) ≃ₜ L)
    (p : P → M) (hp : IsCoveringMap p) (j : C(L, M))
    (hj : Function.Injective j) (a : L) (y : P) (hy : p y = j a) :
    ∃ l : C(L, P), Function.Injective l ∧ l a = y ∧
      (∀ b, p (l b) = j b) ∧
      Set.range l = liftedIntrinsicLeafRange p j a y := by
  let : ContractibleSpace L := e.symm.contractibleSpace
  let : LocallyPathConnectedSpace L := e.locallyPathConnectedSpace
  exact pointed_leaf_lift_with_range p hp j hj a y hy

/-- The pointed lift identifies a simply connected intrinsic leaf with the
actual path component of its covering pullback. Source: Hatcher 1.33--1.34,
pp.61--62, and Bredon II.14, pp.111--112. The inverse is the first projection;
the forward map is the graph of the pointed lift. Intrinsic paths show this
graph lies in the marked component. Uniqueness of covering path lifts shows
every point in that component is on the graph. Both maps are continuous in
the original product and component topologies. -/
theorem pointed_leaf_pullback_homeomorph
    {L P M : Type*} [TopologicalSpace L] [TopologicalSpace P] [TopologicalSpace M]
    [SimplyConnectedSpace L] [LocallyPathConnectedSpace L]
    (p : P → M) (hp : IsCoveringMap p) (j : C(L, M))
    (hj : Function.Injective j) (a : L) (y : P) (hy : j a = p y) :
    ∃ e : L ≃ₜ IntrinsicCoveringPullbackLeaf j p a y hy,
      ∀ b, intrinsicCoveringLeafProjection j p a y hy (e b) = b := by
  obtain ⟨l, _, hbase, hproj, _⟩ :=
    pointed_leaf_lift_with_range p hp j hj a y hy.symm
  let g : L → IntrinsicCoveringPullback j p := fun b ↦ ⟨(b, l b), (hproj b).symm⟩
  have hg : Continuous g := (continuous_id.prodMk l.continuous).subtype_mk _
  have hga : g a = intrinsicCoveringPullbackPoint j p a y hy := by
    apply Subtype.ext
    exact Prod.ext rfl hbase
  have hmem (b : L) : g b ∈ pathComponent (intrinsicCoveringPullbackPoint j p a y hy) := by
    exact ⟨((PathConnectedSpace.somePath a b).map hg).cast hga.symm rfl⟩
  let G : L → IntrinsicCoveringPullbackLeaf j p a y hy := fun b ↦ ⟨g b, hmem b⟩
  have hgraph (z : IntrinsicCoveringPullbackLeaf j p a y hy) : l z.val.val.1 = z.val.val.2 := by
    obtain ⟨γ⟩ := z.property
    have heq : (fun t ↦ l (γ t).val.1) = fun t ↦ (γ t).val.2 := hp.eq_of_comp_eq
      (l.continuous.comp (continuous_fst.comp (continuous_subtype_val.comp γ.continuous)))
      (continuous_snd.comp (continuous_subtype_val.comp γ.continuous))
      (by funext t; exact (hproj (γ t).val.1).trans (γ t).property)
      0 (by rw [γ.source]; exact hbase)
    simpa only [Path.target] using congrFun heq 1
  refine ⟨{ toFun := G
            invFun := intrinsicCoveringLeafProjection j p a y hy
            left_inv := fun _ ↦ rfl
            right_inv := ?_
            continuous_toFun := hg.subtype_mk _
            continuous_invFun := (intrinsicCoveringLeafProjection j p a y hy).continuous },
    fun _ ↦ rfl⟩
  intro z
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl (hgraph z)

/-- Two cycles with uniformly close images in an expansive factor coincide
when the factor map is injective on each same-period fixed set. Source:
Franks (1969), the periodic uniqueness comparison preceding Lemma 1.6,
combined with Shub's cyclic shadowing argument. Iteration of covariance makes
each value periodic. Reduce every integer target iterate modulo that period,
so the finite-cycle bound gives the full expansive-orbit bound. Expansivity
identifies their images, and same-period injectivity identifies the originals.
No global injectivity of the factor is assumed. -/
theorem cyclic_orbits_eq_of_close_images
    {X Y I : Type*} [MetricSpace Y]
    (f : X → X) (g : Y ≃ₜ Y) (k : X → Y)
    (hk : Function.Semiconj k f g) (ε : ℝ)
    (hexp : ∀ u v : Y,
      (∀ t : ℤ, dist ((g.toEquiv ^ t) u) ((g.toEquiv ^ t) v) ≤ ε) → u = v)
    (hperiod : ∀ n : ℕ, 0 < n → ∀ x y,
      f^[n] x = x → f^[n] y = y → k x = k y → x = y)
    (r : I → I) (n : ℕ) (hn : 0 < n) (hr : r^[n] = id)
    (j₁ j₂ : I → X) (hj₁ : Function.Semiconj j₁ r f)
    (hj₂ : Function.Semiconj j₂ r f)
    (hclose : ∀ i, dist (k (j₁ i)) (k (j₂ i)) ≤ ε) : j₁ = j₂ := by
  have hp (j : I → X) (hj : Function.Semiconj j r f) (i : I) :
      f^[n] (j i) = j i := by
    rw [← hj.iterate_right n i, hr]
    rfl
  have hki (j : I → X) (hj : Function.Semiconj j r f) (m : ℕ) (i : I) :
      (g : Y → Y)^[m] (k (j i)) = k (j (r^[m] i)) := by
    rw [← hk.iterate_right m (j i), ← hj.iterate_right m i]
  have hkp (j : I → X) (hj : Function.Semiconj j r f) (i : I) :
      (g : Y → Y)^[n] (k (j i)) = k (j i) := by
    rw [hki j hj n i, hr]
    rfl
  funext i
  apply hperiod n hn _ _ (hp j₁ hj₁ i) (hp j₂ hj₂ i)
  apply hexp
  intro t
  rw [Dynamics.ManningOriginalBasicSetSignedTraceG7.periodic_zpow_remainder
      g.toEquiv hn (hkp j₁ hj₁ i),
    Dynamics.ManningOriginalBasicSetSignedTraceG7.periodic_zpow_remainder
      g.toEquiv hn (hkp j₂ hj₂ i)]
  exact (hki j₁ hj₁ _ i).symm ▸ (hki j₂ hj₂ _ i).symm ▸ hclose (r^[(t % n).toNat] i)

/-- A cyclic pseudo-orbit whose factor images stay near a genuine cycle is
shadowed by that very cycle, provided the shadowing error also has small factor
image. This is the rigidity step in the homoclinic cyclic splice: triangle
inequality makes the two shadowing cycles close in the expansive factor;
`cyclic_orbits_eq_of_close_images` then identifies them using only same-period
injectivity. The pseudo-orbit may repeat values. -/
theorem cyclic_pseudo_orbit_rigidity
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → X) (g : Y ≃ₜ Y) (k : X → Y)
    (hk : Function.Semiconj k f g) (ε η δ : ℝ)
    (hexp : ∀ u v : Y,
      (∀ t : ℤ, dist ((g.toEquiv ^ t) u) ((g.toEquiv ^ t) v) ≤ ε) → u = v)
    (hperiod : ∀ n : ℕ, 0 < n → ∀ x y,
      f^[n] x = x → f^[n] y = y → k x = k y → x = y)
    (hmod : ∀ x y, dist x y < η → dist (k x) (k y) ≤ ε / 2)
    (hshadow : ∀ n : ℕ, 0 < n → ∀ q : Fin n → X,
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
      ∃ l : Fin n → X, Function.Semiconj l (finRotate n) f ∧
        ∀ i, dist (l i) (q i) < η)
    (n : ℕ) (hn : 0 < n) (j q : Fin n → X)
    (hj : Function.Semiconj j (finRotate n) f)
    (hq : ∀ i, dist (f (q i)) (q (finRotate n i)) < δ)
    (himage : ∀ i, dist (k (q i)) (k (j i)) ≤ ε / 2) :
    ∀ i, dist (j i) (q i) < η := by
  let : NeZero n := ⟨by omega⟩
  have hrot (m : ℕ) (i : Fin n) : (finRotate n)^[m] i = i + Fin.ofNat n m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, finRotate_apply]
      open scoped Fin.NatCast in
      change (i + (m : Fin n)) + 1 = i + ((m + 1 : ℕ) : Fin n)
      simp [Nat.cast_add, Nat.cast_one, add_assoc]
  have hr : (finRotate n)^[n] = id := by
    funext i
    simpa using hrot n i
  obtain ⟨l, hl, hclose⟩ := hshadow n hn q hq
  have heq : l = j := cyclic_orbits_eq_of_close_images f g k hk ε hexp hperiod
    (finRotate n) n hn hr l j hl hj (fun i ↦ by
      calc
        dist (k (l i)) (k (j i)) ≤ dist (k (l i)) (k (q i)) +
            dist (k (q i)) (k (j i)) := dist_triangle _ _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add (hmod _ _ (hclose i)) (himage i)
        _ = ε := by ring)
  simpa only [heq] using hclose

/-- Periodic density approximates any prescribed finite orbit segment, with
a period longer than that segment. Source: the periodic approximation in
Franks' proof preceding Lemma 1.6. The finite orbit-coordinate map is continuous,
so a small ball about its value has an open nonempty preimage. Density supplies
a periodic point in that preimage. Repeating its period sufficiently many times
gives the requested length without changing the point or its orbit. -/
theorem periodic_approximation_finite_segment
    {X : Type*} [MetricSpace X] (f : X → X) (hf : Continuous f)
    (hdense : Dense (Function.periodicPts f)) (x : X) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : X, ∃ n : ℕ, N < n ∧ f^[n] p = p ∧
      ∀ m ≤ N, dist (f^[m] p) (f^[m] x) < ε := by
  let Φ : X → Fin (N + 1) → X := fun y i ↦ f^[i.val] y
  have hΦ : Continuous Φ := continuous_pi fun i ↦ hf.iterate i.val
  obtain ⟨p, hper, hp⟩ := hdense.exists_mem_open
    (Metric.isOpen_ball.preimage hΦ)
    (show (Φ ⁻¹' Metric.ball (Φ x) ε).Nonempty from ⟨x, by simpa using hε⟩)
  obtain ⟨n, hn, hpn⟩ := Function.mem_periodicPts.mp hper
  refine ⟨p, n * (N + 1), by nlinarith, ?_, ?_⟩
  · exact hpn.mul_const (N + 1)
  · intro m hm
    exact (dist_pi_lt_iff hε).mp hp ⟨m, by omega⟩

/-- Splice a finite true orbit segment into a longer periodic cycle. Only
the two end jumps need estimates; all remaining jumps are exact orbit steps.
Source: the cyclic pseudo-orbit construction in Shub's shadowing argument,
used in Franks' homoclinic intersection comparison. Factor-image estimates
on the inserted segment and equality outside it bound the whole cycle. -/
theorem exists_cyclic_orbit_splice
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → X) (k : X → Y) (δ ρ : ℝ) (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (n L : ℕ) (hL : 0 < L) (hLn : L < n)
    (j : Fin n → X) (hj : Function.Semiconj j (finRotate n) f) (b : X)
    (hfirst : dist (j ⟨0, by omega⟩) b < δ)
    (hlast : dist (f^[L] b) (j ⟨L, hLn⟩) < δ)
    (himage : ∀ i : Fin n, i.val < L → dist (k (f^[i.val] b)) (k (j i)) ≤ ρ) :
    ∃ q : Fin n → X,
      (∀ i, i.val < L → q i = f^[i.val] b) ∧
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) ∧
      ∀ i, dist (k (q i)) (k (j i)) ≤ ρ := by
  let : NeZero n := ⟨by omega⟩
  let q : Fin n → X := fun i ↦ if i.val < L then f^[i.val] b else j i
  have hrot (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
    rw [finRotate_apply]
    simp [Fin.val_add]
  refine ⟨q, fun i hi ↦ ite_eq_left hi, ?_, ?_⟩
  · intro i
    by_cases hi : i.val + 1 < n
    · have hr : (finRotate n i).val = i.val + 1 := by rw [hrot, Nat.mod_eq_of_lt hi]
      by_cases hiL : i.val < L
      · by_cases hiL' : i.val + 1 < L
        · simp only [q, ite_eq_left hiL, ite_eq_left (show (finRotate n i).val < L by omega)]
          rw [hr, Function.iterate_succ_apply']
          simpa using hδ
        · have he : i.val + 1 = L := by omega
          have hrL : finRotate n i = ⟨L, hLn⟩ := Fin.ext (hr.trans he)
          simp only [q, ite_eq_left hiL, ite_eq_right (show ¬(finRotate n i).val < L by omega)]
          rw [← Function.iterate_succ_apply' f i.val b, Nat.succ_eq_add_one, he, hrL]
          exact hlast
      · simp only [q, ite_eq_right hiL, ite_eq_right (show ¬(finRotate n i).val < L by omega)]
        rw [hj i]
        simpa using hδ
    · have he : i.val + 1 = n := by omega
      have hr0 : finRotate n i = ⟨0, by omega⟩ := by
        apply Fin.ext
        rw [hrot, he, Nat.mod_self]
      have hiL : ¬i.val < L := by omega
      simp only [q, ite_eq_right hiL, ite_eq_left (show (finRotate n i).val < L by rw [hr0]; exact hL)]
      rw [← hj i, hr0]
      exact hfirst
  · intro i
    by_cases hi : i.val < L
    · simpa only [q, ite_eq_left hi] using himage i hi
    · simpa only [q, ite_eq_right hi, dist_self] using hρ

/-- A finite pair of orbit segments with equal factor image and close ends
must remain close throughout, provided periodic points are dense and small
cyclic pseudo-orbits can be shadowed. Source: Franks' homoclinic uniqueness
argument, with the periodic approximation and two splice jumps written out.
Approximate the first segment by a periodic orbit with longer period, insert
the second segment, and apply cyclic factor rigidity. The estimate follows
from the approximation error and the shadowing error. -/
theorem finite_equal_image_segment_bound
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → X) (hf : Continuous f) (g : Y ≃ₜ Y) (k : X → Y)
    (hk : Function.Semiconj k f g) (ε η δ : ℝ)
    (hε : 0 < ε) (hη : 0 < η) (hδ : 0 < δ)
    (hexp : ∀ u v : Y,
      (∀ t : ℤ, dist ((g.toEquiv ^ t) u) ((g.toEquiv ^ t) v) ≤ ε) → u = v)
    (hperiod : ∀ n : ℕ, 0 < n → ∀ x y,
      f^[n] x = x → f^[n] y = y → k x = k y → x = y)
    (hdense : Dense (Function.periodicPts f))
    (hmod : ∀ x y, dist x y < η → dist (k x) (k y) ≤ ε / 2)
    (hshadow : ∀ n : ℕ, 0 < n → ∀ q : Fin n → X,
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
      ∃ l : Fin n → X, Function.Semiconj l (finRotate n) f ∧
        ∀ i, dist (l i) (q i) < η)
    (a b : X) (L : ℕ) (hL : 0 < L) (hab : k a = k b)
    (hfirst : dist a b < δ / 3)
    (hlast : dist (f^[L] b) (f^[L] a) < δ / 3) :
    ∀ m < L, dist (f^[m] a) (f^[m] b) < 2 * η := by
  obtain ⟨p, n, hLn, hpn, hp⟩ := periodic_approximation_finite_segment f hf hdense a L
    (min η (δ / 3)) (lt_min hη (by positivity))
  have hn : 0 < n := by omega
  let : NeZero n := ⟨by omega⟩
  let j : Fin n → X := fun i ↦ f^[i.val] p
  have hj : Function.Semiconj j (finRotate n) f := by
    intro i
    have hr : (finRotate n i).val = (i.val + 1) % n := by
      rw [finRotate_apply]
      simp [Fin.val_add]
    change f^[(finRotate n i).val] p = f (f^[i.val] p)
    rw [hr]
    by_cases hi : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hi, Function.iterate_succ_apply']
    · have he : i.val + 1 = n := by omega
      rw [he, Nat.mod_self]
      symm
      simpa only [← Function.iterate_succ_apply' f i.val p,
        Nat.succ_eq_add_one, he, Function.iterate_zero_apply] using hpn
  have hpη (m : ℕ) (hm : m ≤ L) : dist (f^[m] p) (f^[m] a) < η :=
    (hp m hm).trans_le (min_le_left _ _)
  have hpδ (m : ℕ) (hm : m ≤ L) : dist (f^[m] p) (f^[m] a) < δ / 3 :=
    (hp m hm).trans_le (min_le_right _ _)
  have hstart : dist (j ⟨0, hn⟩) b < δ := by
    have ht := dist_triangle p a b
    have hs := hpδ 0 (by omega)
    change dist p a < δ / 3 at hs
    change dist p b < δ
    linarith
  have hend : dist (f^[L] b) (j ⟨L, hLn⟩) < δ := by
    have ht := dist_triangle (f^[L] b) (f^[L] a) (f^[L] p)
    have hs := hpδ L le_rfl
    rw [dist_comm (f^[L] a) (f^[L] p)] at ht
    change dist (f^[L] b) (f^[L] p) < δ
    linarith
  have himage (i : Fin n) (hi : i.val < L) :
      dist (k (f^[i.val] b)) (k (j i)) ≤ ε / 2 := by
    have he : k (f^[i.val] b) = k (f^[i.val] a) := by
      rw [hk.iterate_right i.val b, hk.iterate_right i.val a, hab]
    rw [he]
    apply hmod
    rw [dist_comm]
    exact hpη i.val (by omega)
  obtain ⟨q, hqseg, hqjump, hqimage⟩ := exists_cyclic_orbit_splice f k δ (ε / 2)
    hδ (by positivity) n L hL hLn j hj b hstart hend himage
  have hclose := cyclic_pseudo_orbit_rigidity f g k hk ε η δ hexp hperiod hmod hshadow
    n hn j q hj hqjump hqimage
  intro m hm
  let i : Fin n := ⟨m, by omega⟩
  have hc := hclose i
  rw [hqseg i hm] at hc
  change dist (f^[m] p) (f^[m] b) < η at hc
  have ht := dist_triangle (f^[m] a) (f^[m] p) (f^[m] b)
  have ha := hpη m (by omega)
  rw [dist_comm (f^[m] a) (f^[m] p)] at ht
  linarith

/-- A homoclinic pair with the same factor image is equal, assuming dense
periodic points, cyclic shadowing and injectivity on each same-period fixed
set. This is the noncircular periodic-splice part of Franks' lifted intersection
argument. Choose a small shadowing scale, move both endpoints far backwards,
and compare the finite segments ending equally far forwards. Their two end
distances are small by backward and forward asymptoticity. The finite splice
bound makes the original middle points arbitrarily close. All dynamical
premises are explicit; this theorem does not assert periodic density. -/
theorem eq_of_homoclinic_of_same_image
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    (f : X ≃ₜ X) (g : Y ≃ₜ Y) (k : C(X, Y))
    (hk : Function.Semiconj k f g) (ε : ℝ) (hε : 0 < ε)
    (hexp : ∀ u v : Y,
      (∀ t : ℤ, dist ((g.toEquiv ^ t) u) ((g.toEquiv ^ t) v) ≤ ε) → u = v)
    (hperiod : ∀ n : ℕ, 0 < n → ∀ x y,
      (f : X → X)^[n] x = x → (f : X → X)^[n] y = y → k x = k y → x = y)
    (hdense : Dense (Function.periodicPts (f : X → X)))
    (hcyclic : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, 0 < n → ∀ q : Fin n → X,
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
      ∃ l : Fin n → X, Function.Semiconj l (finRotate n) f ∧
        ∀ i, dist (l i) (q i) < η)
    (x y : X) (himage : k x = k y)
    (hs : ForwardAsymptotic f x y) (hu : ForwardAsymptotic f.symm x y) : x = y := by
  by_contra hne
  have hd : 0 < dist x y := dist_pos.mpr hne
  obtain ⟨μ, hμ, hμmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous k.continuous) (ε / 2) (by positivity)
  let η := min (dist x y / 4) μ
  have hη : 0 < η := lt_min (by positivity) hμ
  have hηd : η ≤ dist x y / 4 := min_le_left _ _
  have hmod : ∀ a b, dist a b < η → dist (k a) (k b) ≤ ε / 2 := by
    intro a b hab
    exact (hμmod (hab.trans_le (min_le_right _ _))).le
  obtain ⟨δ, hδ, hshadow⟩ := hcyclic η hη
  have hs' : ∀ᶠ N : ℕ in atTop,
      dist ((f : X → X)^[N] y) ((f : X → X)^[N] x) < δ / 3 :=
    (tendsto_order.mp hs).2 _ (by positivity)
  have hu' : ∀ᶠ N : ℕ in atTop,
      dist ((f.symm : X → X)^[N] y) ((f.symm : X → X)^[N] x) < δ / 3 :=
    (tendsto_order.mp hu).2 _ (by positivity)
  obtain ⟨N, ⟨hsN, huN⟩, hN⟩ := ((hs'.and hu').and (eventually_gt_atTop 0)).exists
  have hcancel (m : ℕ) (z : X) :
      (f : X → X)^[m] ((f.symm : X → X)^[m] z) = z := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply', f.apply_symm_apply, ih]
  have htwice (z : X) : (f : X → X)^[2 * N] ((f.symm : X → X)^[N] z) =
      (f : X → X)^[N] z := by
    rw [two_mul, Function.iterate_add_apply, hcancel]
  have hki : Function.Semiconj k f.symm g.symm := by
    intro z
    apply g.injective
    rw [← hk (f.symm z), f.apply_symm_apply, g.apply_symm_apply]
  have himage' : k ((f.symm : X → X)^[N] x) = k ((f.symm : X → X)^[N] y) := by
    rw [hki.iterate_right N x, hki.iterate_right N y, himage]
  have hfirst : dist ((f.symm : X → X)^[N] x) ((f.symm : X → X)^[N] y) < δ / 3 := by
    rwa [dist_comm] at huN
  have hlast : dist
      ((f : X → X)^[2 * N] ((f.symm : X → X)^[N] y))
      ((f : X → X)^[2 * N] ((f.symm : X → X)^[N] x)) < δ / 3 := by
    simpa only [htwice] using hsN
  have hb := finite_equal_image_segment_bound f f.continuous g k hk ε η δ hε hη hδ
    hexp hperiod hdense hmod hshadow
    ((f.symm : X → X)^[N] x) ((f.symm : X → X)^[N] y)
    (2 * N) (by omega) himage' hfirst hlast N (by omega)
  rw [hcancel, hcancel] at hb
  linarith

private theorem forwardAsymptotic_common_base
    {X : Type*} [MetricSpace X] (f : X → X) {s a b : X}
    (ha : ForwardAsymptotic f s a) (hb : ForwardAsymptotic f s b) :
    ForwardAsymptotic f a b := by
  apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    (show Tendsto (fun n : ℕ ↦ dist (f^[n] b) (f^[n] s) +
      dist (f^[n] a) (f^[n] s)) atTop (𝓝 0) from by simpa using hb.add ha)
  calc
    dist (f^[n] b) (f^[n] a) ≤ dist (f^[n] b) (f^[n] s) +
        dist (f^[n] s) (f^[n] a) := dist_triangle _ _ _
    _ = dist (f^[n] b) (f^[n] s) + dist (f^[n] a) (f^[n] s) := by rw [dist_comm (f^[n] s)]

/-- Native lifted stable and unstable leaves have at most one intersection
once homoclinic equal-image rigidity is established downstairs. Source:
Franks (1969), intersection uniqueness preceding Lemma 1.6. Affine INTO
statements put the difference of two intersection images in both complementary
linear subspaces, so their corrected images agree. Their projections form a
homoclinic pair with equal factor image and therefore agree. The exact native
leaf projection identifies their intrinsic parameters, hence their lifts.
The native lifts need no H-coordinate bijectivity or global product. -/
theorem lifted_intersection_subsingleton
    {X Y P V : Type*} [MetricSpace X]
    [AddCommGroup V] [Module ℝ V]
    (f : X ≃ₜ X) (k : X → Y) (p : P → X) (H : P → V) (π : V → Y)
    (hproj : ∀ z, π (H z) = k (p z))
    (hhom : ∀ a b, k a = k b → ForwardAsymptotic f a b →
      ForwardAsymptotic f.symm a b → a = b)
    (S U : Submodule ℝ V) (hSU : Disjoint S U) (s u : X)
    (ls : StableAsymptoticLeaf f s → P)
    (lu : StableAsymptoticLeaf f.symm u → P)
    (hls : ∀ a, p (ls a) = a.val) (hlu : ∀ a, p (lu a) = a.val)
    (vs vu : V) (hs : ∀ a, H (ls a) - vs ∈ S)
    (hu : ∀ a, H (lu a) - vu ∈ U) :
    (Set.range ls ∩ Set.range lu).Subsingleton := by
  rintro x ⟨⟨a, rfl⟩, ⟨c, hc⟩⟩ y ⟨⟨b, rfl⟩, ⟨d, hd⟩⟩
  have hS : H (ls a) - H (ls b) ∈ S := by
    convert S.sub_mem (hs a) (hs b) using 1; abel_nf
  have hU : H (ls a) - H (ls b) ∈ U := by
    rw [← hc, ← hd]
    convert U.sub_mem (hu c) (hu d) using 1; abel_nf
  have hH : H (ls a) = H (ls b) :=
    sub_eq_zero.mp (Submodule.disjoint_def.mp hSU _ hS hU)
  have hk : k (p (ls a)) = k (p (ls b)) := by
    rw [← hproj, ← hproj, hH]
  have hforward : ForwardAsymptotic f (p (ls a)) (p (ls b)) := by
    rw [hls, hls]
    exact forwardAsymptotic_common_base f a.property b.property
  have hbackward : ForwardAsymptotic f.symm (p (ls a)) (p (ls b)) := by
    rw [← hc, ← hd, hlu, hlu]
    exact forwardAsymptotic_common_base f.symm c.property d.property
  have hp := hhom _ _ hk hforward hbackward
  rw [hls, hls] at hp
  exact congrArg ls (Subtype.ext hp)

/-- Relation obtained by lifting intrinsic paths in one fixed selected partition.
The selected family and its intrinsic topologies are retained across basepoints. -/
def intrinsicLiftedPathRel
    {M P ι : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    (p : P → M) (j : ∀ i, L i → M) (x y : P) : Prop :=
  ∃ i a, j i a = p x ∧ y ∈ liftedIntrinsicLeafRange p (j i) a x

/-- Lifted intrinsic paths in a partition form an equivalence relation.
Source: the lifted-foliation construction of Franks (1970), Proposition 1.1,
pp.65--66. Constant paths prove reflexivity, reversed paths symmetry. At a
common endpoint the partition law identifies the leaf labels and injectivity
identifies the intrinsic parameters; concatenate the two intrinsic paths and
their lifts. This does not identify intrinsic and ambient subspace topology. -/
theorem intrinsicLiftedPathRel_equivalence
    {M P ι : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    (p : P → M) (j : ∀ i, L i → M)
    (hinj : ∀ i, Function.Injective (j i))
    (hcover : ∀ z, ∃ i a, j i a = z)
    (hdisjoint : ∀ i i' a b, j i a = j i' b → i = i') :
    Equivalence (intrinsicLiftedPathRel p j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨i, a, ha⟩ := hcover (p x)
    exact ⟨i, a, ha, a, Path.refl a, Path.refl x, fun _ ↦ ha.symm⟩
  · rintro x y ⟨i, a, ha, b, γ, η, hη⟩
    have hb : j i b = p y := by simpa only [Path.target] using (hη 1).symm
    exact ⟨i, b, hb, a, γ.symm, η.symm, fun t ↦ hη (unitInterval.symm t)⟩
  · rintro x y z ⟨i, a, ha, b, γ, η, hη⟩ ⟨i', c, hc, d, γ', η', hη'⟩
    have hb : j i b = p y := by simpa only [Path.target] using (hη 1).symm
    have hii : i = i' := hdisjoint i i' b c (hb.trans hc.symm)
    subst i'
    have hbc : b = c := hinj i (hb.trans hc.symm)
    subst c
    refine ⟨i, a, ha, d, γ.trans γ', η.trans η', ?_⟩
    intro t
    simp only [Path.trans_apply]
    split_ifs
    · exact hη _
    · exact hη' _

/-- The native lifted path partition, using the proved path equivalence. -/
def intrinsicLiftedPathSetoid
    {M P ι : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    (p : P → M) (j : ∀ i, L i → M)
    (hinj : ∀ i, Function.Injective (j i))
    (hcover : ∀ z, ∃ i a, j i a = z)
    (hdisjoint : ∀ i i' a b, j i a = j i' b → i = i') : Setoid P where
  r := intrinsicLiftedPathRel p j
  iseqv := intrinsicLiftedPathRel_equivalence p j hinj hcover hdisjoint

/-- At any chosen native leaf and marked intrinsic point, the common lifted
partition class is exactly its marked path-lift range. The partition and
injectivity laws identify any alternate witness with that same mark. -/
theorem intrinsicLiftedPathRel_iff_range
    {M P ι : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    (p : P → M) (j : ∀ i, L i → M)
    (hinj : ∀ i, Function.Injective (j i))
    (hdisjoint : ∀ i i' a b, j i a = j i' b → i = i')
    (i : ι) (a : L i) (x y : P) (ha : j i a = p x) :
    intrinsicLiftedPathRel p j x y ↔ y ∈ liftedIntrinsicLeafRange p (j i) a x := by
  constructor
  · rintro ⟨i', a', ha', hy⟩
    have hii : i' = i := hdisjoint i' i a' a (ha'.trans ha.symm)
    subst i'
    have haa : a' = a := hinj i (ha'.trans ha.symm)
    simpa only [haa] using hy
  · exact fun hy ↦ ⟨i, a, ha, hy⟩

/-- An actual continuous lifted plaque belongs to one native lifted leaf.
Source: Franks (1970), the lifted local plaques in Proposition 1.1. Join the
two intrinsic plaque coordinates by a path; its images under the native chart
and the lifted plaque are the two paths in the defining lifted relation.
The factorization is pointwise on the whole plaque, not merely at its center. -/
theorem intrinsicLiftedPathRel_of_plaque
    {M P ι T : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    [TopologicalSpace T] [PathConnectedSpace T]
    (p : P → M) (j : ∀ i, L i → M) (i : ι)
    (chart : C(T, L i)) (lift : C(T, P))
    (hproj : ∀ t, p (lift t) = j i (chart t)) (a b : T) :
    intrinsicLiftedPathRel p j (lift a) (lift b) := by
  let γ := PathConnectedSpace.somePath a b
  exact ⟨i, chart a, (hproj a).symm, chart b,
    γ.map chart.continuous, γ.map lift.continuous, fun t ↦ hproj (γ t)⟩

/-- Open one-plaque saturation implies open saturation by finite plaque chains.
Source: the foliation topology construction in Franks (1970), Proposition 1.1.
Let S be the full equivalence saturation of an open set. Its interior contains
the original open set and is preserved by each plaque step: the one-step image
of the interior is open and still contained in S. Symmetry and finite-chain
induction therefore put all of S in its interior. No closedness of the global
leaf relation or global product is assumed. -/
theorem isOpen_eqvGen_saturation
    {P : Type*} [TopologicalSpace P] (R : P → P → Prop)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hopen : ∀ O : Set P, IsOpen O → IsOpen {y | ∃ x ∈ O, R x y})
    (O : Set P) (hO : IsOpen O) :
    IsOpen {y | ∃ x ∈ O, Relation.EqvGen R x y} := by
  let S : Set P := {y | ∃ x ∈ O, Relation.EqvGen R x y}
  have hstep {x y : P} (hx : x ∈ interior S) (hxy : R x y) : y ∈ interior S := by
    have hsub : {b | ∃ a ∈ interior S, R a b} ⊆ S := by
      rintro b ⟨a, ha, hab⟩
      obtain ⟨z, hz, hza⟩ := interior_subset ha
      exact ⟨z, hz, hza.trans _ _ _ (Relation.EqvGen.rel _ _ hab)⟩
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((hopen _ isOpen_interior).mem_nhds ⟨x, hx, hxy⟩) hsub)
  have hpres {x y : P} (hxy : Relation.EqvGen R x y) :
      x ∈ interior S ↔ y ∈ interior S := by
    induction hxy with
    | rel a b hab => exact ⟨fun ha ↦ hstep ha hab, fun hb ↦ hstep hb (hsymm hab)⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, hxy⟩
  apply mem_interior_iff_mem_nhds.mp
  apply (hpres hxy).mp
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hO.mem_nhds hx) (fun z hz ↦ ⟨z, hz, Relation.EqvGen.refl _⟩))

/-- One-box plaque saturation is open: take the open coordinate preimage,
project to the transverse factor, pull that open set back to the product,
and apply the open box map. This is the local foliation saturation calculation. -/
theorem isOpen_one_box_saturation
    {P U V : Type*} [TopologicalSpace P] [TopologicalSpace U] [TopologicalSpace V]
    (B : U × V → P) (hB : Continuous B) (hBo : IsOpenMap B)
    (O : Set P) (hO : IsOpen O) :
    IsOpen {y | ∃ u u' v, B (u, v) ∈ O ∧ B (u', v) = y} := by
  have ho := hBo (Prod.snd ⁻¹' (Prod.snd '' (B ⁻¹' O)))
    ((isOpenMap_snd _ (hO.preimage hB)).preimage continuous_snd)
  convert ho using 1
  ext y
  constructor
  · rintro ⟨u, u', v, hu, hy⟩
    exact ⟨(u', v), ⟨(u, v), hu, rfl⟩, hy⟩
  · rintro ⟨⟨u', v⟩, ⟨⟨u, w⟩, hu, hv⟩, hy⟩
    change w = v at hv
    subst w
    exact ⟨u, u', v, hu, hy⟩

/-- The symmetric relation generated by individual rows of a family of
actual open rectangular boxes. Its equivalence closure is the leaf relation
generated by those plaques; no global-leaf assertion enters this definition. -/
def rectangularPlaqueRel
    {P ι : Type*} {U V : ι → Type*} (B : ∀ i, U i × V i → P) (x y : P) : Prop :=
  ∃ i u u' v, B i (u, v) = x ∧ B i (u', v) = y

/-- Finite chains of actual rectangular plaques preserve openness of
saturation. Source: Franks (1970), local product foliation topology. The
one-step saturation is the union of the open one-box saturations, and the
proved symmetric-equivalence saturation lemma extends this to finite chains. -/
theorem isOpen_rectangularPlaque_saturation
    {P ι : Type*} {U V : ι → Type*}
    [TopologicalSpace P] [∀ i, TopologicalSpace (U i)] [∀ i, TopologicalSpace (V i)]
    (B : ∀ i, U i × V i → P) (hB : ∀ i, Continuous (B i))
    (hBo : ∀ i, IsOpenMap (B i)) (O : Set P) (hO : IsOpen O) :
    IsOpen {y | ∃ x ∈ O, Relation.EqvGen (rectangularPlaqueRel B) x y} := by
  apply isOpen_eqvGen_saturation (rectangularPlaqueRel B) ?_ ?_ O hO
  · rintro x y ⟨i, u, u', v, hx, hy⟩
    exact ⟨i, u', u, v, hy, hx⟩
  · intro W hW
    have ho := isOpen_iUnion (fun i ↦ isOpen_one_box_saturation (B i) (hB i) (hBo i) W hW)
    convert ho using 1
    ext y
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, i, u, u', v, he, hy⟩
      exact ⟨i, u, u', v, he ▸ hx, hy⟩
    · rintro ⟨i, u, u', v, hx, hy⟩
      exact ⟨B i (u, v), hx, i, u, u', v, rfl, hy⟩

/-- Paths within generating plaques concatenate to paths in their generated
leaf. Source: Franks (1970), intrinsic connected leaves via plaque chains.
Reversal uses symmetry of the equivalence closure; concatenation uses its
transitivity to keep the second path in the original starting class. -/
theorem exists_path_in_eqvGen
    {P : Type*} [TopologicalSpace P] (R : P → P → Prop)
    (hpath : ∀ x y, R x y → ∃ γ : Path x y, ∀ t, Relation.EqvGen R x (γ t))
    {x y : P} (hxy : Relation.EqvGen R x y) :
    ∃ γ : Path x y, ∀ t, Relation.EqvGen R x (γ t) := by
  induction hxy with
  | rel x y hxy => exact hpath x y hxy
  | refl x => exact ⟨Path.refl x, fun _ ↦ Relation.EqvGen.refl x⟩
  | symm x y hxy ih =>
    obtain ⟨γ, hγ⟩ := ih
    exact ⟨γ.symm, fun t ↦ Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hxy) (hγ (unitInterval.symm t))⟩
  | trans x y z hxy hyz ih₁ ih₂ =>
    obtain ⟨γ, hγ⟩ := ih₁
    obtain ⟨η, hη⟩ := ih₂
    refine ⟨γ.trans η, ?_⟩
    intro t
    simp only [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact Relation.EqvGen.trans _ _ _ hxy (hη _)

/-- The equivalence classes generated by path-connected rectangular plaques
have actual paths remaining in the class. The parameter path is mapped by
the original box; finite-chain path concatenation handles the full class. -/
theorem rectangularPlaque_path_in_class
    {P ι : Type*} {U V : ι → Type*}
    [TopologicalSpace P] [∀ i, TopologicalSpace (U i)] [∀ i, TopologicalSpace (V i)]
    [∀ i, PathConnectedSpace (U i)]
    (B : ∀ i, U i × V i → P) (hB : ∀ i, Continuous (B i))
    {x y : P} (hxy : Relation.EqvGen (rectangularPlaqueRel B) x y) :
    ∃ γ : Path x y, ∀ t, Relation.EqvGen (rectangularPlaqueRel B) x (γ t) := by
  apply exists_path_in_eqvGen (rectangularPlaqueRel B) ?_ hxy
  rintro x y ⟨i, u, u', v, rfl, rfl⟩
  let γ := PathConnectedSpace.somePath u u'
  let lift : C(U i, P) := ⟨fun w ↦ B i (w, v),
    (hB i).comp (continuous_id.prodMk continuous_const)⟩
  exact ⟨γ.map lift.continuous, fun t ↦
    Relation.EqvGen.rel _ _ ⟨i, u, γ t, v, rfl, rfl⟩⟩

/-- Restrict an actual local product chart to path-connected open coordinate
factors inside a prescribed neighborhood. Source: the local plaque shrinking
in Franks (1970), Proposition 1.1. The product-neighborhood basis gives two
coordinate neighborhoods; local path connectedness shrinks each to a
path-connected open set. The restricted chart is still an open embedding.
This preserves the actual chart values, hence every native plaque factorization. -/
theorem exists_pathConnected_rectangle
    {A C P : Type*} [TopologicalSpace A] [TopologicalSpace C] [TopologicalSpace P]
    [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace C]
    (e : OpenPartialHomeomorph (A × C) P) (z : A × C) (hz : z ∈ e.source)
    (O : Set P) (hO : IsOpen O) (hzO : e z ∈ O) :
    ∃ (U : TopologicalSpace.Opens A) (V : TopologicalSpace.Opens C),
      z.1 ∈ U ∧ z.2 ∈ V ∧ IsPathConnected (U : Set A) ∧
      IsPathConnected (V : Set C) ∧
      (∀ u : U, ∀ v : V, (u.val, v.val) ∈ e.source ∧ e (u.val, v.val) ∈ O) ∧
      _root_.Topology.IsOpenEmbedding (fun w : U × V ↦ e (w.1.val, w.2.val)) := by
  obtain ⟨U₀, hU₀, V₀, hV₀, hrect⟩ := mem_nhds_prod_iff.mp
    ((e.isOpen_inter_preimage hO).mem_nhds ⟨hz, hzO⟩)
  obtain ⟨U, ⟨hU, hzu, hUc⟩, hUU⟩ := (isOpen_isPathConnected_basis z.1).mem_iff.mp hU₀
  obtain ⟨V, ⟨hV, hzv, hVc⟩, hVV⟩ := (isOpen_isPathConnected_basis z.2).mem_iff.mp hV₀
  let U' : TopologicalSpace.Opens A := ⟨U, hU⟩
  let V' : TopologicalSpace.Opens C := ⟨V, hV⟩
  have hr (w : U' × V') : (w.1.val, w.2.val) ∈ e.source ∧
      e (w.1.val, w.2.val) ∈ O := hrect ⟨hUU w.1.property, hVV w.2.property⟩
  refine ⟨U', V', hzu, hzv, hUc, hVc, fun u v ↦ hr (u,v), ?_⟩
  have hi : _root_.Topology.IsOpenEmbedding
      (fun w : U' × V' ↦ (w.1.val, w.2.val)) :=
    hU.isOpenEmbedding_subtypeVal.prodMap hV.isOpenEmbedding_subtypeVal
  have his : _root_.Topology.IsOpenEmbedding
      (fun w : U' × V' ↦ (⟨(w.1.val, w.2.val), (hr w).1⟩ : e.source)) :=
    _root_.Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hi.continuous.subtype_mk _) (fun _ _ h ↦ hi.injective (congrArg Subtype.val h))
      (hi.isOpenMap.subtype_mk _)
  exact e.isOpenEmbedding_restrict.comp his

/-- Lift and shrink an actual downstairs product box through a covering sheet.
Source: the lifted product neighborhoods in Franks (1970), Proposition 1.1.
Choose the covering inverse at the marked upstairs point, compose it with the
original box, then restrict to path-connected open coordinate neighborhoods.
The resulting open embedding has exactly the original box as its projection;
thus native intrinsic row and column charts remain the receiving charts. -/
theorem covering_lift_pathConnected_box_within
    {M P A C : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [TopologicalSpace A] [TopologicalSpace C]
    [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace C]
    (p : P → M) (hp : IsCoveringMap p) (O : TopologicalSpace.Opens M)
    (e : (A × C) ≃ₜ O) (x : P) (hx : p x ∈ O)
    (W : Set P) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ (U : TopologicalSpace.Opens A) (V : TopologicalSpace.Opens C)
      (B : U × V → P), IsPathConnected (U : Set A) ∧ IsPathConnected (V : Set C) ∧
      _root_.Topology.IsOpenEmbedding B ∧ x ∈ Set.range B ∧ Set.range B ⊆ W ∧
      ∀ w, p (B w) = (e (w.1.val, w.2.val)).val := by
  let z := e.symm ⟨p x, hx⟩
  have hz : (e z).val = p x := congrArg Subtype.val (e.apply_symm_apply ⟨p x, hx⟩)
  have : Nonempty (A × C) := ⟨z⟩
  let b : A × C → M := fun w ↦ (e w).val
  have hb : _root_.Topology.IsOpenEmbedding b := O.isOpen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let E := hb.toOpenPartialHomeomorph b
  obtain ⟨s, hxs, hs⟩ := hp.isLocalHomeomorph x
  let F := E.trans s.symm
  have hzF : z ∈ F.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change b z ∈ s.target
    rw [show b z = p x from hz, hs]
    exact s.map_source hxs
  have hFx : F z = x := by
    change s.symm (b z) = x
    rw [show b z = p x from hz, hs]
    exact s.left_inv hxs
  obtain ⟨U, V, hzu, hzv, hUc, hVc, hUV, hB⟩ :=
    exists_pathConnected_rectangle F z hzF W hW (hFx.symm ▸ hxW)
  refine ⟨U, V, fun w ↦ F (w.1.val, w.2.val), hUc, hVc, hB, ?_, ?_, ?_⟩
  · exact ⟨(⟨z.1, hzu⟩, ⟨z.2, hzv⟩), hFx⟩
  · rintro y ⟨w,rfl⟩
    exact (hUV w.1 w.2).2
  · intro w
    change p (s.symm (b (w.1.val, w.2.val))) = b (w.1.val, w.2.val)
    rw [hs]
    exact s.right_inv (hUV w.1 w.2).1.2

/-- Unrestricted-neighborhood form of the covering product-box adapter. -/
theorem covering_lift_pathConnected_box
    {M P A C : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [TopologicalSpace A] [TopologicalSpace C]
    [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace C]
    (p : P → M) (hp : IsCoveringMap p) (O : TopologicalSpace.Opens M)
    (e : (A × C) ≃ₜ O) (x : P) (hx : p x ∈ O) :
    ∃ (U : TopologicalSpace.Opens A) (V : TopologicalSpace.Opens C)
      (B : U × V → P), IsPathConnected (U : Set A) ∧ IsPathConnected (V : Set C) ∧
      _root_.Topology.IsOpenEmbedding B ∧ x ∈ Set.range B ∧
      ∀ w, p (B w) = (e (w.1.val, w.2.val)).val := by
  obtain ⟨U,V,B,hU,hV,hB,hxB,_,hpB⟩ :=
    covering_lift_pathConnected_box_within p hp O e x hx Set.univ isOpen_univ (Set.mem_univ _)
  exact ⟨U,V,B,hU,hV,hB,hxB,hpB⟩

/-- Plaque chains remain in the native leaf relation when every actual
plaque does. This is the finite-chain definition of a foliation leaf. -/
theorem rectangularPlaque_eqvGen_subrelation
    {P ι : Type*} {U V : ι → Type*} (B : ∀ i, U i × V i → P)
    (R : Setoid P) (hrow : ∀ i u u' v, R (B i (u,v)) (B i (u',v)))
    {x y : P} (hxy : Relation.EqvGen (rectangularPlaqueRel B) x y) : R x y := by
  induction hxy with
  | rel a b hab =>
    obtain ⟨i,u,u',v,rfl,rfl⟩ := hab
    exact hrow i u u' v
  | refl a => exact R.refl a
  | symm _ _ _ ih => exact R.symm ih
  | trans _ _ _ _ _ ih ih' => exact R.trans ih ih'

/-- A box row whose projection factors through a continuous native leaf chart
belongs to the native lifted path relation. The coordinate domains here are
the already shrunk path-connected factors, so this does not assume an
ambient path lies in the intrinsic leaf topology. -/
theorem lifted_box_row_native
    {M P ι U V : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    [TopologicalSpace U] [TopologicalSpace V] [PathConnectedSpace U]
    (p : P → M) (j : ∀ i, L i → M) (B : U × V → P) (hB : Continuous B)
    (hrow : ∀ v, ∃ i, ∃ c : C(U,L i), ∀ u, p (B (u,v)) = j i (c u))
    (u u' : U) (v : V) : intrinsicLiftedPathRel p j (B (u,v)) (B (u',v)) := by
  obtain ⟨i,c,hc⟩ := hrow v
  exact intrinsicLiftedPathRel_of_plaque p j i c
    ⟨fun u ↦ B (u,v), hB.comp (continuous_id.prodMk continuous_const)⟩ hc u u'

/-- A family of actual open rectangular embeddings supplies joint local charts
for its row and column plaque-chain relations. The disjoint union of the
coordinate types puts all charts in one fixed target type, without identifying
unrelated native charts or changing their topologies. Source: the product box
construction used in Franks (1969), Lemma 1.6. -/
theorem rectangularPlaque_joint_box
    {P ι : Type*} {U V : ι → Type*}
    [TopologicalSpace P] [∀ i, TopologicalSpace (U i)] [∀ i, TopologicalSpace (V i)]
    (B : ∀ i, U i × V i → P)
    (hB : ∀ i, _root_.Topology.IsOpenEmbedding (B i))
    (x : P) (hx : ∃ i, x ∈ Set.range (B i)) :
    ∃ e : OpenPartialHomeomorph P ((Σ i, U i) × (Σ i, V i)), x ∈ e.source ∧
      ∀ a b, a ∈ e.source → b ∈ e.source →
        ((e a).1, (e b).2) ∈ e.target ∧
        Relation.EqvGen (rectangularPlaqueRel (fun i w ↦ B i (w.2,w.1)))
          a (e.symm ((e a).1,(e b).2)) ∧
        Relation.EqvGen (rectangularPlaqueRel B) b (e.symm ((e a).1,(e b).2)) := by
  obtain ⟨i,w,rfl⟩ := hx
  have : Nonempty (U i × V i) := ⟨w⟩
  let j : U i × V i → (Σ i,U i) × (Σ i,V i) :=
    fun z ↦ (⟨i,z.1⟩,⟨i,z.2⟩)
  have hj : _root_.Topology.IsOpenEmbedding j :=
    _root_.Topology.IsOpenEmbedding.sigmaMk.prodMap
      _root_.Topology.IsOpenEmbedding.sigmaMk
  let EB := (hB i).toOpenPartialHomeomorph (B i)
  let EJ := hj.toOpenPartialHomeomorph j
  let e := EB.symm.trans EJ
  have he (z : U i × V i) : e (B i z) = j z := by
    change j (EB.symm (B i z)) = j z
    rw [(hB i).toOpenPartialHomeomorph_left_inv]
  have hei (z : U i × V i) : e.symm (j z) = B i z := by
    change B i (EJ.symm (j z)) = B i z
    rw [hj.toOpenPartialHomeomorph_left_inv]
  have hes (z : U i × V i) : B i z ∈ e.source :=
    ⟨⟨z,Set.mem_univ _,rfl⟩, Set.mem_univ _⟩
  refine ⟨e, hes w, ?_⟩
  intro a b ha hb
  obtain ⟨wa,_,rfl⟩ := ha.1
  obtain ⟨wb,_,rfl⟩ := hb.1
  rw [he,he]
  change j (wa.1,wb.2) ∈ e.target ∧ _
  have hjcross : ((j wa).1,(j wb).2) = j (wa.1,wb.2) := rfl
  rw [hjcross, hei]
  refine ⟨?_, Relation.EqvGen.rel _ _ ?_, Relation.EqvGen.rel _ _ ?_⟩
  · simpa only [he] using e.map_source (hes (wa.1,wb.2))
  · exact ⟨i,wa.2,wb.2,wa.1,rfl,rfl⟩
  · exact ⟨i,wb.1,wa.1,wb.2,rfl,rfl⟩

/-- Once the generated plaques have global intersections, their relations are
exactly the original native lifted leaf relations. Source: Franks (1969),
uniqueness in Lemma 1.6. For a native-related pair, intersect the generated
leaf through the first point with the opposite generated leaf through the
second. The second point is already a native intersection; native uniqueness
identifies it with the generated intersection. This recovers native dynamic
and deck invariance without assuming the chosen box family is invariant. -/
theorem refining_leaf_relations_eq_of_global_product
    {P : Type*} (Lu Ls Nu Ns : Setoid P)
    (hu : ∀ x y, Lu x y → Nu x y) (hs : ∀ x y, Ls x y → Ns x y)
    (hunique : ∀ a b z z', Nu a z → Ns b z → Nu a z' → Ns b z' → z = z')
    (hproduct : ∀ a b, ∃ z, Lu a z ∧ Ls b z) :
    (∀ x y, Lu x y ↔ Nu x y) ∧ (∀ x y, Ls x y ↔ Ns x y) := by
  constructor
  · intro x y
    refine ⟨hu x y, fun hxy ↦ ?_⟩
    obtain ⟨z,hxz,hyz⟩ := hproduct x y
    have hzy : z = y := hunique x y z y (hu x z hxz) (hs y z hyz) hxy (Ns.refl y)
    exact hzy ▸ hxz
  · intro x y
    refine ⟨hs x y, fun hxy ↦ ?_⟩
    obtain ⟨z,hyz,hxz⟩ := hproduct y x
    have hzy : z = y := hunique y x z y (hu y z hyz) (hs x z hxz) (Nu.refl y) hxy
    exact hzy ▸ hxz

/-- Actual native leaf transports and an actual covering semiconjugacy preserve
marked lifted path relations. Compose the intrinsic path with the supplied
native transport and the upstairs path with the lifted map; their projected
paths agree pointwise. This applies to forward and inverse native dynamics. -/
theorem intrinsicLiftedPathRel_map
    {M P ι : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    (p : P → M) (j : ∀ i, L i → M) (F : C(P,P)) (g : M → M)
    (hsem : ∀ x, p (F x) = g (p x))
    (hleaf : ∀ i, ∃ i', ∃ c : C(L i,L i'), ∀ a, j i' (c a) = g (j i a))
    {x y : P} (hxy : intrinsicLiftedPathRel p j x y) :
    intrinsicLiftedPathRel p j (F x) (F y) := by
  obtain ⟨i,a,ha,b,γ,η,hη⟩ := hxy
  obtain ⟨i',c,hc⟩ := hleaf i
  refine ⟨i',c a, ?_, c b,γ.map c.continuous,η.map F.continuous, ?_⟩
  · rw [hc,ha,hsem]
  · intro t
    exact (hsem (η t)).trans ((congrArg g (hη t)).trans (hc (γ t)).symm)

/-- Integer deck maps preserve the actual native lifted path relation, using
the identity native leaf transport. No chosen box needs to be deck invariant. -/
theorem intrinsicLiftedPathRel_deck
    {M P ι : Type*} {L : ι → Type*}
    [TopologicalSpace M] [TopologicalSpace P] [∀ i, TopologicalSpace (L i)]
    (p : P → M) (j : ∀ i, L i → M) (δ : C(P,P))
    (hdeck : ∀ x, p (δ x) = p x)
    {x y : P} (hxy : intrinsicLiftedPathRel p j x y) :
    intrinsicLiftedPathRel p j (δ x) (δ y) :=
  intrinsicLiftedPathRel_map p j δ id hdeck
    (fun i ↦ ⟨i,ContinuousMap.id _,fun _ ↦ rfl⟩) hxy

end HolomorphicAnosov.FranksOriginalCover

