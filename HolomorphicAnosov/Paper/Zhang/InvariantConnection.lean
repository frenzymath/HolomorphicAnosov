import HolomorphicAnosov.Paper.Zhang.CompatiblePullbackSequenceC0Limit
import HolomorphicAnosov.Paper.Zhang.UnstableBottInvolutive
import HolomorphicAnosov.Paper.Zhang.CompatibleInvariantConnectionsAgree
import HolomorphicAnosov.Paper.Zhang.ContinuousDifferenceValuesBounded
import HolomorphicAnosov.Paper.Zhang.ComplexUnstableInvariant
import HolomorphicAnosov.Paper.Zhang.QuotientLineRank
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus

/-! This file constructs the unique continuous invariant quotient-line connection and proves convergence of compatible connections. (Zhang, Lemma 2.2) -/

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection



/-- The invariant connection and global C⁰ convergence of every smooth compatible seed. (Zhang, Lemma 2.2) -/
theorem lemma_2_2_invariant_connection
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (_hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU_holomorphic : IsHolomorphicTangentSubbundle (d - 1) U) :
    let smoothConnection := fun (D : Connection U) ↦
      ∀ (V : Opens X) (e : HolomorphicFrame U V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (coordinateForm D e c) (c.target ∩ c.symm ⁻¹' (V : Set X))
    (∀ D D' : Connection U, IsContinuous D → IsContinuous D' →
      BddAbove (differenceValues a.metric D D')) ∧
    ∃ (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
        mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x)),
      let pullbackLaw := fun (Dp D : Connection U) ↦
        ∀ (V W : Opens X) (e : HolomorphicFrame U V) (e' : HolomorphicFrame U W)
          (x : X), x ∈ V → f x ∈ W →
          Dp.form V e x =
            (imageFrameCoefficient f hU e e' x)⁻¹ •
              realDifferential (imageFrameCoefficient f hU e e') x +
            (D.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x)
      let isPullbackSequence := fun (D0 : Connection U) (Ds : ℕ → Connection U) ↦
        Agrees (Ds 0) D0 ∧ ∀ n, smoothConnection (Ds n) ∧
          IsCompatible (Ds n) ∧ pullbackLaw (Ds (n + 1)) (Ds n)
      ∃ D : Connection U,
        IsContinuous D ∧ IsCompatible D ∧ IsInvariant D f hU ∧
        (∀ D' : Connection U, IsContinuous D' → IsCompatible D' →
          IsInvariant D' f hU → Agrees D' D) ∧
        (∀ D0 : Connection U, smoothConnection D0 → IsCompatible D0 →
          (∃ Ds : ℕ → Connection U, isPullbackSequence D0 Ds) ∧
          ∀ Ds : ℕ → Connection U, isPullbackSequence D0 Ds →
            Tendsto (fun n ↦ c0Distance a.metric (Ds n) D) atTop (𝓝 0)) := by
  have hU := complex_unstable_invariant f a U hU_real
  have hline := quotient_line_of_holomorphic_codimension_one (by omega : 1 ≤ d)
    U hU_holomorphic
  have hcover := ConnectionCalculus.holomorphic_frame_cover U hU_holomorphic hline
  let smoothConnection := fun (D : Connection U) ↦
      ∀ (V : Opens X) (e : HolomorphicFrame U V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (coordinateForm D e c) (c.target ∩ c.symm ⁻¹' (V : Set X))
  let pullbackLaw := fun (Dp D : Connection U) ↦
        ∀ (V W : Opens X) (e : HolomorphicFrame U V) (e' : HolomorphicFrame U W)
          (x : X), x ∈ V → f x ∈ W →
          Dp.form V e x =
            (imageFrameCoefficient f hU e e' x)⁻¹ •
              realDifferential (imageFrameCoefficient f hU e e') x +
            (D.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x)
  let isPullbackSequence := fun (D0 : Connection U) (Ds : ℕ → Connection U) ↦
        Agrees (Ds 0) D0 ∧ ∀ n, smoothConnection (Ds n) ∧
          IsCompatible (Ds n) ∧ pullbackLaw (Ds (n + 1)) (Ds n)
  refine ⟨?_, hU, ?_⟩
  · exact fun D D' hD hD' ↦
      continuous_difference_values_bounded hcover a.metric D D' hD hD'
  · classical
    obtain ⟨-, -, -, -, -, -, hseed, -, hpull, -⟩ :=
      ConnectionCalculus.zhang_connection_calculus U hU_holomorphic hline
        (unstable_bott_involutive f a U hU_real)
    obtain ⟨Q, hQ, hPull⟩ := hpull f hU
    let E := {D : Connection U // smoothConnection D ∧ IsCompatible D}
    have hnext : ∀ D : E, ∃ Dp : E, pullbackLaw Dp.val D.val := by
      intro D
      obtain ⟨Dp, hs, hp, hcomp, -⟩ := hPull D.val D.property.1
      exact ⟨⟨Dp, hs, hcomp D.property.2⟩, hp⟩
    choose next hnext using hnext
    have hexseq (D0 : Connection U) (hs0 : smoothConnection D0) (hc0 : IsCompatible D0) :
        ∃ Ds : ℕ → Connection U, isPullbackSequence D0 Ds := by
      let Dstart : E := ⟨D0, hs0, hc0⟩
      refine ⟨fun n ↦ ((next^[n]) Dstart).val, ?_, ?_⟩
      · exact fun V e x hx ↦ rfl
      · intro n
        refine ⟨((next^[n]) Dstart).property.1, ((next^[n]) Dstart).property.2, ?_⟩
        change pullbackLaw ((next^[n + 1]) Dstart).val ((next^[n]) Dstart).val
        rw [Function.iterate_succ_apply']
        exact hnext _
    have hlimit (D0 : Connection U) (Ds : ℕ → Connection U)
        (hs : isPullbackSequence D0 Ds) :
        ∃ D : Connection U, IsContinuous D ∧ IsCompatible D ∧ IsInvariant D f hU ∧
          (∀ n, BddAbove (differenceValues a.metric (Ds n) D)) ∧
          Tendsto (fun n ↦ c0Distance a.metric (Ds n) D) atTop (𝓝 0) := by
      apply compatible_pullback_sequence_c0_limit hU_holomorphic f a hU_real hcover hU Ds
      · intro n V e c hc
        exact ((hs.2 n).1 V e c hc).continuousOn
      · exact fun n ↦ (hs.2 n).2.1
      · exact fun n ↦ (hs.2 n).2.2
    obtain ⟨D0, hs0, hc0⟩ := hseed
    obtain ⟨Ds, hseq⟩ := hexseq D0 hs0 hc0
    obtain ⟨D, hc, hcomp, hi, -, -⟩ := hlimit D0 Ds hseq
    refine ⟨D, hc, hcomp, hi, ?_, ?_⟩
    · intro D' hc' hcomp' hi'
      exact compatible_invariant_connections_agree f a hU_holomorphic hU_real
        hcover hU D D' hc hc' hcomp hcomp' hi hi'
    · intro D0 hs0 hc0
      refine ⟨hexseq D0 hs0 hc0, ?_⟩
      intro Ds hseq
      obtain ⟨D', hc', hcomp', hi', -, hlim⟩ := hlimit D0 Ds hseq
      have hagree := compatible_invariant_connections_agree f a hU_holomorphic hU_real
        hcover hU D D' hc hc' hcomp hcomp' hi hi'
      apply hlim.congr'
      apply Eventually.of_forall
      intro n
      unfold c0Distance
      apply congrArg sSup
      ext t
      constructor <;> rintro ⟨V, e, x, hx, v, hv, ht⟩
      · exact ⟨V, e, x, hx, v, hv, by rw [← hagree V e x hx]; exact ht⟩
      · exact ⟨V, e, x, hx, v, hv, by rw [hagree V e x hx]; exact ht⟩


end HolomorphicAnosov
