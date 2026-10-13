import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import HolomorphicAnosov.Analysis.JointRealPartialDerivative
import HolomorphicAnosov.Analysis.Flow.ExistsRealC1LocalFlow
import HolomorphicAnosov.Analysis.Flow.AugmentedField
import HolomorphicAnosov.Analysis.Flow.AugmentedFieldContDiffOn
import HolomorphicAnosov.Analysis.Flow.JointDerivative
import HolomorphicAnosov.Analysis.Flow.FiniteOrderSuccessor
import HolomorphicAnosov.Analysis.Flow.JointDerivativeEqCoprod
import HolomorphicAnosov.Analysis.Flow.ContDiffOnOfLocalFamilies
import HolomorphicAnosov.Analysis.Flow.ExistsC1VariationalFlow

noncomputable section
universe u
open Set Filter Function ODE Metric
open scoped Manifold ContDiff Topology _root_.Topology NNReal

namespace HolomorphicAnosov.W07FiniteFlowBootstrap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Teschl's local finite-order theorem, closed under the augmented field and finite trajectory
continuation. Every order is obtained for the actual C1 family on its own fixed rectangle;
within the induction the augmented pair is propagated over that WHOLE rectangle. -/
theorem exists_real_finite_flow (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    ∀ (F : E → E) (Ω : Set E), IsOpen Ω → ContDiffOn ℝ (n + 1) F Ω →
    ∀ x ∈ Ω, ∃ (U : Set E) (δ : ℝ) (Φ : E × ℝ → E),
      IsOpen U ∧ x ∈ U ∧ 0 < δ ∧
      ContDiffOn ℝ (n + 1) Φ (U ×ˢ Ioo (-δ) δ) ∧
      (∀ w ∈ U, Φ (w, 0) = w) ∧
      (∀ w ∈ U, ∀ t ∈ Ioo (-δ) δ,
        HasDerivAt (fun r ↦ Φ (w, r)) (F (Φ (w, t))) t) ∧
      (∀ w ∈ U, ∀ t ∈ Ioo (-δ) δ, Φ (w, t) ∈ Ω) := by
  induction n with
  | zero =>
    intro E _ _ _ F Ω hΩ hF x hx
    obtain ⟨r, hr, δ, hδ, Φ, Y, hΦ, hY, hzero, hmem, htime, hder, happly⟩ :=
      RealC1FlowExistence.exists_real_c1_local_flow F Ω hΩ (by simpa using hF) x hx
    exact ⟨ball x r, δ, Φ, isOpen_ball, by simpa, hδ, by simpa using hΦ,
      hzero, fun w hw t ht ↦ htime (w, t) ⟨hw, ht⟩,
      fun w hw t ht ↦ hmem (w, t) ⟨hw, ht⟩⟩
  | succ n ih =>
    intro E _ _ _ F Ω hΩ hF x hx
    have hF1 : ContDiffOn ℝ 1 F Ω := hF.of_le (by simp)
    obtain ⟨r, hr, δ, hδ, α, Y, hcont, hmem, hzero, htime, hspace, hY,
      hYzero, hYtime⟩ := exists_c1_variational_flow F Ω hΩ hF1 x hx
    let U := ball x r
    let J := Ioo (-δ) δ
    let Φ : E × ℝ → E := fun p ↦ α p.1 p.2
    let Z : E × ℝ → E →L[ℝ] E := fun p ↦ Y p.1 p.2
    let Γ : E × ℝ → E × (E →L[ℝ] E) := fun p ↦ (Φ p, Z p)
    have h0 : (0 : ℝ) ∈ J := ⟨by linarith, hδ⟩
    have hflowF : ∀ q ∈ Ω, ∃ (A : Set E) (ε : ℝ) (Ψ : E × ℝ → E),
        IsOpen A ∧ q ∈ A ∧ 0 < ε ∧ ContDiffOn ℝ (n + 1) Ψ (A ×ˢ Ioo (-ε) ε) ∧
        (∀ w ∈ A, Ψ (w, 0) = w) ∧
        (∀ w ∈ A, ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (fun r ↦ Ψ (w, r)) (F (Ψ (w, t))) t) ∧
        (∀ w ∈ A, ∀ t ∈ Ioo (-ε) ε, Ψ (w, t) ∈ Ω) :=
      fun q hq ↦ ih F Ω hΩ (hF.of_le (by simp)) q hq
    have hΦn : ContDiffOn ℝ (n + 1) Φ (U ×ˢ J) :=
      W07FiniteFlowContinuation.contDiffOn_of_local_families hΩ hF1 (n + 1) hflowF
        isOpen_ball isOpen_Ioo ordConnected_Ioo h0 hcont
        (contDiffOn_id.congr (fun w hw ↦ hzero w hw))
        htime hmem
    let A := SmoothFlowBootstrap.augmentedField F
    let O := Ω ×ˢ (univ : Set (E →L[ℝ] E))
    have hO : IsOpen O := hΩ.prod isOpen_univ
    have hAn : ContDiffOn ℝ (n + 1) A O :=
      SmoothFlowBootstrap.augmentedField_contDiffOn F Ω hΩ (n + 1) (by simpa using hF)
    have hflowA := fun q hq ↦ ih A O hO hAn q hq
    have hΓtime (w : E) (hw : w ∈ U) (t : ℝ) (ht : t ∈ J) :
        HasDerivAt (fun s ↦ Γ (w, s)) (A (Γ (w, t))) t :=
      (htime w hw t ht).prodMk (hYtime w hw t ht)
    have hΓmem (w : E) (hw : w ∈ U) (t : ℝ) (ht : t ∈ J) : Γ (w, t) ∈ O :=
      ⟨hmem w hw t ht, mem_univ _⟩
    have hΓ0 : ContDiffOn ℝ (n + 1) (fun w ↦ Γ (w, 0)) U := by
      apply (contDiffOn_id.prodMk (contDiffOn_const (c := ContinuousLinearMap.id ℝ E))).congr
      intro w hw
      exact Prod.ext (hzero w hw) (hYzero w hw)
    have hΓn := W07FiniteFlowContinuation.contDiffOn_of_local_families hO
      (hAn.of_le (by simp)) (n + 1) hflowA isOpen_ball isOpen_Ioo ordConnected_Ioo h0
      (hcont.prodMk hY) hΓ0 hΓtime hΓmem
    have hFc : ContinuousOn (fun p : E × ℝ ↦ F (Φ p)) (U ×ˢ J) :=
      hF1.continuousOn.comp hcont (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2)
    have hd := HolomorphicAnosov.JointRealC1Scratch.joint_hasFDerivAt_of_partials
      α Y (fun w t ↦ F (α w t)) U J isOpen_ball isOpen_Ioo hspace htime hY hFc
    have hder : ∀ p ∈ U ×ˢ J,
        HasFDerivAt Φ (SmoothFlowBootstrap.jointDerivative Z (fun q ↦ F (Φ q)) p) p := by
      intro p hp
      rw [SmoothFlowBootstrap.jointDerivative_eq_coprod]
      exact hd p hp
    have hsuc := SmoothFlowBootstrap.finite_order_successor (U ×ˢ J)
      (isOpen_ball.prod isOpen_Ioo) (n + 1) Φ Z (fun p ↦ F (Φ p)) hder hΓn.snd
      ((hF.of_le (by simp)).comp hΦn (fun p hp ↦ hmem p.1 hp.1 p.2 hp.2))
    exact ⟨U, δ, Φ, isOpen_ball, by simpa [U], hδ, by simpa using hsuc, hzero, htime, hmem⟩

end HolomorphicAnosov.W07FiniteFlowBootstrap
