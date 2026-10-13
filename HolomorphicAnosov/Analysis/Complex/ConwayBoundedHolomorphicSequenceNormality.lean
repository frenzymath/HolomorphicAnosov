import HolomorphicAnosov.Analysis.Complex.ConwayCompactOpenAscoliNormality
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compact-open subsequence normality for bounded holomorphic sequences

Stage2 statement for `analysis.conway_bounded_holomorphic_sequence_normality_g2`,
following Conway, *Functions of One Complex Variable I*, VII §2 Theorem2.9, p.153.
-/

open Filter

namespace HolomorphicAnosov

/--
Conway, *Functions of One Complex Variable I*, Chapter VII, §2, Theorem 2.9,
printed p.153 (PDF p.164): a sequence of holomorphic functions locally bounded
on every compact subset of an open complex domain has a compact-open convergent
subsequence with holomorphic limit. Holomorphicity is complex differentiability on
`G`; the ambient total functions impose no condition outside `G`. On an open
complex domain, locally uniform convergence is equivalent to uniform convergence
on every compact subset (`tendstoLocallyUniformlyOn_iff_forall_isCompact`).

Proof from the DAG node `analysis.conway_bounded_holomorphic_sequence_normality_g2`:
Fix a point of `G` and a positive radius whose closed disk lies in `G`. The
compact-disk bound is uniform over the sequence. Schwarz's distance estimate
on the half-radius disk gives a common local Lipschitz bound and hence
equicontinuity, as does Conway's difference-of-Cauchy-formulas argument. The compact
singleton bound at each point puts the point-value family in a compact closed
complex ball. Conway VII 1.23 (printed pp.148–150), the compact-open Arzela–Ascoli
theorem, then extracts a strictly increasing subsequence with a continuous
compact-uniform limit. Convert this convergence to locally uniform convergence
on the open domain and apply Conway VII 2.1 (printed p.151) to obtain a
holomorphic limit. The same argument covers an empty domain, where the
convergence conditions are vacuous. No connectedness assumption is used.
-/
theorem conway_bounded_holomorphic_sequence_normality_g2
    {G : Set ℂ} (hG : IsOpen G) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) G)
    (hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ G →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖f n z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g G ∧
        ∀ K : Set ℂ, IsCompact K → K ⊆ G →
          TendstoUniformlyOn (fun n z => f (φ n) z) g atTop K := by
  classical
  -- Schwarz gives the common local modulus used in Conway's Ascoli argument.
  let u : ℕ → C(G, ℂ) := fun n ↦ ⟨fun z ↦ f n z, (hf n).continuousOn.domRestrict⟩
  have heq : ∀ a : G, EquicontinuousAt (fun v : Set.range u ↦ fun z : G ↦ v.val z) a := by
    intro a
    obtain ⟨r, hr, hrG⟩ := Metric.mem_nhds_iff.mp (hG.mem_nhds a.property)
    obtain ⟨M, hM, hMf⟩ := hbound (Metric.closedBall (a : ℂ) (r / 2))
      (isCompact_closedBall _ _) (fun z hz ↦ hrG (show dist z a < r from
        lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
    have hr2 : 0 < r / 2 := by positivity
    let L : ℝ := 2 * (M + 1) / (r / 2)
    have hL : 0 < L := by dsimp [L]; positivity
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    refine ⟨min (r / 2) (ε / L), lt_min hr2 (div_pos hε hL), ?_⟩
    intro z hz v
    rcases v with ⟨v, n, rfl⟩
    have hzball : (z : ℂ) ∈ Metric.ball (a : ℂ) (r / 2) :=
      lt_of_lt_of_le hz (min_le_left _ _)
    have hmaps : Set.MapsTo (f n) (Metric.ball (a : ℂ) (r / 2))
        (Metric.closedBall (f n a) (2 * (M + 1))) := by
      intro w hw
      change dist (f n w) (f n a) ≤ 2 * (M + 1)
      calc
        dist (f n w) (f n a) ≤ ‖f n w‖ + ‖f n a‖ := by simpa only [dist_eq_norm] using norm_sub_le (f n w) (f n a)
        _ ≤ M + M := add_le_add (hMf n w (Metric.ball_subset_closedBall hw))
          (hMf n a (Metric.mem_closedBall_self hr2.le))
        _ ≤ 2 * (M + 1) := by linarith
    have hdist := Complex.dist_le_div_mul_dist_of_mapsTo_ball
      ((hf n).mono (fun w hw ↦ hrG (show dist w a < r from lt_trans (Metric.mem_ball.mp hw) (by linarith)))) hmaps hzball
    change dist (f n a) (f n z) < ε
    rw [dist_comm]
    exact hdist.trans_lt ((mul_lt_mul_of_pos_left
      (lt_of_lt_of_le hz (min_le_right _ _)) hL).trans_eq (mul_div_cancel₀ ε hL.ne'))
  have hpt : ∀ a : G, IsCompact (closure ((fun v : C(G, ℂ) ↦ v a) '' Set.range u)) := by
    intro a
    obtain ⟨M, hM, hMf⟩ := hbound {a.val} (isCompact_singleton) (by simp)
    apply (isCompact_closedBall (0 : ℂ) M).of_isClosed_subset isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    rintro _ ⟨v, ⟨n, rfl⟩, rfl⟩
    change dist (f n a) 0 ≤ M
    rw [dist_zero_right]
    exact hMf n a (Set.mem_singleton _)
  obtain ⟨φ, hφ, v, hv⟩ :=
    (conway_compact_open_ascoli_normality_g2 hG (Set.range u)).mpr ⟨heq, hpt⟩
      u (fun n ↦ Set.mem_range_self n)
  let g : ℂ → ℂ := fun z ↦ if hz : z ∈ G then v ⟨z, hz⟩ else 0
  have hconv : ∀ K : Set ℂ, IsCompact K → K ⊆ G →
      TendstoUniformlyOn (fun n z ↦ f (φ n) z) g atTop K := by
    intro K hK hKG
    have hK' : IsCompact (Subtype.val ⁻¹' K : Set G) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKG)
    have ht := hv (Subtype.val ⁻¹' K) hK'
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with n hn
    intro z hz
    have := hn ⟨z, hKG hz⟩ hz
    change dist (v ⟨z, hKG hz⟩) (f (φ n) z) < ε at this
    simpa only [g, dite_eq_left (hKG hz)] using this
  refine ⟨φ, hφ, g, ?_, hconv⟩
  exact ((tendstoLocallyUniformlyOn_iff_forall_isCompact hG).mpr (fun K hKG hK ↦ hconv K hK hKG)).differentiableOn
    (Filter.Eventually.of_forall fun n ↦ hf (φ n)) hG

end HolomorphicAnosov

