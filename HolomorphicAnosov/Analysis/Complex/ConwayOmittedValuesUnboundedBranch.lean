import HolomorphicAnosov.Analysis.Complex.ConwayCenterBoundPropagationG7
import HolomorphicAnosov.Analysis.Complex.ConwayConnectedBoundG7
import HolomorphicAnosov.Geometry.LyubichModularLambdaCover
import Mathlib.Analysis.Convex.Contractible

open Set Filter Metric
open scoped Topology

/-!
# Unbounded branch of Conway's omitted-values normality theorem

DAG node: `analysis.conway_omitted_values_unbounded_branch_g7`.
Source: Conway, Functions of One Complex Variable II, XVI §4 Theorem 4.2,
pp.124–125, together with Conway I, VII §§1–3.
-/

namespace HolomorphicAnosov

/-- The two excluded compact-bound alternatives cannot both fail.

This proof expands Conway II XVI Theorem 4.2 pp.124–125 by center-bound
propagation. The modular-lambda construction supplies a holomorphic disk cover.
On a simply connected disk, two square-root reductions move bounded center
values into a compact subset away from zero and one. The covering-lift claim
then gives compact bounds, and an open-and-closed argument propagates them
through the connected domain. At a fixed point, either infinitely many original
values have norm at most one, or eventually their reciprocals do. Extract the
corresponding strictly increasing subsequence and propagate its point bound;
either case contradicts the hypothesis. The empty domain is vacuous.

The uniform double-root reduction and connected propagation are agent-written
expansions, recorded separately in the DAG. No spherical-limit classification
is used. The theorem retains its original statement.
-/
theorem conway_omitted_values_unbounded_branch_g7
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsPreconnected G) (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) G)
    (homit : ∀ n z, z ∈ G → f n z ≠ 0 ∧ f n z ≠ 1)
    (hNoSub : ¬ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ K : Set ℂ, IsCompact K → K ⊆ G →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖f (ψ n) z‖ ≤ M) ∨
        (∀ K : Set ℂ, IsCompact K → K ⊆ G →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖(f (ψ n) z)⁻¹‖ ≤ M))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ h : ℂ → ℂ, DifferentiableOn ℂ h G ∧
          ∀ K : Set ℂ, IsCompact K → K ⊆ G →
            TendstoUniformlyOn (fun k z ↦ f (φ k) z) h Filter.atTop K) ∨
        (∀ K : Set ℂ, IsCompact K → K ⊆ G →
          ∀ M : ℝ, 0 < M → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
            ∀ z : ℂ, z ∈ K → M < ‖f (φ k) z‖)) := by
  classical
  exfalso
  apply hNoSub
  by_cases hne : G.Nonempty
  swap
  · refine ⟨id, strictMono_id, Or.inl ?_⟩
    intro K hK hKG
    exact ⟨0, le_rfl, fun n z hz ↦ (hne ⟨z, hKG hz⟩).elim⟩
  obtain ⟨a, ha⟩ := hne
  let T : MarkedIdealDiskTriangle := {
    vertex := ![1, Complex.I, -1]
    norm_vertex := by intro i; fin_cases i <;> simp
    distinct := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | (have hre := congrArg Complex.re hij; norm_num at hre)
    positive_order := by
      refine ⟨0, Real.pi / 2, Real.pi, by positivity, ?_, ?_, ?_, ?_, ?_⟩
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · simp
      · simp [Complex.exp_mul_I]
      · simp
  }
  obtain ⟨lam, hlam, hcover, hrange, _, hlocal, _⟩ := lyubich_modular_lambda_cover T
  have hglobal (F : ℕ → ℂ → ℂ) (hF : ∀ n, DifferentiableOn ℂ (F n) G)
      (hFo : ∀ n z, z ∈ G → F n z ≠ 0 ∧ F n z ≠ 1)
      (hFa : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖F n a‖ ≤ M) :
      ∀ K : Set ℂ, IsCompact K → K ⊆ G →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, z ∈ K → ‖F n z‖ ≤ M := by
    apply conway_connected_compact_bound_g7 hG hconn F _ ha hFa
    intro x r hr hrG b hb hbB K hK hKB
    have : ContractibleSpace (ball x r) :=
      (convex_ball x r).contractibleSpace ⟨x, mem_ball_self hr⟩
    have hsimply : IsSimplyConnected (ball x r) := SimplyConnectedSpace.ofContractible _
    obtain ⟨M, hM, hMb⟩ := hbB
    exact conway_center_bound_compact_bound_g7 isOpen_ball hsimply hlam hcover hrange
      hlocal F (fun n ↦ (hF n).mono hrG) (fun n z hz ↦ hFo n z (hrG hz))
      hb hM hMb K hK hKB
  by_cases hfreq : ∃ᶠ n in atTop, ‖f n a‖ ≤ 1
  · obtain ⟨φ, hφ, hφB⟩ := extraction_of_frequently_atTop hfreq
    exact ⟨φ, hφ, Or.inl (hglobal (fun n ↦ f (φ n)) (fun n ↦ hf (φ n))
      (fun n ↦ homit (φ n)) ⟨1, by norm_num, hφB⟩)⟩
  · have hlarge : ∀ᶠ n in atTop, 1 < ‖f n a‖ := by simpa using hfreq
    obtain ⟨φ, hφ, hφB⟩ := extraction_of_eventually_atTop hlarge
    refine ⟨φ, hφ, Or.inr ?_⟩
    apply hglobal (fun n z ↦ (f (φ n) z)⁻¹)
    · exact fun n ↦ (hf (φ n)).inv (fun z hz ↦ (homit (φ n) z hz).1)
    · intro n z hz
      exact ⟨inv_ne_zero (homit (φ n) z hz).1,
        fun he ↦ (homit (φ n) z hz).2 (inv_eq_one.mp he)⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro n
      rw [norm_inv]
      exact (inv_le_one₀ (lt_trans zero_lt_one (hφB n))).mpr (hφB n).le

end HolomorphicAnosov

