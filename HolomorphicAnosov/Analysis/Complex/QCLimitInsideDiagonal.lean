import HolomorphicAnosov.Analysis.Complex.QCLimitCompactContainment

namespace HolomorphicAnosov
open Set Filter _root_.Topology

/-- The actual diagonal choice in Lehto–Virtanen I.Theorem 5.2, p.29.
For each inner compact set choose an eventual threshold for image containment and the
prescribed uniform error on the whole compact test region. Recursively choose the next index
above that threshold and the previous index. The resulting subsequence is strictly increasing,
stays beyond any fixed initial tail, and has the two estimates simultaneously. -/
theorem qc_limit_inside_diagonal
    {U C V : Set ℂ} {Cinner : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hC : IsCompact C) (hCU : C ⊆ U) (hg : ContinuousOn g C)
    (hInner : ∀ j, IsCompact (Cinner j)) (hInnerC : ∀ j, Cinner j ⊆ C)
    (hV : IsOpen V) (hgV : ∀ j, MapsTo g (Cinner j) V)
    (hF : TendstoLocallyUniformlyOn F g atTop U)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (N : ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, N ≤ φ j ∧ j ≤ φ j ∧
      MapsTo (F (φ j)) (Cinner j) V ∧ ∀ x ∈ C, dist (F (φ j) x) (g x) < ε j := by
  have hFC : TendstoUniformlyOn F g atTop C :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).mp (hF.mono hCU)
  have hj : ∀ j, ∀ᶠ n in atTop, MapsTo (F n) (Cinner j) V ∧
      ∀ x ∈ C, dist (F n x) (g x) < ε j := by
    intro j
    filter_upwards [qc_limit_eventually_mapsTo (hInner j) ((hInnerC j).trans hCU)
      (hg.mono (hInnerC j)) hV (hgV j) hF,
      (Metric.tendstoUniformlyOn_iff.mp hFC) (ε j) (hε j)] with n hn hnε
    exact ⟨hn, fun x hx ↦ (dist_comm _ _).trans_lt (hnε x hx)⟩
  classical
  choose b hb using fun j ↦ eventually_atTop.mp (hj j)
  let φ : ℕ → ℕ := fun j ↦ Nat.rec (max N (b 0))
    (fun k prev ↦ max (prev + 1) (max N (b (k + 1)))) j
  have hφstep : ∀ j, φ j < φ (j + 1) := by
    intro j
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ hφstep
  refine ⟨φ, hφ, fun j ↦ ?_⟩
  have hNb : N ≤ φ j ∧ b j ≤ φ j := by
    cases j with
    | zero => exact ⟨le_max_left _ _, le_max_right _ _⟩
    | succ j => exact ⟨(le_max_left _ _).trans (le_max_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
  exact ⟨hNb.1, hφ.id_le j, hb j (φ j) hNb.2⟩


end HolomorphicAnosov
