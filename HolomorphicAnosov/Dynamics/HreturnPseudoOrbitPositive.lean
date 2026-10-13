import HolomorphicAnosov.Dynamics.SmalePeriodicShadowingClosure
import HolomorphicAnosov.Dynamics.SmaleCyclicShadowing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Homeomorph.Lemmas
namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- Exploratory splice lemma with the positive-time connector premise made explicit.
The source transitivity statement currently permits k=0; this file isolates the
indexing proof once a positive connector is available. -/
theorem hreturn_of_cyclic_basin_transitivity_pos
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    (L : Set X) (hL : L.Nonempty)
    (htrans : ∀ U V : Set X, IsOpen U → (U ∩ L).Nonempty →
      IsOpen V → (V ∩ L).Nonempty →
      ∃ k : ℕ, ((f : X → X)^[k] '' (U ∩ L) ∩ V).Nonempty)
    (hcyclic : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → X,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
          ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
            ∀ i, dist (j i) (q i) < ε)
    (x : X)
    (hstable : Tendsto (fun n : ℕ ↦ Metric.infDist ((f : X → X)^[n] x) L)
      atTop (𝓝 0))
    (hunstable : Tendsto (fun n : ℕ ↦ Metric.infDist ((f.symm : X → X)^[n] x) L)
      atTop (𝓝 0)) :
    ∀ W : Set X, IsOpen W → x ∈ W →
      ∃ k : ℕ, 0 < k ∧ (((f : X → X)^[k]) '' W ∩ W).Nonempty := by
  intro W hW hxW
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.mp hW x hxW
  obtain ⟨δ, hδ, hshadow⟩ := smale_periodic_shadowing_of_cyclic_semiconjugacy f hcyclic
    (ρ / 2) (by positivity)
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp
    (hstable.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 4)))
  obtain ⟨Nu, hNu⟩ := eventually_atTop.mp
    (hunstable.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < δ / 4)))
  let N := Ns + 1
  let M := Nu
  have hN : Metric.infDist ((f : X → X)^[N] x) L < δ / 4 := by
    exact hNs N (by dsimp [N]; omega)
  have hM : Metric.infDist ((f.symm : X → X)^[M] x) L < δ / 4 := by
    exact hNu M le_rfl
  obtain ⟨ls, hls, hlsd⟩ := (Metric.infDist_lt_iff hL).mp hN
  obtain ⟨lu, hlu, hlud⟩ := (Metric.infDist_lt_iff hL).mp hM
  obtain ⟨k, z, ⟨y, hy, hyz⟩, hzy⟩ := htrans
    (Metric.ball ls (δ / 4)) (Metric.ball lu (δ / 4))
    Metric.isOpen_ball ⟨ls, ⟨Metric.mem_ball_self (by positivity), hls⟩⟩
    Metric.isOpen_ball ⟨lu, ⟨Metric.mem_ball_self (by positivity), hlu⟩⟩
  have hyclose : dist ((f : X → X)^[N] x) y < δ / 2 := by
    have hyd : dist y ls < δ / 4 := Metric.mem_ball.mp hy.1
    have hyd' : dist ls y < δ / 4 := by simpa [dist_comm] using hyd
    calc
      dist ((f : X → X)^[N] x) y ≤ dist ((f : X → X)^[N] x) ls + dist ls y := dist_triangle _ _ _
      _ < δ / 2 := by linarith
  have hzclose : dist ((f : X → X)^[k] y) ((f.symm : X → X)^[M] x) < δ / 2 := by
    have hzy' : dist ((f : X → X)^[k] y) lu < δ / 4 := by
      rw [hyz]
      exact Metric.mem_ball.mp hzy
    have hlud' : dist lu ((f.symm : X → X)^[M] x) < δ / 4 := by
      simpa [dist_comm] using hlud
    calc
      dist ((f : X → X)^[k] y) ((f.symm : X → X)^[M] x) ≤
        dist ((f : X → X)^[k] y) lu + dist lu ((f.symm : X → X)^[M] x) := dist_triangle _ _ _
      _ < δ / 2 := by linarith
  have hbridge0 (hk0 : k = 0) :
      dist ((f : X → X)^[N] x) ((f.symm : X → X)^[M] x) < δ := by
    have hy0 : dist y ((f.symm : X → X)^[M] x) < δ / 2 := by
      simpa [hk0] using hzclose
    calc
      dist ((f : X → X)^[N] x) ((f.symm : X → X)^[M] x) ≤
          dist ((f : X → X)^[N] x) y + dist y ((f.symm : X → X)^[M] x) := dist_triangle _ _ _
      _ < δ := by linarith
  let C := N + k + M
  let q : ℕ → X := fun j ↦
    if j < N then (f : X → X)^[j] x
    else if j < N + k then (f : X → X)^[j - N] y
    else (f : X → X)^[j - (N + k)] ((f.symm : X → X)^[M] x)
  have hq0 : q 0 = x := by
    have hNpos : 0 < N := by dsimp [N]; omega
    simp [q, hNpos]
  have hqC : q C = q 0 := by
    have hCM : C - (N + k) = M := by dsimp [C]; omega
    have hCgt : ¬ C < N := by dsimp [C]; omega
    have hCmid : ¬ C < N + k := by dsimp [C]; omega
    simp only [q, hCgt, hCmid, ↓reduceIte, hCM, hq0]
    exact Function.LeftInverse.iterate f.apply_symm_apply M x
  have hiter (r : ℕ) (a : X) : f ((f : X → X)^[r] a) = (f : X → X)^[r + 1] a := by
    symm
    simpa [Nat.succ_eq_add_one] using Function.iterate_succ_apply' (f : X → X) r a
  have hqjump : ∀ j < C, dist (f (q j)) (q (j + 1)) < δ := by
    intro j hj
    by_cases hj0 : j + 1 < N
    · have hj : j < N := by omega
      simp only [q, hj, hj0, ↓reduceIte]
      rw [hiter]
      exact dist_self _ |>.trans_lt hδ
    · by_cases hj1 : j < N
      · have hjEq : j + 1 = N := by omega
        have hjsub : j + 1 - N = 0 := by omega
        have hj1not : ¬ j + 1 < N := by omega
        by_cases hk0 : k = 0
        · have hNtail : ¬ N < N + k := by omega
          simp only [q, hj1, hj0, hjsub,
            Function.iterate_zero_apply, ↓reduceIte]
          rw [hiter, hjEq]
          have hsubzero : N - (N + k) = 0 := by omega
          simp only [ite_eq_right hNtail, hsubzero, Function.iterate_zero_apply]
          exact hbridge0 hk0
        · have hNmid : N < N + k := by omega
          simp only [q, hj1, hj0, hjsub,
            Function.iterate_zero_apply, ↓reduceIte]
          rw [hiter, hjEq]
          simp only [ite_eq_left hNmid]
          exact lt_trans hyclose (by linarith)
      · have hjN : N ≤ j := by omega
        by_cases hj2 : j + 1 < N + k
        · have hj : j < N + k := by omega
          have hjnot : ¬ j < N := by omega
          have hj1not : ¬ j + 1 < N := by omega
          simp only [q, hjnot, hj1not, hj, hj2, ↓reduceIte]
          have hsub : j + 1 - N = (j - N) + 1 := by omega
          rw [hsub, hiter]
          exact dist_self _ |>.trans_lt hδ
        · by_cases hj3 : j < N + k
          · have hjEq : j + 1 = N + k := by omega
            have hjsub : j + 1 - N = k := by omega
            have hjnext : j + 1 - (N + k) = 0 := by omega
            have hjnot : ¬ j < N := by omega
            have hj1not : ¬ j + 1 < N := by omega
            have hj1next : ¬ j + 1 < N + k := by omega
            have hjpow : j - N + 1 = k := by omega
            simp only [q, hjnot, hj1not, hj3, hj1next, hjnext,
              Function.iterate_zero_apply, ↓reduceIte]
            rw [hiter, hjpow]
            exact lt_trans hzclose (by linarith)
          · have hj : N + k ≤ j := by omega
            have hjnot : ¬ j < N := by omega
            have hj1not : ¬ j + 1 < N := by omega
            have hj1tail : ¬ j + 1 < N + k := by omega
            simp only [q, hjnot, hj1not, hj3, hj1tail, ↓reduceIte]
            have hsub : j + 1 - (N + k) = (j - (N + k)) + 1 := by omega
            rw [hsub, hiter]
            exact dist_self _ |>.trans_lt hδ
  obtain ⟨p, hp, hpclose⟩ := hshadow C (by dsimp [C]; omega) q hqC
    (fun j hj => hqjump j (by simpa [C] using hj))
  have hpW : p ∈ W := hρW (by
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hpclose (by linarith))
  refine ⟨C, by dsimp [C]; omega, p, ⟨p, hpW, ?_⟩, hpW⟩
  exact hp
end HolomorphicAnosov
