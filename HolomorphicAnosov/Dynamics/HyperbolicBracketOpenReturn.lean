import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Order.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Hyperbolic bracket contraction and periodic-phase open returns

Agent omission-fill for dynamics.smale_original_anosov_spectral_basins_g7: Shub, Global
Stability of Dynamical Systems (Springer,1987), Chapter9 Proposition9.6 Remark(1),
printedp119/PDF132, literature/Shub-Global-Stability-1987-author.pdf/.txt. The author says the
open-set case has a direct proof using earlier techniques, but does not print that proof;
Proposition9.8 printedp120 uses that open return. This abstract point-contraction lemma is not
claimed to be printed in Shub.

This module states the agent omission-fill lemma recorded in DAG node
`dynamics.hyperbolic_bracket_periodic_phase_open_return_g1`. Stage2 leaves its Lean
proof postponed. No bracket continuity, uniqueness or compactness is assumed.
-/

open Filter Topology _root_.Topology

namespace HolomorphicAnosov

/-- Arbitrarily late open returns from stable and unstable asymptotics to periodic phases.

Source: Agent omission-fill for dynamics.smale_original_anosov_spectral_basins_g7: Shub, Global
Stability of Dynamical Systems (Springer,1987), Chapter9 Proposition9.6 Remark(1),
printedp119/PDF132, literature/Shub-Global-Stability-1987-author.pdf/.txt. The author says the
open-set case has a direct proof using earlier techniques, but does not print that proof;
Proposition9.8 printedp120 uses that open return. This abstract point-contraction lemma is not
claimed to be printed in Shub.

Natural-language proof (the complete agent-written proof of the DAG node):
1. Nontruncated natural times and periodic phase identities
   For each natural N≥1 set m_N=aN and ℓ_N=(aN+s)−r, where this subtraction is in N. Since r<a,
   r≤a−1 and r<a≤aN+s, no subtraction is truncated. Consequently ℓ_N+r=aN+s and the integer cast
   of ℓ_N is (a:Z)(N:Z)+(s:Z)−(r:Z). Also ℓ_N≥a(N−1)+1+s≥N and m_N=aN≥N. The canonical
   Homeomorph multiplication evaluates as composition. From zpow_add, f^(j+k)(x)=f^j(f^k(x)) for
   integers j,k, with f^0 the identity and f^(−j) the inverse of f^j. Induction using f^a(p)=p
   gives f^(aN)(p)=p; applying the inverse gives f^(−aN)(p)=p. Put q=f^s(p). Thus
   f^(ℓ_N+r)(p)=f^(aN+s)(p)=q and f^((s:Z)−(m_N:Z))(p)=q. In particular the backward phase
   subtraction is an integer subtraction, not natural truncated subtraction.

2. The two aligned orbit points approach one periodic phase
   Define b_N=f^ℓ_N(xs) and c_N=f^(−m_N)(xu) for N≥1. Write e_n=d(f^n xs,f^(n+r)p) and
   h_n=d(f^(−n)xu,f^((s:Z)−(n:Z))p). Both nonnegative real sequences tend to zero by hypothesis.
   Metric.tendsto_atTop, specialized to their real-valued limits, gives for every τ>0 thresholds
   after which e_n<τ and h_n<τ; the real distance from a nonnegative number to zero is that
   number. Since ℓ_N,m_N≥N, these thresholds apply to e_ℓ_N and h_m_N for every sufficiently
   large N. The phase identities give d(b_N,q)=e_ℓ_N and d(c_N,q)=h_m_N. Hence both aligned
   orbit points approach q, with an explicit common tail threshold for every positive τ.

3. Verify the close-pair guard before selecting a contraction point
   Apply the preceding thresholds with τ=ε0/3>0, and choose N_pair≥1 such that for every
   N≥N_pair both d(b_N,q)<ε0/3 and d(c_N,q)<ε0/3. By symmetry and the metric triangle
   inequality, d(b_N,c_N)≤d(b_N,q)+d(q,c_N)<2ε0/3<ε0. Only for such an N apply the stated close-
   pair hypothesis to b=b_N and c=c_N, obtaining a point z with d(z,b_N),d(z,c_N)≤γ and the two
   contraction inequalities. The proof below works for any such point. It requires neither a
   globally chosen bracket nor uniqueness or continuity of its choice.

4. Pull back the first endpoint and advance the second endpoint
   For N≥N_pair and a chosen z define y=f^(−ℓ_N)(z). In the backward contraction inequality take
   n=ℓ_N. Integer-power cancellation gives f^(−ℓ_N)(b_N)=xs, so d(y,xs)≤κ^ℓ_N d(z,b_N)≤γκ^ℓ_N.
   In the forward inequality take n=m_N. Since c_N=f^(−m_N)(xu), cancellation gives
   f^m_N(c_N)=xu, so d(f^m_N(z),xu)≤κ^m_N d(z,c_N)≤γκ^m_N. Multiplication preserves these
   inequalities because κ^ℓ_N and κ^m_N are nonnegative. Both bounds involve the same point z,
   with exactly the backward unstable and forward stable directions prescribed in the
   hypothesis.

5. One geometric tail bounds both endpoint errors
   From 0<κ<1 we have 0≤κ≤1. Apply pow_le_pow_of_le_one with smaller exponent N and larger
   exponent ℓ_N, and again with larger exponent m_N. The established inequalities N≤ℓ_N and
   N≤m_N give κ^ℓ_N≤κ^N and κ^m_N≤κ^N. Because γ>0, both endpoint errors are therefore at most
   γκ^N. The geometric-limit theorem gives κ^N→0, and multiplication by the fixed real γ gives
   γκ^N→0. For every η>0, Filter.Tendsto.eventually_lt_const yields γκ^N<η eventually;
   Filter.eventually_atTop converts this into one natural threshold valid for every subsequent
   N. These bounds hold for every admissible z chosen at that N, so no continuity of the
   contraction-point choice is being used.

6. Strict open-ball containment puts both endpoints in the prescribed sets
   Since U is open and xs∈U, Metric.isOpen_iff gives a real ρ_U>0 with ball(xs,ρ_U)⊆U. Similarly
   choose ρ_V>0 with ball(xu,ρ_V)⊆V. Apply the geometric tail with η=min(ρ_U,ρ_V)>0, obtaining
   N_ball such that γκ^N<min(ρ_U,ρ_V) for all N≥N_ball. For N≥max(N_pair,N_ball), the previous
   bounds imply d(y,xs)<ρ_U and d(f^m_N(z),xu)<ρ_V. The exact metric-ball membership criterion
   yields y∈U and f^m_N(z)∈V. Thus closed contraction bounds have been converted to strict
   inequalities before using openness.

7. An arbitrarily late positive iterate carries the first endpoint to the second
   Let L∈N be arbitrary. Choose N≥max(N_pair,N_ball) with N≥1 and N>L, and choose z using the
   verified close-pair guard. Put t=ℓ_N+m_N∈N. Then t≥2N>L, in particular t>0. Using the same
   integer-power composition and cancellation, f^t(y)=f^(ℓ_N+m_N)(f^(−ℓ_N)(z))=f^m_N(z). The
   left endpoint y belongs to U and the right endpoint belongs to V, so f^t(y) is an element of
   f^t(U)∩V. This proves the claimed return for every L. The argument also covers a=1 and zero-
   dimensional or singleton metric spaces whenever the hypotheses hold; the points xs and xu
   make the relevant open sets nonempty. No compactness, tangent dimension, transversality or
   smoothness enters this conclusion.

Integer powers are powers in the group of self-homeomorphisms; natural powers use
the corresponding group power. The endpoint directions are backward contraction
towards the first point and forward contraction towards the second point.
-/
theorem hyperbolic_bracket_periodic_phase_open_return
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    (γ ε₀ κ : ℝ) (hγ : 0 < γ) (hε₀ : 0 < ε₀) (hκ₀ : 0 < κ) (hκ₁ : κ < 1)
    (hbracket : ∀ b c : X, dist b c ≤ ε₀ →
      ∃ z : X, dist z b ≤ γ ∧ dist z c ≤ γ ∧
        ∀ n : ℕ,
          dist ((f ^ n) z) ((f ^ n) c) ≤ κ ^ n * dist z c ∧
          dist ((f ^ (-(n : ℤ))) z) ((f ^ (-(n : ℤ))) b) ≤ κ ^ n * dist z b)
    (a : ℕ) (ha : 1 ≤ a) (p : X) (hp : (f ^ a) p = p)
    (r s : ℕ) (hr : r < a) (_hs : s < a)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (xs xu : X) (hxs : xs ∈ U) (hxu : xu ∈ V)
    (hstable : Tendsto (fun n : ℕ ↦ dist ((f ^ n) xs) ((f ^ (n + r)) p))
      atTop (𝓝 (0 : ℝ)))
    (hunstable : Tendsto
      (fun n : ℕ ↦ dist ((f ^ (-(n : ℤ))) xu) ((f ^ ((s : ℤ) - (n : ℤ))) p))
      atTop (𝓝 (0 : ℝ))) :
    ∀ L : ℕ, ∃ t : ℕ, L < t ∧ Set.Nonempty (((f ^ t : X ≃ₜ X) : X → X) '' U ∩ V) := by
  have hp_mul (N : ℕ) : (f ^ (a * N)) p = p := by
    induction N with
    | zero => simp
    | succ N ih => simpa [Nat.mul_succ, pow_add, Homeomorph.mul_apply, hp] using ih
  have cancel_left (n : ℕ) (x : X) : (f ^ (-(n : ℤ))) ((f ^ n) x) = x := by
    rw [← zpow_natCast f n, ← Homeomorph.mul_apply, ← zpow_add]
    simp
  have cancel_right (n : ℕ) (x : X) : (f ^ n) ((f ^ (-(n : ℤ))) x) = x := by
    rw [← zpow_natCast f n, ← Homeomorph.mul_apply, ← zpow_add]
    simp
  have hp_neg (N : ℕ) : (f ^ (-(a * N : ℕ) : ℤ)) p = p := by
    simpa [hp_mul N] using cancel_left (a * N) p
  obtain ⟨ρU, hρU, hballU⟩ := Metric.isOpen_iff.mp hU xs hxs
  obtain ⟨ρV, hρV, hballV⟩ := Metric.isOpen_iff.mp hV xu hxu
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp
    (hstable.eventually_lt_const (show (0 : ℝ) < ε₀ / 3 by positivity))
  obtain ⟨Nu, hNu⟩ := eventually_atTop.mp
    (hunstable.eventually_lt_const (show (0 : ℝ) < ε₀ / 3 by positivity))
  have hgeo : Tendsto (fun N : ℕ ↦ γ * κ ^ N) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ₀.le hκ₁).const_mul γ
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp
    (hgeo.eventually_lt_const (lt_min hρU hρV))
  intro L
  let N := max (max Ns Nu) (max Nb (L + 1))
  have hNsN : Ns ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNuN : Nu ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNbN : Nb ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hLN : L < N := lt_of_lt_of_le (Nat.lt_succ_self L)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  let m := a * (N + 1)
  let l := m + s - r
  have haN : N ≤ a * N := by simpa using Nat.mul_le_mul_right N ha
  have hmN : N ≤ m := by dsimp [m]; nlinarith
  have hrm : r ≤ m + s := by dsimp [m]; nlinarith
  have hlr : l + r = m + s := Nat.sub_add_cancel hrm
  have hm_eq : m = a * N + a := Nat.mul_succ a N
  have hlN : N ≤ l := by omega
  have hphase : (f ^ (l + r)) p = (f ^ s) p := by
    rw [hlr, Nat.add_comm m s, pow_add, Homeomorph.mul_apply]
    dsimp [m]
    rw [hp_mul (N + 1)]
  have hphase_neg : (f ^ ((s : ℤ) - (m : ℤ))) p = (f ^ s) p := by
    rw [sub_eq_add_neg, zpow_add, Homeomorph.mul_apply]
    have hmneg : (f ^ (-(m : ℤ))) p = p := hp_neg (N + 1)
    rw [hmneg, zpow_natCast]
  let b := (f ^ l) xs
  let c := (f ^ (-(m : ℤ))) xu
  have hb : dist b ((f ^ s) p) < ε₀ / 3 := by
    simpa only [b, hphase] using hNs l (le_trans hNsN hlN)
  have hc : dist c ((f ^ s) p) < ε₀ / 3 := by
    simpa only [c, hphase_neg] using hNu m (le_trans hNuN hmN)
  have hbc : dist b c ≤ ε₀ := by
    have := dist_triangle b ((f ^ s) p) c
    rw [dist_comm ((f ^ s) p) c] at this
    linarith
  obtain ⟨z, hzb, hzc, hz⟩ := hbracket b c hbc
  let y := (f ^ (-(l : ℤ))) z
  have hy : dist y xs ≤ γ * κ ^ N := by
    have h := (hz l).2
    simp only [b, cancel_left] at h
    calc
      dist y xs ≤ κ ^ l * dist z b := h
      _ ≤ κ ^ l * γ := mul_le_mul_of_nonneg_left hzb (pow_nonneg hκ₀.le _)
      _ ≤ κ ^ N * γ := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hκ₀.le hκ₁.le hlN) hγ.le
      _ = γ * κ ^ N := mul_comm _ _
  have hzV : dist ((f ^ m) z) xu ≤ γ * κ ^ N := by
    have h := (hz m).1
    simp only [c, cancel_right] at h
    calc
      dist ((f ^ m) z) xu ≤ κ ^ m * dist z c := h
      _ ≤ κ ^ m * γ := mul_le_mul_of_nonneg_left hzc (pow_nonneg hκ₀.le _)
      _ ≤ κ ^ N * γ := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hκ₀.le hκ₁.le hmN) hγ.le
      _ = γ * κ ^ N := mul_comm _ _
  have hyU : y ∈ U := hballU (by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hy (lt_of_lt_of_le (hNb N hNbN) (min_le_left _ _)))
  have hzVV : (f ^ m) z ∈ V := hballV (by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hzV (lt_of_lt_of_le (hNb N hNbN) (min_le_right _ _)))
  have hreturn : (f ^ (l + m)) y = (f ^ m) z := by
    rw [Nat.add_comm l m, pow_add, Homeomorph.mul_apply]
    simp only [y, cancel_right]
  refine ⟨l + m, by omega, (f ^ m) z, ?_, hzVV⟩
  exact ⟨y, hyU, hreturn⟩

end HolomorphicAnosov
