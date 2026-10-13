import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque
import Mathlib.Tactic.Linarith

/-!
# Local agreement of closed orbit plaques

An extraction of `BowenRegularClosedPreparation.plaque_local_agreement` from
`RegularClosedProduct`, using the existing public closed-plaque definition.
The hypotheses and conclusion are preserved. The proof below expands the
original calls to plaque monotonicity, contraction, self-membership and the
triangle inequality, so no private declarations are imported.

Source context: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Lemma 8 p.729 and Lemma 10 p.730. The quantitative carrier comparison is an
agent-written expansion, not a separately stated source theorem.
DAG node: `dynamics.bowen_plaque_local_agreement_g15`.
-/

namespace HolomorphicAnosov.Dynamics.Bowen

open Set HolomorphicAnosov.Bowen.RectangleSlicesPreparation

/-- Contracting closed plaques centered at two nearby points have identical
carriers in a ball about one center. The radius condition is non-strict;
membership in the comparison ball is strict. No compactness is needed.

Proof: contraction and λⁿ≤1 bound orbit distances by initial distances.
For t in the plaque at q, the triangle inequality through q bounds its
distance from the orbit of d by η+δ≤γ. Conversely, t and q in the plaque
at d contract towards one another, so their orbit distance is at most
dist(t,q)<η≤γ. The last inequality follows from δ≥0, which itself follows
from q's time-zero membership bound. -/
theorem plaqueLocalAgreement {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {lam γ δ η : ℝ} (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hc : ∀ a y z n, y ∈ stablePlaque f γ a → z ∈ stablePlaque f γ a →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hγ : 0 ≤ γ) (hδ : δ ≤ γ) (hη : η + δ ≤ γ) {q d : X}
    (hqd : q ∈ stablePlaque f δ d) :
    ∀ t, dist t q < η → (t ∈ stablePlaque f γ q ↔ t ∈ stablePlaque f γ d) := by
  have hqdγ : q ∈ stablePlaque f γ d := fun n ↦ (hqd n).trans hδ
  have hqd₀ : dist q d ≤ δ := by simpa using hqd 0
  have hδnonneg : 0 ≤ δ := dist_nonneg.trans hqd₀
  intro t ht
  constructor
  · intro htq n
    have hqt := hc q t q n htq (fun _ ↦ by simpa using hγ)
    have hqd' := hc d q d n hqdγ (fun _ ↦ by simpa using hγ)
    have hpow : lam ^ n ≤ 1 := pow_le_one₀ hlam.1 hlam.2
    have htbound : dist ((f ^ n) t) ((f ^ n) q) ≤ dist t q :=
      hqt.trans (by simpa using mul_le_mul_of_nonneg_right hpow (dist_nonneg : 0 ≤ dist t q))
    have hqbound : dist ((f ^ n) q) ((f ^ n) d) ≤ dist q d :=
      hqd'.trans (by simpa using mul_le_mul_of_nonneg_right hpow (dist_nonneg : 0 ≤ dist q d))
    have htri := dist_triangle ((f ^ n) t) ((f ^ n) q) ((f ^ n) d)
    change dist ((f ^ n) t) ((f ^ n) d) ≤ γ
    linarith
  · intro htd n
    have h := hc d t q n htd hqdγ
    have hpow : lam ^ n ≤ 1 := pow_le_one₀ hlam.1 hlam.2
    have hbound : dist ((f ^ n) t) ((f ^ n) q) ≤ dist t q :=
      h.trans (by simpa using mul_le_mul_of_nonneg_right hpow (dist_nonneg : 0 ≤ dist t q))
    change dist ((f ^ n) t) ((f ^ n) q) ≤ γ
    linarith

end HolomorphicAnosov.Dynamics.Bowen

