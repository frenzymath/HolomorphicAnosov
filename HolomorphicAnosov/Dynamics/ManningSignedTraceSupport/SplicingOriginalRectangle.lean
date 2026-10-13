import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalPlaqueIntersectionUnique

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section
open BowenBasicSetCoding

/-- For the SAME returned coding family, choose a code over y carrying the given zero label and a code over x with that label. Splice past(y) with future(x). The provider's ORIGINAL epsilon bounds give closed b-plaque membership when epsilon≤b, and the zero-coordinate itinerary puts the splice image in the SAME rectangle. The preceding expansive uniqueness proves the literal IsRectangle clause. This is an agent-expanded application of the provider's actual splicing output, not a claim that arbitrary compatible same-radius plaques coincide. -/
theorem splicing_original_rectangle {X : Type*} [MetricSpace X]
 (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X)
 (B : Fin N → Fin N → Prop) (coding : CodeSpace B → X)
 {e b ε : ℝ} (hεb : ε ≤ b) (hb : 2*b ≤ e)
 (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x=y)
 (hshape : ∀ i, (R i).Nonempty ∧ IsCompact (R i) ∧ R i = closure (interior (R i)))
 (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F^j) (coding a) ∈ R (a.val j))
 (hlabel : ∀ x i, x ∈ R i → ∃ a : CodeSpace B, coding a=x ∧ a.val 0=i)
 (hsplice : ∀ a b : CodeSpace B, a.val 0=b.val 0 → ∃ c : CodeSpace B,
  (∀ j : ℤ, j ≤ 0 → c.val j=a.val j) ∧
  (∀ j : ℤ, 0 ≤ j → c.val j=b.val j) ∧
  (∀ j : ℤ, 0 ≤ j → dist ((F^j) (coding c)) ((F^j) (coding b))<ε) ∧
  (∀ j : ℤ, j ≤ 0 → dist ((F^j) (coding c)) ((F^j) (coding a))<ε)) :
 ∀ i, IsRectangle F dist b (R i) := by
 intro i
 refine ⟨(hshape i).1,(hshape i).2.1,(hshape i).2.2,?_⟩
 intro x hx y hy
 obtain ⟨a,ha,hai⟩ := hlabel y i hy
 obtain ⟨d,hd,hdi⟩ := hlabel x i hx
 obtain ⟨c,hpast,hfuture,hs,hu⟩ := hsplice a d (hai.trans hdi.symm)
 have hcR : coding c ∈ R i := by
  have h := horbit c 0
  simpa [hfuture 0 le_rfl,hdi] using h
 have hc : coding c ∈ localStable F dist b x ∧ coding c ∈ localUnstable F dist b y := by
  constructor
  · intro n
    have h := (hs (n:ℤ) (by omega)).le.trans hεb
    simpa [hd,zpow_natCast] using h
  · intro n
    have h := (hu (-(n:ℤ)) (by omega)).le.trans hεb
    simpa [ha] using h
 refine ⟨coding c,hcR,?_⟩
 intro w
 constructor
 · exact fun hw ↦ original_plaque_intersection_unique F hb hexp hc hw
 · intro hw; simpa [hw] using hc


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
