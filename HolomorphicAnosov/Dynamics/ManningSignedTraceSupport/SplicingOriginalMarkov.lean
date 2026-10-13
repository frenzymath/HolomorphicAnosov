import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StableSpliceImageEq
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.UnstableSpliceImageEq
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ProperRectanglesInteriorLabel

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section
open BowenBasicSetCoding

/-- Agent-expanded SAME-partition transfer of the actual coding splice output. At x in int Ri and Fx in int Rj, any code over x has zero label i and next label j by properness and disjoint interiors. For y in the original stable slice of x in Ri, splice past(y) with future(x). The stable splice identity gives image y, so its next label j proves Fy in Rj; the stable orbit inequalities shift by one. For y in the original unstable slice of Fx in Rj, splice past(Fx) with future(y). The unstable splice identity gives image y, and the negative-one label i proves F inverse y in Ri. The inverse orbit inequalities shift by one as well. All eps+b≤e estimates concern the ORIGINAL metric; neither coding adapted metric nor its radius is substituted. Rectangles and coding are retained unchanged. -/
theorem splicing_original_markov {X : Type*} [MetricSpace X]
 (F : X ≃ₜ X) {N : ℕ} (R : Fin N → Set X)
 (B : Fin N → Fin N → Prop) (coding : CodeSpace B → X)
 {e b ε : ℝ} (hb : 0 ≤ b) (hsum : ε+b ≤ e)
 (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x=y)
 (hproper : ∀ i, R i = closure (interior (R i)))
 (hdisjoint : ∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j)))
 (horbit : ∀ a : CodeSpace B, ∀ j : ℤ, (F^j) (coding a) ∈ R (a.val j))
 (hlabel : ∀ x i, x ∈ R i → ∃ a : CodeSpace B, coding a=x ∧ a.val 0=i)
 (hsplice : ∀ a d : CodeSpace B, a.val 0=d.val 0 → ∃ c : CodeSpace B,
  (∀ j : ℤ, j ≤ 0 → c.val j=a.val j) ∧
  (∀ j : ℤ, 0 ≤ j → c.val j=d.val j) ∧
  (∀ j : ℤ, 0 ≤ j → dist ((F^j) (coding c)) ((F^j) (coding d))<ε) ∧
  (∀ j : ℤ, j ≤ 0 → dist ((F^j) (coding c)) ((F^j) (coding a))<ε)) :
 HasMarkovInclusions F dist b R := by
 intro i j x hxi hfxj
 constructor
 · rintro _ ⟨y,⟨hyi,hys⟩,rfl⟩
   obtain ⟨a,ha,hai⟩ := hlabel y i hyi
   obtain ⟨d,hd,hdi⟩ := hlabel x i (interior_subset hxi)
   obtain ⟨c,hpast,hfuture,hs,hu⟩ := hsplice a d (hai.trans hdi.symm)
   have hcy : coding c=y := stable_splice_image_eq F hb hsum hexp hys
    (by simpa only [hd] using hs) (by simpa only [ha] using hu)
   have hdj : d.val 1=j := proper_rectangles_interior_label R hproper hdisjoint hfxj (by
    simpa only [hd,zpow_one] using horbit d 1)
   refine ⟨?_,?_⟩
   · have h := horbit c 1
     simpa only [hcy,zpow_one,hfuture 1 (by omega),hdj] using h
   · intro n
     have h := hys (n+1)
     simpa only [pow_succ,Homeomorph.mul_apply] using h
 · intro y hy
   obtain ⟨a,ha,haj⟩ := hlabel (F x) j (interior_subset hfxj)
   obtain ⟨d,hd,hdj⟩ := hlabel y j hy.1
   obtain ⟨c,hpast,hfuture,hs,hu⟩ := hsplice a d (haj.trans hdj.symm)
   have hcy : coding c=y := unstable_splice_image_eq F hb hsum hexp hy.2
    (by simpa only [hd] using hs) (by simpa only [ha] using hu)
   have hai : a.val (-1)=i := proper_rectangles_interior_label R hproper hdisjoint hxi (by
    simpa only [ha,zpow_neg_one,Homeomorph.inv_apply,Homeomorph.symm_apply_apply] using horbit a (-1))
   refine ⟨F.symm y,⟨?_,?_⟩,F.apply_symm_apply y⟩
   · have h := horbit c (-1)
     simpa only [hcy,zpow_neg_one,Homeomorph.inv_apply,hpast (-1) (by omega),hai] using h
   · intro n
     have h := hy.2 (n+1)
     have he : -(↑n : ℤ)+(-1) = -((n+1 : ℕ):ℤ) := by omega
     have hleft : (F ^ (-(n : ℤ))) (F.symm y) = (F ^ (-((n+1 : ℕ):ℤ))) y := by
       rw [← Homeomorph.inv_apply, ← zpow_neg_one, ← Homeomorph.mul_apply, ← zpow_add,he]
     have hright : (F ^ (-((n+1 : ℕ):ℤ))) (F x) = (F ^ (-(n : ℤ))) x := by
       change (F ^ (-((n+1 : ℕ):ℤ))) ((F ^ (1 : ℤ)) x) = (F ^ (-(n : ℤ))) x
       rw [← Homeomorph.mul_apply, ← zpow_add]
       congr 2
       omega
     rw [hleft]
     rw [hright] at h
     exact h


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
