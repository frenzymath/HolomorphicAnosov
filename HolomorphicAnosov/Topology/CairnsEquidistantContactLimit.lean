import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed

namespace HolomorphicAnosov
open Set Filter
open scoped _root_.Topology

/-- Equidistant contacts in nested gap intervals cannot keep missing the
limiting open gap. Source: Cairns (1951), Lemma 4.1, p.865. Choose a convergent
subsequence of contacts in the compact parameter interval. Its limit lies
between the limiting endpoints. If every contact misses their open interval,
the limit is an endpoint. Passing the equidistance equation to the limit then
identifies the two endpoint images, contradicting injectivity. -/
theorem equidistant_contacts_cannot_avoid_limit_gap
    {E : Type*} [MetricSpace E] (σ : unitInterval → E)
    (hσ : Continuous σ) (hinj : Function.Injective σ)
    (l u w : ℕ → unitInterval) (a b : unitInterval) (hab : a < b)
    (hl : Tendsto l atTop (nhds a)) (hu : Tendsto u atTop (nhds b))
    (hbetween : ∀ n, l n ≤ w n ∧ w n ≤ u n)
    (hequidistant : ∀ n, dist (σ (w n)) (σ (l n)) = dist (σ (w n)) (σ (u n)))
    (havoid : ∀ n, w n ≤ a ∨ b ≤ w n) : False := by
  obtain ⟨c,k,hk,hw⟩ := CompactSpace.tendsto_subseq w
  have hlk := hl.comp hk.tendsto_atTop
  have huk := hu.comp hk.tendsto_atTop
  have hac : a ≤ c := le_of_tendsto_of_tendsto' hlk hw (fun n ↦ (hbetween (k n)).1)
  have hcb : c ≤ b := le_of_tendsto_of_tendsto' hw huk (fun n ↦ (hbetween (k n)).2)
  have hc : c ∈ Iic a ∪ Ici b :=
    (isClosed_Iic.union isClosed_Ici).mem_of_tendsto hw
      (Eventually.of_forall (fun n ↦ havoid (k n)))
  have heq : dist (σ c) (σ a) = dist (σ c) (σ b) := by
    apply tendsto_nhds_unique ((hσ.tendsto c).comp hw |>.dist ((hσ.tendsto a).comp hlk))
    exact (((hσ.tendsto c).comp hw).dist ((hσ.tendsto b).comp huk)).congr
      (fun n ↦ (hequidistant (k n)).symm)
  rcases hc with hca | hbc
  · have hca' : c = a := le_antisymm hca hac
    rw [hca', dist_self] at heq
    exact (ne_of_lt hab) (hinj (dist_eq_zero.mp heq.symm))
  · have hcb' : c = b := le_antisymm hcb hbc
    rw [hcb', dist_self] at heq
    exact (ne_of_lt hab) (hinj (dist_eq_zero.mp heq)).symm

/-- Successive gap endpoints converge to the same parameter when each
refinement retains an equidistant interior contact. Source: Cairns Lemma 4.1.
The left endpoints increase and the right endpoints decrease, hence converge
to their supremum and infimum. Every new contact is outside the next gap and
therefore outside the limiting open interval. The preceding compactness
argument rules out distinct limiting endpoints. -/
theorem nested_equidistant_gap_endpoints_converge
    {E : Type*} [MetricSpace E] (σ : unitInterval → E)
    (hσ : Continuous σ) (hinj : Function.Injective σ)
    (l u w : ℕ → unitInterval) (hlmono : Monotone l) (humono : Antitone u)
    (hbetween : ∀ n, l n ≤ w n ∧ w n ≤ u n)
    (hequidistant : ∀ n, dist (σ (w n)) (σ (l n)) = dist (σ (w n)) (σ (u n)))
    (hretain : ∀ n, w n ≤ l (n + 1) ∨ u (n + 1) ≤ w n) :
    ∃ t : unitInterval, Tendsto l atTop (nhds t) ∧ Tendsto u atTop (nhds t) := by
  let a : unitInterval := ⨆ n, l n
  let b : unitInterval := ⨅ n, u n
  have hl : Tendsto l atTop (nhds a) := tendsto_atTop_iSup hlmono
  have hu : Tendsto u atTop (nhds b) := tendsto_atTop_iInf humono
  have hlu (n m : ℕ) : l n ≤ u m := by
    rcases le_total n m with hnm | hmn
    · exact (hlmono hnm).trans ((hbetween m).1.trans (hbetween m).2)
    · exact ((hbetween n).1.trans (hbetween n).2).trans (humono hmn)
  have hab : a ≤ b := iSup_le (fun n ↦ le_iInf (hlu n))
  have heq : a = b := by
    by_contra hne
    apply equidistant_contacts_cannot_avoid_limit_gap σ hσ hinj l u w a b
      (lt_of_le_of_ne hab hne) hl hu hbetween hequidistant
    intro n
    rcases hretain n with hn | hn
    · exact Or.inl (hn.trans (le_iSup l (n + 1)))
    · exact Or.inr ((iInf_le u (n + 1)).trans hn)
  exact ⟨a,hl,heq ▸ hu⟩

/-- Closed increasing contact sets on an embedded interval become dense
when every complementary gap gains an equidistant interior contact at the
next stage. Source: Cairns Lemma 4.1, p.865. Around an omitted parameter take
the greatest left and least right retained contacts. They are monotone in
opposite directions. Each new contact is outside the next such gap, so the
endpoint convergence lemma identifies their limits with the omitted
parameter, putting it in the closure of the retained contacts after all. -/
theorem dense_of_equidistant_gap_refinement
    {E : Type*} [MetricSpace E] (σ : unitInterval → E)
    (hσ : Continuous σ) (hinj : Function.Injective σ)
    (T : ℕ → Set unitInterval) (hclosed : ∀ n, IsClosed (T n))
    (hmono : Monotone T) (hzero : ∀ n, 0 ∈ T n) (hone : ∀ n, 1 ∈ T n)
    (hrefine : ∀ n (l u : unitInterval), l ∈ T n → u ∈ T n → l < u →
      (∀ z : unitInterval, l < z → z < u → z ∉ T n) →
      ∃ w ∈ T (n + 1), l < w ∧ w < u ∧
        dist (σ w) (σ l) = dist (σ w) (σ u)) : Dense (⋃ n, T n) := by
  classical
  intro x
  by_cases hx : x ∈ ⋃ n, T n
  · exact subset_closure hx
  have hxnot (n : ℕ) : x ∉ T n := fun hn ↦ hx (mem_iUnion.mpr ⟨n,hn⟩)
  have hleft (n : ℕ) : ∃ l : unitInterval, l ∈ T n ∧ l ≤ x ∧
      ∀ z ∈ T n, z ≤ x → z ≤ l := by
    obtain ⟨l,hl,hm⟩ := ((hclosed n).inter isClosed_Iic).isCompact.exists_isGreatest
      (show (T n ∩ Iic x).Nonempty from ⟨0,hzero n,by exact x.property.1⟩)
    exact ⟨l,hl.1,hl.2,fun z hz hzx ↦ hm ⟨hz,hzx⟩⟩
  have hright (n : ℕ) : ∃ u : unitInterval, u ∈ T n ∧ x ≤ u ∧
      ∀ z ∈ T n, x ≤ z → u ≤ z := by
    obtain ⟨u,hu,hm⟩ := ((hclosed n).inter isClosed_Ici).isCompact.exists_isLeast
      (show (T n ∩ Ici x).Nonempty from ⟨1,hone n,by exact x.property.2⟩)
    exact ⟨u,hu.1,hu.2,fun z hz hxz ↦ hm ⟨hz,hxz⟩⟩
  choose l hl hlx hmax using hleft
  choose u hu hxu hmin using hright
  have hlmono : Monotone l := fun n m hnm ↦ hmax m _ (hmono hnm (hl n)) (hlx n)
  have humono : Antitone u := fun n m hnm ↦ hmin m _ (hmono hnm (hu n)) (hxu n)
  have hinterval (n : ℕ) (z : unitInterval) (hz : z ∈ T n) :
      z ≤ l n ∨ u n ≤ z := by
    rcases le_total z x with hzx | hxz
    · exact Or.inl (hmax n z hz hzx)
    · exact Or.inr (hmin n z hz hxz)
  have hlu (n : ℕ) : l n < u n := by
    have hlne : l n ≠ x := fun he ↦ hxnot n (he ▸ hl n)
    exact (lt_of_le_of_ne (hlx n) hlne).trans_le (hxu n)
  have hw (n : ℕ) : ∃ w ∈ T (n + 1), l n < w ∧ w < u n ∧
      dist (σ w) (σ (l n)) = dist (σ w) (σ (u n)) := by
    apply hrefine n (l n) (u n) (hl n) (hu n) (hlu n)
    intro z hlz hzu hz
    exact (hinterval n z hz).elim (not_le_of_gt hlz) (not_le_of_gt hzu)
  choose w hwT hlw hwu heq using hw
  obtain ⟨t,hlt,hut⟩ := nested_equidistant_gap_endpoints_converge σ hσ hinj
    l u w hlmono humono (fun n ↦ ⟨(hlw n).le,(hwu n).le⟩) heq
    (fun n ↦ hinterval (n + 1) (w n) (hwT n))
  have htx : t = x := le_antisymm
    (le_of_tendsto_of_tendsto' hlt tendsto_const_nhds hlx)
    (le_of_tendsto_of_tendsto' tendsto_const_nhds hut hxu)
  subst t
  exact isClosed_closure.mem_of_tendsto hlt (Eventually.of_forall
    (fun n ↦ subset_closure (mem_iUnion.mpr ⟨n,hl n⟩)))

/-- Points on the perpendicular bisector of a complex chord are equidistant
from its endpoints. This is the metric input in Cairns's first-contact density
argument; the signed ray parameter may have either orientation. -/
theorem complex_perpendicular_bisector_equidistant (p q : ℂ) (t : ℝ) :
    dist ((p + q) / 2 + t • (Complex.I * (q - p))) p =
      dist ((p + q) / 2 + t • (Complex.I * (q - p))) q := by
  rw [dist_eq_norm, dist_eq_norm]
  have hs : ‖(p + q) / 2 + t • (Complex.I * (q - p)) - p‖ ^ 2 =
      ‖(p + q) / 2 + t • (Complex.I * (q - p)) - q‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.smul_re, Complex.smul_im,
      Complex.I_mul_re, Complex.I_mul_im]
    ring
  nlinarith [norm_nonneg ((p + q) / 2 + t • (Complex.I * (q - p)) - p),
    norm_nonneg ((p + q) / 2 + t • (Complex.I * (q - p)) - q)]

end HolomorphicAnosov


