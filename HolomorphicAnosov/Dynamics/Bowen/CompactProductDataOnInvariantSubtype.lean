import HolomorphicAnosov.Dynamics.Bowen.CompactProductDataOfFactOne
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

namespace HolomorphicAnosov.BowenBasicSetCoding

open Set Filter
open scoped Topology _root_.Topology

/-- Restrict a literal ambient Fact 1 bracket to the invariant subtype, keeping
the original forward and inverse iterates and the actual inherited topology.
The total bracket uses an arbitrary value only outside the close-pair domain;
all laws and continuity are proved on that domain. Source: Bowen (1970),
Fact 1 pp. 726–727 and Lemmas 5–8 pp. 727–729. -/
theorem compact_product_data_on_invariant_subtype
    {M : Type*} [MetricSpace M] (F : M ≃ₜ M) (Λ : Set M)
    (hΛ : ∀ x, x ∈ Λ ↔ F x ∈ Λ) (hcompact : IsCompact Λ) (hne : Λ.Nonempty)
    (γ lam ε : ℝ) (hγ : 0 < γ) (hlam : 0 < lam) (hlam1 : lam < 1) (hε : 0 < ε)
    (hs : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ,
      (∀ n : ℕ, dist ((F : M → M)^[n] y) ((F : M → M)^[n] x) ≤ γ) →
      (∀ n : ℕ, dist ((F : M → M)^[n] z) ((F : M → M)^[n] x) ≤ γ) →
      ∀ n : ℕ, dist ((F : M → M)^[n] y) ((F : M → M)^[n] z) ≤ lam ^ n * dist y z)
    (hu : ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ,
      (∀ n : ℕ, dist ((F.symm : M → M)^[n] y) ((F.symm : M → M)^[n] x) ≤ γ) →
      (∀ n : ℕ, dist ((F.symm : M → M)^[n] z) ((F.symm : M → M)^[n] x) ≤ γ) →
      ∀ n : ℕ, dist ((F.symm : M → M)^[n] y) ((F.symm : M → M)^[n] z) ≤
        lam ^ n * dist y z)
    (b : {p : M × M // p.1 ∈ Λ ∧ p.2 ∈ Λ ∧ dist p.1 p.2 ≤ ε} → Λ)
    (hb : Continuous b)
    (hbmem : ∀ p,
      (∀ n : ℕ, dist ((F : M → M)^[n] (b p).val) ((F : M → M)^[n] p.val.1) ≤ γ) ∧
      (∀ n : ℕ, dist ((F.symm : M → M)^[n] (b p).val)
        ((F.symm : M → M)^[n] p.val.2) ≤ γ))
    (hbuniq : ∀ p, ∀ z : Λ,
      (∀ n : ℕ, dist ((F : M → M)^[n] z.val) ((F : M → M)^[n] p.val.1) ≤ γ) →
      (∀ n : ℕ, dist ((F.symm : M → M)^[n] z.val)
        ((F.symm : M → M)^[n] p.val.2) ≤ γ) → z = b p) :
    letI : CompactSpace Λ := isCompact_iff_compactSpace.mp hcompact
    Nonempty (Dynamics.Bowen.CompactLocalProductData (F.subtype hΛ) γ lam) := by
  classical
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty Λ := hne.to_subtype
  let f := F.subtype hΛ
  have hiter : ∀ (n : ℕ) (x : Λ), ((f : Λ → Λ)^[n] x).val =
      ((F : M → M)^[n]) x.val := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg F ih
  have hinv : ∀ (n : ℕ) (x : Λ), ((f.symm : Λ → Λ)^[n] x).val =
      ((F.symm : M → M)^[n]) x.val := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg F.symm ih
  let c : Λ → Λ → Λ := fun x y ↦
    if h : dist x y ≤ ε then b ⟨(x.val, y.val), x.property, y.property, h⟩ else x
  have hc : ∀ x y (h : dist x y ≤ ε),
      c x y = b ⟨(x.val, y.val), x.property, y.property, h⟩ := by
    intro x y h
    simp only [c, dite_eq_left h]
  have hcmem : ∀ x y, dist x y ≤ ε →
      c x y ∈ Dynamics.relativeClosedStablePlaque f γ x ∩
        Dynamics.relativeClosedUnstablePlaque f γ y := by
    intro x y hxy
    rw [hc x y hxy]
    refine ⟨fun n ↦ ?_, fun n ↦ ?_⟩
    · change dist (((f : Λ → Λ)^[n] _).val) (((f : Λ → Λ)^[n] _).val) ≤ γ
      simpa only [hiter] using (hbmem ⟨(x.val, y.val), x.property, y.property, hxy⟩).1 n
    · change dist (((f.symm : Λ → Λ)^[n] _).val) (((f.symm : Λ → Λ)^[n] _).val) ≤ γ
      simpa only [hinv] using (hbmem ⟨(x.val, y.val), x.property, y.property, hxy⟩).2 n
  have hcuniq : ∀ x y z, dist x y ≤ ε →
      z ∈ Dynamics.relativeClosedStablePlaque f γ x ∩
        Dynamics.relativeClosedUnstablePlaque f γ y → z = c x y := by
    intro x y z hxy hz
    rw [hc x y hxy]
    apply hbuniq
    · intro n
      simpa only [Subtype.dist_eq, hiter] using hz.1 n
    · intro n
      simpa only [Subtype.dist_eq, hinv] using hz.2 n
  have hccont : ContinuousOn (fun p : Λ × Λ ↦ c p.1 p.2)
      {p | dist p.1 p.2 ≤ ε} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let lift : {p : Λ × Λ // dist p.1 p.2 ≤ ε} →
        {p : M × M // p.1 ∈ Λ ∧ p.2 ∈ Λ ∧ dist p.1 p.2 ≤ ε} :=
      fun p ↦ ⟨(p.val.1.val, p.val.2.val), p.val.1.property, p.val.2.property, p.property⟩
    have hlift : Continuous lift := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
    exact (hb.comp hlift).congr (fun p ↦ (hc p.val.1 p.val.2 p.property).symm)
  apply compact_product_data_of_factOne f γ lam ε hγ hlam hlam1 hε c hcmem hcuniq hccont
  · intro x y z hy hz n
    have hy' : ∀ n : ℕ, dist ((F : M → M)^[n] y.val) ((F : M → M)^[n] x.val) ≤ γ :=
      fun n ↦ by simpa only [Subtype.dist_eq, hiter] using hy n
    have hz' : ∀ n : ℕ, dist ((F : M → M)^[n] z.val) ((F : M → M)^[n] x.val) ≤ γ :=
      fun n ↦ by simpa only [Subtype.dist_eq, hiter] using hz n
    simpa only [Subtype.dist_eq, hiter] using
      hs x.val x.property y.val y.property z.val z.property hy' hz' n
  · intro x y z hy hz n
    have hy' : ∀ n : ℕ, dist ((F.symm : M → M)^[n] y.val)
        ((F.symm : M → M)^[n] x.val) ≤ γ :=
      fun n ↦ by simpa only [Subtype.dist_eq, hinv] using hy n
    have hz' : ∀ n : ℕ, dist ((F.symm : M → M)^[n] z.val)
        ((F.symm : M → M)^[n] x.val) ≤ γ :=
      fun n ↦ by simpa only [Subtype.dist_eq, hinv] using hz n
    simpa only [Subtype.dist_eq, hinv] using
      hu x.val x.property y.val y.property z.val z.property hy' hz' n


end HolomorphicAnosov.BowenBasicSetCoding
