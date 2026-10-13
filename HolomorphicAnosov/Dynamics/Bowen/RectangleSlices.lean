import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueSlice
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueBoundary
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.bracketImage
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque_closed
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque_closed
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stablePlaque_self
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque_self
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueSlice_closed
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueSlice_inter
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.stable_slice_small
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstable_slice_small
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.homeomorph_pow_apply
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.narrow_intersection_unique
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.regular_closed_open_restriction
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.regular_closed_prod_left
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.regular_closed_prod_right
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.regular_slices_of_product_chart
import HolomorphicAnosov.Dynamics.Bowen.ProductChart
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic

/-!
# Bowen rectangle slices

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Lemma 9, printed pp. 729--730.  The proof follows Bowen's argument: closed
plaques give compact slices, the rectangle identity comes from the bracket
relations, and the product chart transfers regular-closedness to both factors.
The boundary identity is obtained by applying the product chart at points in
both plaque interiors.  The theorem is stated with the original Fact 1,
modulus, and scale hypotheses, including the frontier cases.
-/

namespace HolomorphicAnosov

open Set
open Bowen.RectangleSlicesPreparation

/-- Bowen's regular-closed plaque slices for a compact rectangle (Lemma 9,
pp. 729--730). Every hypothesis appearing in Bowen's Fact 1, the positive
bracket moduli, and the five auxiliary scales is retained explicitly. The
slice closure/interior assertions are relative to the full native γ-plaques,
so they also apply when `q` lies on the ambient frontier of `A`.

Proof source and correspondence: (1) each γ-plaque is an intersection of
closed orbit-distance conditions, hence its intersection with compact `A` is
compact; the contraction estimate and `diam A ≤ α₃` put the slices in the
α₃-plaques. (2) Bracket closure gives `[C(q),D(q)] ⊆ A`; for `z ∈ A`, the
points `[z,q]` and `[q,z]` lie in the corresponding slices, and bracket
uniqueness gives `z = [[z,q],[q,z]]`, proving `A = [C(q),D(q)]`. (3) Bowen's
local product chart identifies suitable open plaque neighborhoods with their
product. Transporting `A = closure (interior A)` through this chart gives
`C(q)×D(q) = closure (interior C(q)×interior D(q))`; nonemptiness of both
factors then yields the two relative closure/interior assertions. (4) An
ambient interior point has neighborhoods in both slices. Conversely, plaque
interior points in both factors have an open bracket neighborhood contained in
`A`; therefore `frontier A` is exactly the union of the two plaque boundaries.
These are the source steps of Bowen's Lemma 9; the local product chart is the
standard consequence of Fact 1 and the displayed scale margins, while compactness
uses the given compact metric hypothesis. -/
theorem bowen_fact1_rectangle_slices_g6
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : Homeomorph X X) (lam γ ε : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hγ : 0 < γ) (hε : 0 < ε)
    (bracket : X → X → X)
    (hstable : ∀ {x y z : X}, y ∈ stablePlaque f γ x → z ∈ stablePlaque f γ x →
      ∀ n : ℕ, dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hunstable : ∀ {x y z : X}, y ∈ unstablePlaque f γ x →
      z ∈ unstablePlaque f γ x → ∀ n : ℕ,
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ {x y : X}, dist x y ≤ ε →
      bracket x y ∈ stablePlaque f γ x ∩ unstablePlaque f γ y)
    (hbracket_unique : ∀ {x y z : X}, dist x y ≤ ε →
      z ∈ stablePlaque f γ x ∩ unstablePlaque f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (εmod : ℝ → ℝ) (hεmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ)
    (hmod : ∀ {x y : X} {δ : ℝ}, 0 < δ → δ ≤ γ →
      dist x y ≤ εmod δ → bracket x y ∈ stablePlaque f δ x ∩ unstablePlaque f δ y)
    (α : ℕ → ℝ) (hα0 : α 0 = γ)
    (hα : ∀ n, n ≤ 3 → 0 < α (n + 1) ∧ α (n + 1) < α n ∧
      α (n + 1) < (1 / 3 : ℝ) * min (α n / 3) (εmod (α n / 3)))
    (hiterate : ∀ n, n ≤ 3 → ∀ {x y : X}, dist x y ≤ α (n + 1) →
      dist (f x) (f y) < α n ∧ dist (f.symm x) (f.symm y) < α n)
    (A : Set X) (hAnonempty : A.Nonempty) (hAcompact : IsCompact A)
    (hAclosed : ∀ {c d : X}, c ∈ A → d ∈ A → bracket c d ∈ A)
    (hAdiam : Metric.diam A ≤ α 3) (hAregular : A = closure (interior A))
    (C D : X → Set X)
    (hC : ∀ q ∈ A, C q = A ∩ unstablePlaque f γ q)
    (hD : ∀ q ∈ A, D q = A ∩ stablePlaque f γ q) :
    ∀ q ∈ A,
      ((C q).Nonempty ∧ (D q).Nonempty) ∧
      (IsCompact (C q) ∧ IsCompact (D q)) ∧
      (C q ⊆ unstablePlaque f (α 3) q ∧ D q ⊆ stablePlaque f (α 3) q) ∧
      IsClosed (plaqueSlice (unstablePlaque f γ q) (C q)) ∧
      IsClosed (plaqueSlice (stablePlaque f γ q) (D q)) ∧
      plaqueSlice (unstablePlaque f γ q) (C q) =
        closure (interior (plaqueSlice (unstablePlaque f γ q) (C q))) ∧
      plaqueSlice (stablePlaque f γ q) (D q) =
        closure (interior (plaqueSlice (stablePlaque f γ q) (D q))) ∧
      A = bracketImage bracket (C q) (D q) ∧
      (frontier A =
        {x | x ∈ A ∧ x ∈ plaqueBoundary (unstablePlaque f γ x) (C x)} ∪
        {x | x ∈ A ∧ x ∈ plaqueBoundary (stablePlaque f γ x) (D x)}) := by
  have _ := hAnonempty
  have hγ₀ := hγ.le
  have hα1 := hα 0 (by omega)
  have hα2 := hα 1 (by omega)
  have hα3 := hα 2 (by omega)
  have hα4 := hα 3 (by omega)
  have hαpos : ∀ i : Fin 5, 0 < α i := by
    intro i
    fin_cases i
    · exact hα0.symm ▸ hγ
    · exact hα1.1
    · exact hα2.1
    · exact hα3.1
    · exact hα4.1
  have hchart := Bowen.bowen_fact1_product_chart_g6 f lam γ ε hlam hlam1 hγ hε
    (fun i : Fin 5 ↦ α i) εmod hεmod hα0 hαpos
    (fun i ↦ (hα i (by omega)).2.2)
    (fun i a b hab ↦ hiterate i (by omega) hab) bracket
    (fun x y z n hy hz ↦ by
      change (∀ k, dist ((f : X → X)^[k] y) ((f : X → X)^[k] x) ≤ γ) at hy
      change (∀ k, dist ((f : X → X)^[k] z) ((f : X → X)^[k] x) ≤ γ) at hz
      simpa only [homeomorph_pow_apply] using hstable
        (by simpa only [stablePlaque, mem_ofPred_eq, homeomorph_pow_apply] using hy)
        (by simpa only [stablePlaque, mem_ofPred_eq, homeomorph_pow_apply] using hz) n)
    (fun x y z n hy hz ↦ by
      change (∀ k, dist ((f.symm : X → X)^[k] y) ((f.symm : X → X)^[k] x) ≤ γ) at hy
      change (∀ k, dist ((f.symm : X → X)^[k] z) ((f.symm : X → X)^[k] x) ≤ γ) at hz
      simpa only [homeomorph_pow_apply] using hunstable
        (by simpa only [unstablePlaque, mem_ofPred_eq, homeomorph_pow_apply] using hy)
        (by simpa only [unstablePlaque, mem_ofPred_eq, homeomorph_pow_apply] using hz) n)
    (fun a b hab ↦ by
      refine ⟨bracket a b, ?_, ?_⟩
      · change (∀ k, dist ((f : X → X)^[k] (bracket a b)) ((f : X → X)^[k] a) ≤ γ) ∧
          (∀ k, dist ((f.symm : X → X)^[k] (bracket a b)) ((f.symm : X → X)^[k] b) ≤ γ)
        simpa only [stablePlaque, unstablePlaque, mem_inter_iff, mem_ofPred_eq, homeomorph_pow_apply] using hbracket_mem hab
      · intro z hz
        change (∀ k, dist ((f : X → X)^[k] z) ((f : X → X)^[k] a) ≤ γ) ∧
          (∀ k, dist ((f.symm : X → X)^[k] z) ((f.symm : X → X)^[k] b) ≤ γ) at hz
        exact hbracket_unique hab
          (by simpa only [stablePlaque, unstablePlaque, mem_inter_iff, mem_ofPred_eq, homeomorph_pow_apply] using hz))
    (fun a b hab ↦ by
      change (∀ k, dist ((f : X → X)^[k] (bracket a b)) ((f : X → X)^[k] a) ≤ γ) ∧
        (∀ k, dist ((f.symm : X → X)^[k] (bracket a b)) ((f.symm : X → X)^[k] b) ≤ γ)
      simpa only [stablePlaque, unstablePlaque, mem_inter_iff, mem_ofPred_eq, homeomorph_pow_apply] using hbracket_mem hab)
    hbracket_cont
    (fun δ hδ hδγ a b hab ↦ by
      change (∀ k, dist ((f : X → X)^[k] (bracket a b)) ((f : X → X)^[k] a) ≤ δ) ∧
        (∀ k, dist ((f.symm : X → X)^[k] (bracket a b)) ((f.symm : X → X)^[k] b) ≤ δ)
      simpa only [stablePlaque, unstablePlaque, mem_inter_iff, mem_ofPred_eq, homeomorph_pow_apply] using hmod hδ hδγ hab)
  have hsEq (r : ℝ) (x : X) :
      {y | ∀ n, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ r} =
        stablePlaque f r x := by
    ext y
    simp only [stablePlaque, mem_ofPred_eq, homeomorph_pow_apply]
  have huEq (r : ℝ) (x : X) :
      {y | ∀ n, dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] x) ≤ r} =
        unstablePlaque f r x := by
    ext y
    simp only [unstablePlaque, mem_ofPred_eq, homeomorph_pow_apply]
  have hprod (x : X) (U V : Set X)
      (hU : U ⊆ unstablePlaque f (α 2) x) (hV : V ⊆ stablePlaque f (α 2) x)
      (hUo : IsOpen (plaqueSlice (unstablePlaque f γ x) U))
      (hVo : IsOpen (plaqueSlice (stablePlaque f γ x) V)) :
      let UV := bracketImage bracket U V
      IsOpen UV ∧ ∃ h :
        ({u : unstablePlaque f γ x // (u : X) ∈ U} ×
          {v : stablePlaque f γ x // (v : X) ∈ V}) ≃ₜ UV,
        (∀ p, (h p : X) = bracket p.1 p.2) ∧
        (∀ z : UV, ((h.symm z).1 : X) = bracket (z : X) x ∧
          ((h.symm z).2 : X) = bracket x (z : X)) := by
    let P (T S : Set X) : Prop :=
      IsOpen {u : T | (u : X) ∈ U} → IsOpen {v : S | (v : X) ∈ V} →
      IsOpen (bracketImage bracket U V) ∧ ∃ h :
        ({u : T // (u : X) ∈ U} × {v : S // (v : X) ∈ V}) ≃ₜ
          bracketImage bracket U V,
        (∀ p, (h p : X) = bracket p.1 p.2) ∧
        (∀ z : bracketImage bracket U V, ((h.symm z).1 : X) = bracket (z : X) x ∧
          ((h.symm z).2 : X) = bracket x (z : X))
    have hc : P
        {y | ∀ n, dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] x) ≤ γ}
        {y | ∀ n, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ γ} := by
      apply hchart.2 x U V
      · intro y hy
        change ∀ n, dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] x) ≤ α 2
        simpa only [unstablePlaque, mem_ofPred_eq, homeomorph_pow_apply] using hU hy
      · intro y hy
        change ∀ n, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ α 2
        simpa only [stablePlaque, mem_ofPred_eq, homeomorph_pow_apply] using hV hy
    rw [huEq γ x, hsEq γ x] at hc
    exact hc hUo hVo
  have hα2γ : α 2 < γ := by
    have := hα1.2.1
    have := hα2.2.1
    rw [hα0] at *
    linarith
  have hδpos : 0 < α 2 / 3 := by linarith [hα2.1]
  have hδγ : α 2 / 3 ≤ γ := by linarith
  have hδsum : α 2 / 3 + α 2 / 3 ≤ γ := by linarith
  have hmodsmall : α 3 ≤ εmod (α 2 / 3) := by
    have h := hα3.2.2.trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    have he := hεmod (α 2 / 3) hδpos hδγ
    linarith
  have hdist {x y : X} (hx : x ∈ A) (hy : y ∈ A) : dist x y ≤ α 3 :=
    (Metric.dist_le_diam_of_mem hAcompact.isBounded hx hy).trans hAdiam
  have hm {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
      bracket x y ∈ stablePlaque f (α 2 / 3) x ∩ unstablePlaque f (α 2 / 3) y :=
    hmod hδpos hδγ ((hdist hx hy).trans hmodsmall)
  have hbb (x : X) : bracket x x = x :=
    (hbracket_unique (by simpa using hε.le)
      ⟨stablePlaque_self f hγ.le x, unstablePlaque_self f hγ.le x⟩).symm
  have hrect (x : X) (hx : x ∈ A) : A = bracketImage bracket (C x) (D x) := by
    apply Subset.antisymm
    · intro z hz
      have hc := hm hz hx
      have hd := hm hx hz
      have hca := hAclosed hz hx
      have hda := hAclosed hx hz
      have he := hm hca hda
      refine ⟨bracket z x, ?_, bracket x z, ?_, ?_⟩
      · rw [hC x hx]
        exact ⟨hca, fun n ↦ (hc.2 n).trans hδγ⟩
      · rw [hD x hx]
        exact ⟨hda, fun n ↦ (hd.1 n).trans hδγ⟩
      · exact narrow_intersection_unique f γ ε _ _ _ _ hγ hε hδsum hδsum
          bracket hbracket_unique (bracket z x) (bracket x z)
          (bracket (bracket z x) (bracket x z)) z he.1
          (fun n ↦ by simpa only [dist_comm] using hc.1 n) he.2
          (fun n ↦ by simpa only [dist_comm] using hd.2 n)
    · rintro z ⟨c, hc, d, hd, rfl⟩
      exact hAclosed ((hC x hx ▸ hc).1) ((hD x hx ▸ hd).1)
  intro q hq
  have hCq := hC q hq
  have hDq := hD q hq
  have hCnon : (C q).Nonempty := ⟨q, hCq.symm ▸ ⟨hq, unstablePlaque_self f hγ₀ q⟩⟩
  have hDnon : (D q).Nonempty := ⟨q, hDq.symm ▸ ⟨hq, stablePlaque_self f hγ₀ q⟩⟩
  have hCcomp : IsCompact (C q) := hCq.symm ▸
    hAcompact.inter_right (unstablePlaque_closed f γ q)
  have hDcomp : IsCompact (D q) := hDq.symm ▸
    hAcompact.inter_right (stablePlaque_closed f γ q)
  have hCsmall : C q ⊆ unstablePlaque f (α 3) q := by
    rw [hCq]
    exact unstable_slice_small f lam γ (α 3) hlam.le hlam1.le hγ₀
      hunstable hAcompact hAdiam hq
  have hDsmall : D q ⊆ stablePlaque f (α 3) q := by
    rw [hDq]
    exact stable_slice_small f lam γ (α 3) hlam.le hlam1.le hγ₀
      hstable hAcompact hAdiam hq
  have hCsclosed : IsClosed (plaqueSlice (unstablePlaque f γ q) (C q)) :=
    plaqueSlice_closed hCcomp.isClosed _
  have hDsclosed : IsClosed (plaqueSlice (stablePlaque f γ q) (D q)) :=
    plaqueSlice_closed hDcomp.isClosed _
  let r := (α 3 + α 2) / 2
  have hr3 : α 3 < r := by dsimp [r]; linarith [hα3.2.1]
  have hr2 : r < α 2 := by dsimp [r]; linarith [hα3.2.1]
  let U := Metric.ball q r ∩ unstablePlaque f γ q
  let V := Metric.ball q r ∩ stablePlaque f γ q
  have hUopen : IsOpen (plaqueSlice (unstablePlaque f γ q) U) := by
    dsimp [U]
    rw [plaqueSlice_inter]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hVopen : IsOpen (plaqueSlice (stablePlaque f γ q) V) := by
    dsimp [V]
    rw [plaqueSlice_inter]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hU2 : U ⊆ unstablePlaque f (α 2) q := by
    intro z hz n
    exact (hunstable hz.2 (unstablePlaque_self f hγ.le q) n).trans
      ((mul_le_mul_of_nonneg_right (pow_le_one₀ hlam.le hlam1.le) dist_nonneg).trans
        (by simpa using (Metric.mem_ball.mp hz.1).le.trans hr2.le))
  have hV2 : V ⊆ stablePlaque f (α 2) q := by
    intro z hz n
    exact (hstable hz.2 (stablePlaque_self f hγ.le q) n).trans
      ((mul_le_mul_of_nonneg_right (pow_le_one₀ hlam.le hlam1.le) dist_nonneg).trans
        (by simpa using (Metric.mem_ball.mp hz.1).le.trans hr2.le))
  have hCU : C q ⊆ U := by
    intro z hz
    refine ⟨Metric.mem_ball.mpr ?_, (hCq ▸ hz).2⟩
    exact (show dist z q ≤ α 3 by simpa using hCsmall hz 0).trans_lt hr3
  have hDV : D q ⊆ V := by
    intro z hz
    refine ⟨Metric.mem_ball.mpr ?_, (hDq ▸ hz).2⟩
    exact (show dist z q ≤ α 3 by simpa using hDsmall hz 0).trans_lt hr3
  obtain ⟨hWopen, h, hforward, hinverse⟩ := hprod q U V hU2 hV2 hUopen hVopen
  have hpre : h ⁻¹' (Subtype.val ⁻¹' A) =
      (Subtype.val ⁻¹' plaqueSlice (unstablePlaque f γ q) (C q)) ×ˢ
      (Subtype.val ⁻¹' plaqueSlice (stablePlaque f γ q) (D q)) := by
    ext p
    constructor
    · intro hp
      have hi := hinverse (h p)
      simp only [h.symm_apply_apply] at hi
      constructor
      · change p.1.val.val ∈ C q
        rw [hCq]
        exact ⟨hi.1 ▸ hAclosed hp hq, p.1.val.property⟩
      · change p.2.val.val ∈ D q
        rw [hDq]
        exact ⟨hi.2 ▸ hAclosed hq hp, p.2.val.property⟩
    · intro hp
      change (h p : X) ∈ A
      rw [hforward]
      exact hAclosed ((hCq ▸ hp.1).1) ((hDq ▸ hp.2).1)
  have hCsnon : (plaqueSlice (unstablePlaque f γ q) (C q)).Nonempty :=
    ⟨⟨q, unstablePlaque_self f hγ.le q⟩, hCq.symm ▸
      ⟨hq, unstablePlaque_self f hγ.le q⟩⟩
  have hDsnon : (plaqueSlice (stablePlaque f γ q) (D q)).Nonempty :=
    ⟨⟨q, stablePlaque_self f hγ.le q⟩, hDq.symm ▸
      ⟨hq, stablePlaque_self f hγ.le q⟩⟩
  have hregular := regular_slices_of_product_chart A (bracketImage bracket U V)
    (plaqueSlice (unstablePlaque f γ q) U) (plaqueSlice (unstablePlaque f γ q) (C q))
    (plaqueSlice (stablePlaque f γ q) V) (plaqueSlice (stablePlaque f γ q) (D q))
    hWopen hUopen hVopen hCsclosed hDsclosed
    (fun _ hz ↦ hCU hz) (fun _ hz ↦ hDV hz) hCsnon hDsnon h hAregular hpre
  refine ⟨⟨hCnon, hDnon⟩, ⟨hCcomp, hDcomp⟩, ⟨hCsmall, hDsmall⟩,
    hCsclosed, hDsclosed, ?_, ?_, ?_, ?_⟩
  · exact hregular.1
  · exact hregular.2
  · exact hrect q hq
  · have hint (x : X) (hx : x ∈ A) :
        x ∈ interior A ↔
        (⟨x, unstablePlaque_self f hγ.le x⟩ : unstablePlaque f γ x) ∈
          interior (plaqueSlice (unstablePlaque f γ x) (C x)) ∧
        (⟨x, stablePlaque_self f hγ.le x⟩ : stablePlaque f γ x) ∈
          interior (plaqueSlice (stablePlaque f γ x) (D x)) := by
      constructor
      · intro hxi
        constructor
        · rw [hC x hx, plaqueSlice_inter]
          exact preimage_interior_subset_interior_preimage continuous_subtype_val hxi
        · rw [hD x hx, plaqueSlice_inter]
          exact preimage_interior_subset_interior_preimage continuous_subtype_val hxi
      · intro hi
        let IU := interior (plaqueSlice (unstablePlaque f γ x) (C x))
        let IV := interior (plaqueSlice (stablePlaque f γ x) (D x))
        let Ux := Subtype.val '' IU
        let Vx := Subtype.val '' IV
        have hUC : Ux ⊆ C x := by
          rintro z ⟨u, hu, rfl⟩
          exact interior_subset (s := plaqueSlice (unstablePlaque f γ x) (C x)) hu
        have hVD : Vx ⊆ D x := by
          rintro z ⟨v, hv, rfl⟩
          exact interior_subset (s := plaqueSlice (stablePlaque f γ x) (D x)) hv
        have hU2x : Ux ⊆ unstablePlaque f (α 2) x := by
          intro z hz n
          have hs := unstable_slice_small f lam γ (α 3) hlam.le hlam1.le hγ.le
            hunstable hAcompact hAdiam hx (hC x hx ▸ hUC hz) n
          exact hs.trans hα3.2.1.le
        have hV2x : Vx ⊆ stablePlaque f (α 2) x := by
          intro z hz n
          have hs := stable_slice_small f lam γ (α 3) hlam.le hlam1.le hγ.le
            hstable hAcompact hAdiam hx (hD x hx ▸ hVD hz) n
          exact hs.trans hα3.2.1.le
        have hUox : IsOpen (plaqueSlice (unstablePlaque f γ x) Ux) := by
          change IsOpen (Subtype.val ⁻¹' (Subtype.val '' IU))
          rw [preimage_image_eq _ Subtype.val_injective]
          exact isOpen_interior
        have hVox : IsOpen (plaqueSlice (stablePlaque f γ x) Vx) := by
          change IsOpen (Subtype.val ⁻¹' (Subtype.val '' IV))
          rw [preimage_image_eq _ Subtype.val_injective]
          exact isOpen_interior
        have hWo := (hprod x Ux Vx hU2x hV2x hUox hVox).1
        have hxW : x ∈ bracketImage bracket Ux Vx :=
          ⟨x, ⟨⟨x, unstablePlaque_self f hγ.le x⟩, hi.1, rfl⟩,
            x, ⟨⟨x, stablePlaque_self f hγ.le x⟩, hi.2, rfl⟩, hbb x⟩
        have hWA : bracketImage bracket Ux Vx ⊆ A := by
          rintro z ⟨u, hu, v, hv, rfl⟩
          exact hAclosed ((hC x hx ▸ hUC hu).1) ((hD x hx ▸ hVD hv).1)
        exact mem_interior.mpr ⟨_, hWA, hWo, hxW⟩
    have hbu (x : X) (hx : x ∈ A) :
        x ∈ plaqueBoundary (unstablePlaque f γ x) (C x) ↔
        (⟨x, unstablePlaque_self f hγ.le x⟩ : unstablePlaque f γ x) ∉
          interior (plaqueSlice (unstablePlaque f γ x) (C x)) := by
      have hc : IsClosed (plaqueSlice (unstablePlaque f γ x) (C x)) := by
        rw [hC x hx, plaqueSlice_inter]
        exact plaqueSlice_closed hAcompact.isClosed _
      rw [plaqueBoundary, frontier, hc.closure_eq]
      simp only [mem_image, mem_sdiff, plaqueSlice, mem_preimage]
      constructor
      · rintro ⟨u, ⟨hu, hni⟩, he⟩
        have he' : u = ⟨x, unstablePlaque_self f hγ.le x⟩ := Subtype.ext he
        rwa [he'] at hni
      · intro hni
        exact ⟨⟨x, unstablePlaque_self f hγ.le x⟩,
          ⟨hC x hx |>.symm ▸ ⟨hx, unstablePlaque_self f hγ.le x⟩, hni⟩, rfl⟩
    have hbs (x : X) (hx : x ∈ A) :
        x ∈ plaqueBoundary (stablePlaque f γ x) (D x) ↔
        (⟨x, stablePlaque_self f hγ.le x⟩ : stablePlaque f γ x) ∉
          interior (plaqueSlice (stablePlaque f γ x) (D x)) := by
      have hc : IsClosed (plaqueSlice (stablePlaque f γ x) (D x)) := by
        rw [hD x hx, plaqueSlice_inter]
        exact plaqueSlice_closed hAcompact.isClosed _
      rw [plaqueBoundary, frontier, hc.closure_eq]
      simp only [mem_image, mem_sdiff, plaqueSlice, mem_preimage]
      constructor
      · rintro ⟨u, ⟨hu, hni⟩, he⟩
        have he' : u = ⟨x, stablePlaque_self f hγ.le x⟩ := Subtype.ext he
        rwa [he'] at hni
      · intro hni
        exact ⟨⟨x, stablePlaque_self f hγ.le x⟩,
          ⟨hD x hx |>.symm ▸ ⟨hx, stablePlaque_self f hγ.le x⟩, hni⟩, rfl⟩
    ext x
    rw [frontier, hAcompact.isClosed.closure_eq]
    simp only [mem_sdiff, mem_union, mem_ofPred_eq]
    by_cases hx : x ∈ A
    · simp only [hx, true_and, hbu x hx, hbs x hx, hint x hx, not_and_or]
    · simp [hx]


end HolomorphicAnosov
