import HolomorphicAnosov.Dynamics.Bowen.FiniteUnstableSliceCover
import HolomorphicAnosov.Dynamics.Bowen.PlaqueRebase
import HolomorphicAnosov.Dynamics.Bowen.RegularClosedProduct
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import HolomorphicAnosov.Dynamics.Bowen.StablePlaqueInteriorIntegerChart

/-!
# Bowen's rectangles enlarged for one common iterate

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Fact 1 pp.726-727, Lemmas 14-18 pp.732-735, Lemma 22 pp.737-738.
DAG node: `topo.manning_bowen_iterate_g3_enlarged_rectangles_remaining_gap_g20`.
The public helper definitions below are literal set operations for the downstream atom construction,
not supplied geometric data.
-/

open Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Bowen

/-- Closed forward orbit plaque, Bowen Fact 1, p.727. -/
def ws {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (r : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f ^ n) y) ((f ^ n) x) ≤ r}

/-- Closed backward orbit plaque, Bowen Fact 1, p.727. -/
def wu {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (r : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f.symm ^ n) y) ((f.symm ^ n) x) ≤ r}

/-- Bracket image of two sets, Bowen Lemma 10, p.730. -/
def bi {X : Type*} (b : X → X → X) (C D : Set X) : Set X :=
  {z | ∃ c ∈ C, ∃ d ∈ D, b c d = z}

/-- Interior in the full plaque subtype, Bowen Lemmas 9-10, pp.729-730. -/
def ri {X : Type*} [TopologicalSpace X] (S C : Set X) : Set X :=
  (Subtype.val : S → X) '' interior ((Subtype.val : S → X) ⁻¹' C)

/-- Closure in the full plaque subtype, Bowen Lemma 15, p.734. -/
def rc {X : Type*} [TopologicalSpace X] (S C : Set X) : Set X :=
  (Subtype.val : S → X) '' closure ((Subtype.val : S → X) ⁻¹' C)

/-- Set-valued plaque neighborhoods mean unions, Bowen Lemma 2, p.727. -/
def pu {X : Type*} (P : ℝ → X → Set X) (r : ℝ) (C : Set X) : Set X :=
  {z | ∃ c ∈ C, z ∈ P r c}

/-- A proper rectangle at the stated scale, Bowen pp.728-730. -/
def proper {X : Type*} [MetricSpace X] (b : X → X → X) (r : ℝ)
    (A : Set X) : Prop :=
  A.Nonempty ∧ IsCompact A ∧ (∀ x ∈ A, ∀ y ∈ A, b x y ∈ A) ∧
    Metric.diam A ≤ r ∧ A = closure (interior A)

/-- The finite-union recursion in Bowen p.733; swapping both factors gives its dual. -/
def stage {X I : Type*} [TopologicalSpace X] (h : X ≃ₜ X) (b : X → X → X)
    (C₀ : I → Set X) (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X) : ℕ → I → Set X
  | 0 => C₀
  | n + 1 => fun i ↦ ⋃ j, h.symm '' bi b (stage h b C₀ k T y n (T i j)) {h (y i j)}

private theorem ws_symm {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (r : ℝ) (x : X) :
    ws f.symm r x = wu f r x := rfl

private theorem wu_symm {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (r : ℝ) (x : X) :
    wu f.symm r x = ws f r x := by simp only [wu, ws, Homeomorph.symm_symm]

private theorem bi_flip {X : Type*} (b : X → X → X) (C D : Set X) :
    bi (fun x y ↦ b y x) D C = bi b C D := by
  ext z
  simp only [bi, mem_ofPred_eq]
  aesop

private theorem proper_flip {X : Type*} [MetricSpace X] (b : X → X → X)
    (r : ℝ) (A : Set X) : proper (fun x y ↦ b y x) r A ↔ proper b r A := by
  unfold proper
  constructor
  · rintro ⟨hn, hc, hb, hd, hr⟩
    exact ⟨hn, hc, fun x hx y hy ↦ hb y hy x hx, hd, hr⟩
  · rintro ⟨hn, hc, hb, hd, hr⟩
    exact ⟨hn, hc, fun x hx y hy ↦ hb y hy x hx, hd, hr⟩

/-- Bowen Lemma 11(a). Small orbit-pair guards transport the bracket through a
finite iterate. Comparing the two candidate brackets in both orbit directions
reduces to diagonal intersection uniqueness. -/
private theorem finiteBracketCovariance
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ ε δ r : ℝ)
    (b : X → X → X) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (_hδ : 0 ≤ δ)
    (hδγ : 2 * δ ≤ γ)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hb : ∀ x y, dist x y ≤ r → b x y ∈ ws f δ x ∩ wu f δ y)
    {x y : X} (m : ℕ) (hpair : ∀ k ≤ m, dist ((f ^ k) x) ((f ^ k) y) ≤ r) :
    (f ^ m) (b x y) = b ((f ^ m) x) ((f ^ m) y) := by
  have hdiag (x z : X) (hs : z ∈ ws f γ x) (ht : z ∈ wu f γ x) : z = x := by
    exact (hu x x z (by simpa using hε) hs ht).trans
      (hu x x x (by simpa using hε)
        (fun n ↦ by simpa using hγ) (fun n ↦ by simpa using hγ)).symm
  have hone (u v : X) (h0 : dist u v ≤ r) (h1 : dist (f u) (f v) ≤ r) :
      f (b u v) = b (f u) (f v) := by
    have hsource := hb u v h0
    have htarget := hb (f u) (f v) h1
    apply hdiag (b (f u) (f v)) (f (b u v))
    · intro n
      have hs := hsource.1 (n + 1)
      have ht := htarget.1 n
      rw [pow_succ, Homeomorph.mul_apply] at hs
      exact (dist_triangle _ ((f ^ n) (f u)) _).trans
        ((add_le_add hs (by simpa only [dist_comm] using ht)).trans (by linarith [hδγ]))
    · intro n
      cases n with
      | zero =>
        have hs := hsource.1 1
        have ht := htarget.1 0
        change dist (f (b u v)) (b (f u) (f v)) ≤ γ
        have ht' : dist (b (f u) (f v)) (f u) ≤ δ := by simpa using ht
        exact (dist_triangle _ (f u) _).trans
          ((add_le_add hs (by simpa [pow_zero, Homeomorph.one_apply, dist_comm] using ht)).trans (by linarith [hδγ]))
      | succ n =>
        have hs := hsource.2 n
        have ht := htarget.2 (n + 1)
        simp only [pow_succ, Homeomorph.mul_apply, Homeomorph.symm_apply_apply] at ht ⊢
        exact (dist_triangle _ ((f.symm ^ n) v) _).trans
          ((add_le_add hs (by simpa only [dist_comm] using ht)).trans (by linarith [hδγ]))
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Homeomorph.mul_apply, ih (fun k hk ↦ hpair k (by omega))]
    exact hone _ _ (hpair m (by omega)) (by
      simpa only [pow_succ', Homeomorph.mul_apply] using hpair (m + 1) le_rfl)

/-- Guarded absorption for one repeated stable coordinate. -/
private theorem bracket_absorb_right
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ ε δ r : ℝ)
    (b : X → X → X) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (_hδ : 0 ≤ δ)
    (hδγ : 3 * δ ≤ γ)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hb : ∀ x y, dist x y ≤ r → b x y ∈ ws f δ x ∩ wu f δ y)
    (u v z : X) (huz : dist u z ≤ r) (hvz : dist v z ≤ r)
    (houter : dist u (b v z) ≤ r) : b u (b v z) = b u z := by
  have h1 := hb u z huz
  have h2 := hb v z hvz
  have h3 := hb u (b v z) houter
  apply BowenRegularClosedPreparation.diagonal_separation f b hγ hε
    (fun x w hx hs ht ↦ hu x x w hx hs ht)
  · intro n
    exact (dist_triangle _ ((f ^ n) u) _).trans
      ((add_le_add (h3.1 n) (by simpa only [dist_comm] using h1.1 n)).trans
        (by linarith))
  · intro n
    calc
      dist ((f.symm ^ n) (b u (b v z))) ((f.symm ^ n) (b u z)) ≤
          dist ((f.symm ^ n) (b u (b v z))) ((f.symm ^ n) (b v z)) +
          dist ((f.symm ^ n) (b v z)) ((f.symm ^ n) (b u z)) := dist_triangle _ _ _
      _ ≤ δ + (δ + δ) := add_le_add (h3.2 n)
        ((dist_triangle _ ((f.symm ^ n) z) _).trans
          (add_le_add (h2.2 n) (by simpa only [dist_comm] using h1.2 n)))
      _ ≤ γ := by linarith

/-- Bracketing two points in one sufficiently small unstable plaque retains the first. -/
private theorem smallUnstableBracketSelf
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ ε δ r : ℝ) (b : X → X → X)
    (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hbudget : δ + 2 * r ≤ γ)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hb : ∀ u v, dist u v ≤ 2 * r → b u v ∈ ws f δ u ∩ wu f δ v)
    (x u v : X) (hux : u ∈ wu f r x) (hvx : v ∈ wu f r x) : b u v = u := by
  have huv (n : ℕ) : dist ((f.symm ^ n) u) ((f.symm ^ n) v) ≤ 2 * r := by
    exact (dist_triangle _ ((f.symm ^ n) x) _).trans
      ((add_le_add (hux n) (by simpa only [dist_comm] using hvx n)).trans (by linarith))
  have hh := hb u v (huv 0)
  apply BowenRegularClosedPreparation.diagonal_separation f b hγ hε
    (fun a z ha hs ht ↦ hu a a z ha hs ht)
  · exact fun n ↦ (hh.1 n).trans (by linarith)
  · intro n
    exact (dist_triangle _ ((f.symm ^ n) v) _).trans
      ((add_le_add (hh.2 n) (by simpa only [dist_comm] using huv n)).trans hbudget)

/-- Replacing a stable coordinate by a point on its small product slice preserves the slice. -/
private theorem smallSliceAbsorption
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ ε : ℝ)
    (b : X → X → X) (εmod : ℝ → ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → b x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (x s : X) (C : Set X) (hC : C ⊆ wu f (2 * α 5) x)
    (hs : s ∈ ws f (2 * α 5) x) (c : X) (hc : c ∈ C) :
    bi b C {b c s} = bi b C {s} := by
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hag (i : Fin 8) : α i ≤ γ := by simpa only [hα0] using hmono (show 0 ≤ i by omega)
  have hscale (i : Fin 7) : 9 * α i.succ < α i.castSucc := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hsm (i : Fin 7) : 3 * α i.succ < εmod (α i.castSucc / 3) := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hds (u : X) (hu : u ∈ C) : dist u s ≤ 4 * α 5 := by
    have hh := dist_triangle u x s
    have hu0 : dist u x ≤ 2 * α 5 := hC hu 0
    have hs0 : dist s x ≤ 2 * α 5 := hs 0
    rw [dist_comm x s] at hh
    linarith
  have hbs : dist (b c s) s ≤ α 3 / 3 :=
    ((hmod (α 3 / 3) (div_pos (hαpos 3) (by norm_num)) (by linarith [hag 3])).2 c s
      (by have hh := hds c hc; have hh5 := hscale 4; have hh4 := hsm 3
          norm_num at hh5 hh4; linarith [hαpos 5])).2 0
  have heq (u : X) (huC : u ∈ C) : b u (b c s) = b u s := by
    apply bracket_absorb_right f γ ε (α 2 / 3) (α 3) b hγ.le hε.le
      (by linarith [hαpos 2]) (by linarith [hag 2]) hu
      (fun p q hpq ↦ (hmod (α 2 / 3) (div_pos (hαpos 2) (by norm_num))
        (by linarith [hag 2])).2 p q (by
          have hh := hsm 2; norm_num at hh; linarith [hαpos 3]))
    · have hh := hds u huC; have h5 := hscale 4; have h4 := hscale 3
      norm_num at h5 h4; linarith [hαpos 4]
    · have hh := hds c hc; have h5 := hscale 4; have h4 := hscale 3
      norm_num at h5 h4; linarith [hαpos 4]
    · have hh := dist_triangle u s (b c s)
      rw [dist_comm s (b c s)] at hh
      have hh' := hds u huC; have h5 := hscale 4; have h4 := hscale 3
      norm_num at h5 h4; linarith [hαpos 4]
  ext q
  constructor
  · rintro ⟨u, huC, t, ht, rfl⟩
    have ht' : t = b c s := ht
    exact ⟨u, huC, s, rfl, by simpa only [ht'] using (heq u huC).symm⟩
  · rintro ⟨u, huC, t, ht, rfl⟩
    have ht' : t = s := ht
    exact ⟨u, huC, b c s, rfl, by simpa only [ht'] using heq u huC⟩

/-- A finite slice transport identity gives transport at every point of the slice. -/
private theorem transportFromSlices
    {X I : Type*} [MetricSpace X] (f h : X ≃ₜ X) (γ ε : ℝ)
    (b : X → X → X) (εmod : ℝ → ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → b x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (x : I → X) (C D : I → Set X)
    (hC : ∀ i, C i ⊆ wu f (2 * α 5) (x i))
    (hD : ∀ i, D i ⊆ ws f (2 * α 5) (x i))
    (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X)
    (htrans : ∀ i s, s ∈ ws f (2 * α 5) (x i) →
      (∀ j, h (b (y i j) s) ∈ D (T i j)) ∧
      h '' bi b (C i) {s} = ⋃ j, bi b (C (T i j)) {h (b (y i j) s)}) :
    ∀ i z, z ∈ bi b (C i) (ws f (2 * α 5) (x i)) →
      ∃ j, h z ∈ bi b (C j) (D j) ∧
        bi b (C j) {h z} ⊆ h '' bi b (C i) {z} := by
  intro i z hz
  obtain ⟨c, hc, s, hs, rfl⟩ := hz
  have ht := htrans i s hs
  have hm : h (b c s) ∈ ⋃ j, bi b (C (T i j)) {h (b (y i j) s)} := by
    rw [← ht.2]
    exact ⟨b c s, ⟨c, hc, s, rfl, rfl⟩, rfl⟩
  obtain ⟨j, u, huC, t, htmem, he⟩ := mem_iUnion.mp hm
  have hteq : t = h (b (y i j) s) := htmem
  subst t
  refine ⟨T i j, ⟨u, huC, _, ht.1 j, he⟩, ?_⟩
  rw [← he, smallSliceAbsorption f γ ε b εmod hγ hε hu hmod α hα0 hαpos hαdesc
    hαrec (x (T i j)) _ (C (T i j)) (hC _) (hD _ (ht.1 j)) u huC]
  rw [smallSliceAbsorption f γ ε b εmod hγ hε hu hmod α hα0 hαpos hαdesc
    hαrec (x i) s (C i) (hC i) hs c hc, ht.2]
  exact fun q hq ↦ mem_iUnion.mpr ⟨j, hq⟩

/-- Guarded absorption for one repeated unstable coordinate. -/
private theorem bracket_absorb_left
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ ε δ r : ℝ)
    (b : X → X → X) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hδγ : 3 * δ ≤ γ)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hb : ∀ x y, dist x y ≤ r → b x y ∈ ws f δ x ∩ wu f δ y)
    (u v z : X) (huz : dist u z ≤ r) (huv : dist u v ≤ r)
    (houter : dist (b u v) z ≤ r) : b (b u v) z = b u z := by
  exact bracket_absorb_right f.symm γ ε δ r (fun p q ↦ b q p) hγ hε hδ hδγ
    (fun p q w hpq hs ht ↦ hu q p w (by simpa only [dist_comm] using hpq)
      (by simpa only [wu_symm] using ht) hs)
    (fun p q hpq ↦ by
      have hh := hb q p (by simpa only [dist_comm] using hpq)
      exact ⟨hh.2, by simpa only [wu_symm] using hh.1⟩)
    z v u (by simpa only [dist_comm] using huz) (by simpa only [dist_comm] using huv)
    (by simpa only [dist_comm] using houter)

/-- Bowen Lemma 11(b)'s pointwise slice transport under explicit finite-orbit guards. -/
private theorem guardedSliceCovariance
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ ε δ r : ℝ)
    (b : X → X → X) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hδγ : 3 * δ ≤ γ)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hb : ∀ x y, dist x y ≤ r → b x y ∈ ws f δ x ∩ wu f δ y)
    (u v z : X) (m : ℕ) (huz : dist u z ≤ r) (hvz : dist v z ≤ r)
    (hpair : ∀ k ≤ m, dist ((f ^ k) u) ((f ^ k) (b v z)) ≤ r) :
    (f ^ m) (b u z) = b ((f ^ m) u) ((f ^ m) (b v z)) := by
  rw [← bracket_absorb_right f γ ε δ r b hγ hε hδ hδγ hu hb u v z huz hvz
    (hpair 0 (Nat.zero_le _))]
  exact finiteBracketCovariance f γ ε δ r b hγ hε hδ (by linarith) hu hb m hpair

/-- Backward contraction at the endpoint controls every earlier point of a
finite orbit segment. -/
private theorem forward_distance_of_unstable_endpoint
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (lam γ r : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hγ : 0 ≤ γ)
    (hc : ∀ x y z n, y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (u v : X) (m : ℕ) (huv : (f ^ m) u ∈ wu f γ ((f ^ m) v))
    (hd : dist ((f ^ m) u) ((f ^ m) v) ≤ r) :
    ∀ k ≤ m, dist ((f ^ k) u) ((f ^ k) v) ≤ r := by
  intro k hk
  have hshift (x : X) : (f.symm ^ (m - k)) ((f ^ m) x) = (f ^ k) x := by
    have hi : f.symm ^ (m - k) = (f ^ (m - k)).symm := inv_pow _ _
    rw [hi, ← pow_sub_mul_pow f hk, Homeomorph.mul_apply, Homeomorph.symm_apply_apply]
  have hh := hc ((f ^ m) v) ((f ^ m) u) ((f ^ m) v) (m - k) huv
    (fun n ↦ by simpa using hγ)
  rw [hshift u, hshift v] at hh
  exact hh.trans ((mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.1 hlam.2)).trans hd)

/-- Bowen Lemma 11(b) at the actual nested scales: unstable closeness after the
iterate and a small source stable displacement provide all intermediate guards. -/
private theorem scaledSliceCovariance
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (lam γ ε : ℝ)
    (b : X → X → X) (εmod : ℝ → ℝ) (α : Fin 8 → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (_hs : ∀ x y z n, y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (ht : ∀ x y z n, y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hu : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hb : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → b x y ∈ ws f δ x ∩ wu f δ y)
    (x u v z : X) (m : ℕ)
    (hux : u ∈ wu f (2 * α 5) x) (hvx : v ∈ wu f (α 5) x)
    (hzx : z ∈ ws f (2 * α 5) x)
    (htarget : (f ^ m) u ∈ wu f (α 3) ((f ^ m) v)) :
    (f ^ m) (b u z) = b ((f ^ m) u) ((f ^ m) (b v z)) := by
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hag (i : Fin 8) : α i ≤ γ := hα0 ▸ hmono (Fin.zero_le i)
  have hscale (i : Fin 7) : 9 * α i.succ < α i.castSucc ∧
      3 * α i.succ < εmod (α i.castSucc / 3) := by
    constructor
    · have hh := (hαrec i).trans_le
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
      linarith
    · have hh := (hαrec i).trans_le
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
      linarith
  have huz : dist u z ≤ 4 * α 5 := by
    have hu0 := hux 0
    have hz0 := hzx 0
    change dist u x ≤ 2 * α 5 at hu0
    change dist z x ≤ 2 * α 5 at hz0
    have hh := dist_triangle u x z
    rw [dist_comm x z] at hh
    linarith
  have hvz : dist v z ≤ 3 * α 5 := by
    have hv0 := hvx 0
    have hz0 := hzx 0
    change dist v x ≤ α 5 at hv0
    change dist z x ≤ 2 * α 5 at hz0
    have hh := dist_triangle v x z
    rw [dist_comm x z] at hh
    linarith
  have h53 : 9 * α 5 < α 3 := (hscale 4).1.trans_le (hmono (by decide))
  have h32 : 9 * α 3 < α 2 := (hscale 2).1
  have h21 : 9 * α 2 < α 1 := (hscale 1).1
  have he3 : 3 * α 3 < εmod (α 2 / 3) := (hscale 2).2
  have he2 : 3 * α 2 < εmod (α 1 / 3) := (hscale 1).2
  have hp := (hb (α 2 / 3) (div_pos (hαpos 2) (by norm_num))
    (by linarith [hag 2])).2 v z (hvz.trans (by linarith [he3, hαpos 5]))
  have hprefix (k : ℕ) (hk : k ≤ m) : dist ((f ^ k) u) ((f ^ k) v) ≤ α 3 :=
    forward_distance_of_unstable_endpoint f lam γ (α 3) ⟨hlam.1.le, hlam.2.le⟩
      hγ.le ht u v m (fun n ↦ (htarget n).trans (hag 3)) (htarget 0) k hk
  apply guardedSliceCovariance f γ ε (α 1 / 3) (α 2) b hγ.le hε.le
    (by linarith [hαpos 1]) (by linarith [hag 1]) hu
    (fun p q hpq ↦ (hb (α 1 / 3) (div_pos (hαpos 1) (by norm_num))
      (by linarith [hag 1])).2 p q (hpq.trans (by linarith [he2, hαpos 2])))
    u v z m (huz.trans (by linarith [hαpos 5])) (hvz.trans (by linarith [hαpos 5]))
  intro k hk
  have hpbound := hp.1 k
  have htri := dist_triangle ((f ^ k) u) ((f ^ k) v) ((f ^ k) (b v z))
  rw [dist_comm ((f ^ k) v) ((f ^ k) (b v z))] at htri
  linarith [hprefix k hk, hαpos 3]

/-- Backward iterates contract the radius of an unstable plaque. -/
private theorem unstable_pullback_radius
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (lam γ r : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hγ : 0 ≤ γ) (hr : r ≤ γ)
    (hc : ∀ x y z n, y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    {u v : X} (huv : u ∈ wu f r v) (m : ℕ) :
    (f ^ m).symm u ∈ wu f (lam ^ m * r) ((f ^ m).symm v) := by
  intro n
  have hi : f.symm ^ m = (f ^ m).symm := inv_pow _ _
  have hh := hc v u v (n + m) (fun k ↦ (huv k).trans hr)
    (fun k ↦ by simpa using hγ)
  have hpow := pow_le_one₀ hlam.1 hlam.2 (n := n)
  have hd : dist u v ≤ r := huv 0
  have hbound : lam ^ (n + m) * dist u v ≤ lam ^ m * r := by
    rw [pow_add]
    calc
      lam ^ n * lam ^ m * dist u v = lam ^ m * (lam ^ n * dist u v) := by ring
      _ ≤ lam ^ m * dist u v := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left dist_nonneg hpow) (pow_nonneg hlam.1 _)
      _ ≤ lam ^ m * r := mul_le_mul_of_nonneg_left hd (pow_nonneg hlam.1 _)
  simpa only [pow_add, Homeomorph.mul_apply, hi] using hh.trans hbound

/-- The geometric tail bound controls both the iterate contraction and every
partial radius used in Bowen's enlargement. -/
private theorem enlargement_numeric_bounds
    (lam γ a : ℝ) (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ)
    (_ha : 0 < a) (haγ : a < γ / 2) (m : ℕ) (hm : 1 ≤ m)
    (htail : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) :
    0 < lam ^ m ∧ lam ^ m < 1 / 2 ∧ lam ^ m * γ < a ∧
      ∀ n, (∑ j ∈ Finset.range (n + 1), (lam ^ m) ^ j) < 3 / 2 := by
  have hβ0 : 0 < lam ^ m := pow_pos hlam.1 _
  have hβ1 : lam ^ m < 1 := pow_lt_one₀ hlam.1.le hlam.2 (by omega)
  have hsum := hasSum_geometric_of_lt_one hβ0.le hβ1
  have htailSum : HasSum (fun k : ℕ ↦ (lam ^ m) ^ (k + 1))
      (lam ^ m / (1 - lam ^ m)) := by
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using hsum.mul_left (lam ^ m)
  have htailLess := htail.trans_le (min_le_right _ _)
  have htailHalf : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < 1 / 2 :=
    htailLess.trans ((div_lt_iff₀ hγ).mpr (by linarith))
  have hβTail : lam ^ m ≤ ∑' k : ℕ, (lam ^ m) ^ (k + 1) := by
    simpa using htailSum.summable.le_tsum 0 (fun k _ ↦ pow_nonneg hβ0.le _)
  refine ⟨hβ0, hβTail.trans_lt htailHalf,
    (lt_div_iff₀ hγ).mp (hβTail.trans_lt htailLess), ?_⟩
  intro n
  have hfinite := htailSum.summable.sum_le_tsum (Finset.range n)
    (fun k _ ↦ pow_nonneg hβ0.le _)
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  linarith

/-- A receiving cover makes the finite enlargement stages increasing. This is
Bowen Lemma 15's monotonicity argument: pull back the seed cover, then apply
monotonicity of finite unions and bracket images. -/
private theorem pu_unstable_subset
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) {r s : ℝ} {C : Set X} {z : X}
    (hC : C ⊆ wu f r z) (_hr : 0 ≤ r) (_hs : 0 ≤ s) :
    pu (wu f) s C ⊆ wu f (r + s) z := by
  intro q hq
  obtain ⟨c, hc, hq⟩ := hq
  intro n
  have ht := dist_triangle ((f.symm ^ n) q) ((f.symm ^ n) c) ((f.symm ^ n) z)
  rw [dist_comm ((f.symm ^ n) c) ((f.symm ^ n) z)] at ht
  have h1 := hC hc n
  rw [dist_comm ((f.symm ^ n) c) ((f.symm ^ n) z)] at h1
  linarith [h1, hq n]

private theorem pu_stable_subset
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) {r s : ℝ} {C : Set X} {z : X}
    (hC : C ⊆ ws f r z) (_hr : 0 ≤ r) (_hs : 0 ≤ s) :
    pu (ws f) s C ⊆ ws f (r + s) z := by
  intro q hq
  obtain ⟨c, hc, hq⟩ := hq
  intro n
  have ht := dist_triangle ((f ^ n) q) ((f ^ n) c) ((f ^ n) z)
  rw [dist_comm ((f ^ n) c) ((f ^ n) z)] at ht
  have h1 := hC hc n
  rw [dist_comm ((f ^ n) c) ((f ^ n) z)] at h1
  linarith [h1, hq n]

private theorem stage_monotone
    {X I : Type*} [TopologicalSpace X] (h : X ≃ₜ X) (b : X → X → X)
    (C₀ : I → Set X) (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X)
    (hcover : ∀ i, h '' C₀ i ⊆ ⋃ j, bi b (C₀ (T i j)) {h (y i j)}) :
    ∀ i, Monotone (fun n ↦ stage h b C₀ k T y n i) := by
  have hstep : ∀ n i, stage h b C₀ k T y n i ⊆ stage h b C₀ k T y (n + 1) i := by
    intro n
    induction n with
    | zero =>
      intro i v hv
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover i ⟨v, hv, rfl⟩)
      exact mem_iUnion.mpr ⟨j, h v, hj, h.symm_apply_apply v⟩
    | succ n ih =>
      intro i v hv
      obtain ⟨j, p, ⟨c, hc, d, hd, heq⟩, hp⟩ := mem_iUnion.mp hv
      exact mem_iUnion.mpr ⟨j, p, ⟨c, ih (T i j) hc, d, hd, heq⟩, hp⟩
  exact fun i ↦ monotone_nat_of_le_succ (fun n ↦ hstep n i)

private theorem stage_base_radius
    {X I : Type*} [MetricSpace X] (f : X ≃ₜ X) (lam γ r : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hγ : 0 ≤ γ)
    (hc : ∀ x y z n, y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (b : X → X → X) (C₀ : I → Set X) (k : I → ℕ)
    (T : (i : I) → Fin (k i) → I) (y : (i : I) → Fin (k i) → X)
    (x : I → X) (m : ℕ)
    (hseed : ∀ i, C₀ i ⊆ wu f r (x i))
    (hy : ∀ i j, y i j ∈ wu f r (x i))
    (hradius : ∀ n, (∑ j ∈ Finset.range (n + 1), (lam ^ m) ^ j) * r ≤ γ)
    (hslice : ∀ n i j,
      bi b (stage (f ^ m) b C₀ k T y n (T i j)) {(f ^ m) (y i j)} ⊆
        wu f ((∑ t ∈ Finset.range (n + 1), (lam ^ m) ^ t) * r) ((f ^ m) (y i j))) :
    ∀ n i, stage (f ^ m) b C₀ k T y n i ⊆
      wu f ((∑ j ∈ Finset.range (n + 1), (lam ^ m) ^ j) * r) (x i) := by
  intro n i
  cases n with
  | zero => simpa [stage] using hseed i
  | succ n =>
    intro p hp
    obtain ⟨j, q, hq, rfl⟩ := mem_iUnion.mp hp
    have hh := unstable_pullback_radius f lam γ _ hlam hγ (hradius n) hc (hslice n i j hq) m
    have heq : lam ^ m * ((∑ t ∈ Finset.range (n + 1), (lam ^ m) ^ t) * r) + r =
        (∑ t ∈ Finset.range (n + 1 + 1), (lam ^ m) ^ t) * r := by
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [pow_zero, pow_succ, ← Finset.sum_mul]
      ring
    intro t
    have hqdist := hh t
    rw [Homeomorph.symm_apply_apply] at hqdist
    have ht := dist_triangle ((f.symm ^ t) ((f ^ m).symm q))
      ((f.symm ^ t) (y i j)) ((f.symm ^ t) (x i))
    rw [← heq]
    linarith [hy i j t]

/-- The relative closure inside a closed orbit plaque is compact, and contains
any seed already lying in that plaque. -/
private theorem rc_compact_contains
    {X : Type*} [MetricSpace X] [CompactSpace X] (f : X ≃ₜ X)
    (γ : ℝ) (x : X) (B U : Set X) (hB : B ⊆ ws f γ x) (hBU : B ⊆ U) :
    IsCompact (rc (ws f γ x) U) ∧ B ⊆ rc (ws f γ x) U := by
  have hclosed : IsClosed (ws f γ x) := BowenRegularClosedPreparation.isClosed_stable f γ x
  let : CompactSpace (ws f γ x) := isCompact_iff_compactSpace.mp hclosed.isCompact
  refine ⟨isClosed_closure.isCompact.image continuous_subtype_val, ?_⟩
  intro z hz
  exact ⟨⟨z, hB hz⟩, subset_closure (hBU hz), rfl⟩

/-- Closing a union of regular closed factors remains regular closed in the
same full plaque topology. -/
private theorem rc_subset_closed {X : Type*} [TopologicalSpace X]
    (S U K : Set X) (hK : IsClosed K) (hUK : U ⊆ K) : rc S U ⊆ K := by
  rintro q ⟨p, hp, rfl⟩
  exact closure_minimal (preimage_mono hUK) (hK.preimage continuous_subtype_val) hp

private theorem rc_eq_closure {X : Type*} [TopologicalSpace X]
    (S U : Set X) (hS : IsClosed S) (hUS : U ⊆ S) : rc S U = closure U := by
  rw [rc, ← hS.isClosedMap_subtype_val.closure_image_eq_of_continuous continuous_subtype_val]
  rw [image_preimage_eq_of_subset]
  simpa only [Subtype.range_coe] using hUS

private theorem ri_subset {X : Type*} [TopologicalSpace X] (S U : Set X) :
    ri S U ⊆ U := by
  rintro q ⟨p, hp, rfl⟩
  exact (interior_subset hp : p ∈ (Subtype.val : S → X) ⁻¹' U)

private theorem ri_carrier {X : Type*} [TopologicalSpace X] (S U : Set X) :
    ri S U ⊆ S := by
  rintro q ⟨p, hp, rfl⟩
  exact p.property

private theorem regular_image_of_interior_transport
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (h : X ≃ₜ X) (S T C : Set X) (hS : IsClosed S) (hT : IsClosed T)
    (hcompact : IsCompact C) (hreg : C = rc S (ri S C))
    (hinterior : h '' ri S C ⊆ ri T (h '' C)) :
    h '' C = rc T (ri T (h '' C)) := by
  rw [rc_eq_closure T _ hT (ri_carrier _ _)]
  apply Subset.antisymm
  · calc
      h '' C = h '' closure (ri S C) := by
        conv_lhs => rw [hreg]
        rw [rc_eq_closure S _ hS (ri_carrier _ _)]
      _ = closure (h '' ri S C) := h.image_closure _
      _ ⊆ closure (ri T (h '' C)) := closure_mono hinterior
  · exact closure_minimal (ri_subset _ _) (hcompact.image h.continuous).isClosed

private theorem chart_interior_image
    {X : Type*} [TopologicalSpace X] (S T C : Set X) (g : X → X)
    (p : S) (hp : p.val ∈ ri S C)
    (O : Set S) (_hO : IsOpen O) (hpO : p ∈ O)
    (G : O → T) (hG : _root_.Topology.IsOpenEmbedding G)
    (hGeq : ∀ t, (G t).val = g t.val.val) : g p.val ∈ ri T (g '' C) := by
  have hp' : p ∈ interior ((Subtype.val : S → X) ⁻¹' C) := by
    obtain ⟨q, hq, hqp⟩ := hp
    have heq : q = p := Subtype.ext hqp
    exact heq ▸ hq
  let W : Set O := (Subtype.val : O → S) ⁻¹' interior ((Subtype.val : S → X) ⁻¹' C)
  have hW : IsOpen W := isOpen_interior.preimage continuous_subtype_val
  have himage : G '' W ⊆ (Subtype.val : T → X) ⁻¹' (g '' C) := by
    rintro t ⟨v, hv, rfl⟩
    have hc : v.val.val ∈ C :=
      (interior_subset hv : v.val ∈ (Subtype.val : S → X) ⁻¹' C)
    exact ⟨v.val.val, hc, (hGeq v).symm⟩
  have hi : G ⟨p, hpO⟩ ∈ interior ((Subtype.val : T → X) ⁻¹' (g '' C)) :=
    (hG.isOpenMap W hW).subset_interior_iff.mpr himage ⟨⟨p,hpO⟩,hp',rfl⟩
  exact ⟨G ⟨p,hpO⟩, hi, hGeq ⟨p,hpO⟩⟩

private theorem stable_integer_interior_transport
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ lam r : ℝ)
    (hγ : 0 < γ) (hlam : 0 ≤ lam ∧ lam ≤ 1) (hr : r < γ)
    (hc : ∀ a y z n, y ∈ ws f γ a → z ∈ ws f γ a →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (x v : X) (C : Set X) (n : ℤ)
    (hC : C ⊆ ws f r x) (himage : (f ^ n) '' C ⊆ ws f r v) :
    (f ^ n) '' ri (ws f γ x) C ⊆ ri (ws f γ v) ((f ^ n) '' C) := by
  have hplaque (a : X) : Dynamics.relativeClosedStablePlaque f γ a = ws f γ a := by
    ext q
    simp only [Dynamics.relativeClosedStablePlaque, ws,
      BowenRegularClosedPreparation.pow_apply_iterate]
  rintro q ⟨p, hp, rfl⟩
  have hpC := ri_subset _ _ hp
  have hpγ : p ∈ ws f γ x := fun k ↦ (hC hpC k).trans hr.le
  have hpdist : dist p x < γ := (hC hpC 0).trans_lt hr
  let p' : Dynamics.relativeClosedStablePlaque f γ x := ⟨p, by simpa only [hplaque] using hpγ⟩
  have hchart := Dynamics.Bowen.stablePlaqueInteriorIntegerChart f γ lam hγ hlam
    (by
      intro a y z hy hz k
      rw [hplaque] at hy hz
      simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hc a y z k hy hz)
    x p' hpdist n
  obtain ⟨O, hO, hpO, G, hG, hGeq⟩ := hchart
  have hi := chart_interior_image (Dynamics.relativeClosedStablePlaque f γ x)
    (Dynamics.relativeClosedStablePlaque f γ ((f ^ n) p)) C (⇑(f ^ n))
    p' (by simpa only [hplaque] using hp) O hO hpO G hG hGeq
  rw [hplaque] at hi
  have hqsmall : (f ^ n) p ∈ ws f r v := himage ⟨p,hpC,rfl⟩
  have hqγ : (f ^ n) p ∈ ws f γ v := fun k ↦ (hqsmall k).trans hr.le
  have hr0 : 0 ≤ r := (dist_nonneg (x := (f ^ n) p) (y := v)).trans (hqsmall 0)
  let η := (γ - r) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hlocal := BowenRegularClosedPreparation.plaque_local_agreement f hlam hc hγ.le hr.le
    (show η + r ≤ γ by dsimp [η]; linarith) hqsmall
  have hself : (f ^ n) p ∈ ws f γ ((f ^ n) p) := fun _ ↦ by simpa using hγ.le
  exact (BowenRegularClosedPreparation.relativeInterior_local (ws f γ ((f ^ n) p))
    (ws f γ v) ((f ^ n) '' C) ((f ^ n) p) hself hqγ hη hlocal).mp hi

/-- A strict plaque collar transfers interior points across an inverse iterate. -/
private theorem unstableInteriorPullbackSubset
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ lam r : ℝ)
    (hγ : 0 < γ) (hlam : 0 ≤ lam ∧ lam ≤ 1) (hr : r < γ)
    (hc : ∀ a y z n, y ∈ wu f γ a → z ∈ wu f γ a →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (q : X) (C E : Set X) (m : ℕ)
    (hC : C ⊆ wu f r q) (hE : E ⊆ wu f r ((f ^ m) q))
    (hsub : E ⊆ (f ^ m) '' C) :
    (f ^ m).symm '' ri (wu f γ ((f ^ m) q)) E ⊆ ri (wu f γ q) C := by
  have hi : f.symm ^ (m : ℤ) = (f ^ m).symm := by
    rw [zpow_natCast]
    exact inv_pow f m
  have hpre : (f ^ m).symm '' E ⊆ C := by
    rintro z ⟨t, ht, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hsub ht
    simpa using hu
  have hh := stable_integer_interior_transport f.symm γ lam r hγ hlam hr hc
    ((f ^ m) q) q E (m : ℤ) hE (by
      simpa only [ws_symm, hi] using hpre.trans hC)
  have hh' : (f ^ m).symm '' ri (wu f γ ((f ^ m) q)) E ⊆
      ri (wu f γ q) ((f ^ m).symm '' E) := by
    simpa only [ws_symm, hi] using hh
  exact hh'.trans (image_mono (interior_mono (preimage_mono hpre)))

private theorem regular_finite_union
    {X J : Type*} [TopologicalSpace X] [T2Space X] [Finite J]
    (S : Set X) (hS : IsClosed S) (B : J → Set X)
    (hcompact : ∀ j, IsCompact (B j)) (hreg : ∀ j, B j = rc S (ri S (B j))) :
    IsCompact (⋃ j, B j) ∧ (⋃ j, B j) = rc S (ri S (⋃ j, B j)) := by
  have hcomp : IsCompact (⋃ j, B j) := isCompact_iUnion hcompact
  refine ⟨hcomp, ?_⟩
  rw [rc_eq_closure S _ hS (ri_carrier _ _)]
  apply Subset.antisymm
  · apply iUnion_subset
    intro j
    rw [hreg j, rc_eq_closure S _ hS (ri_carrier _ _)]
    apply closure_mono
    exact image_mono (interior_mono (preimage_mono (subset_iUnion B j)))
  · exact closure_minimal (ri_subset _ _) hcomp.isClosed

private theorem unstable_pullback_regular
    {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (γ lam r : ℝ)
    (hγ : 0 < γ) (hlam : 0 ≤ lam ∧ lam ≤ 1) (hr : r < γ)
    (hc : ∀ a y z n, y ∈ wu f γ a → z ∈ wu f γ a →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (x v : X) (C : Set X) (m : ℕ) (hC : C ⊆ wu f r x)
    (himage : (f ^ m).symm '' C ⊆ wu f r v)
    (hcompact : IsCompact C) (hreg : C = rc (wu f γ x) (ri (wu f γ x) C)) :
    (f ^ m).symm '' C = rc (wu f γ v) (ri (wu f γ v) ((f ^ m).symm '' C)) := by
  have hinv : f.symm ^ (m : ℤ) = (f ^ m).symm := by
    rw [zpow_natCast]
    exact inv_pow f m
  apply regular_image_of_interior_transport (f ^ m).symm (wu f γ x) (wu f γ v) C
    (BowenRegularClosedPreparation.isClosed_stable f.symm γ x)
    (BowenRegularClosedPreparation.isClosed_stable f.symm γ v) hcompact hreg
  have hh := stable_integer_interior_transport f.symm γ lam r hγ hlam hr hc x v C (m : ℤ)
    hC (by simpa only [ws_symm, hinv] using himage)
  simpa only [ws_symm, hinv] using hh

private theorem limitFactorProperties
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ r : ℝ) (hr : r ≤ γ) (x : X) (B : ℕ → Set X)
    (hB : ∀ n, B n ⊆ wu f r x)
    (hreg : ∀ n, B n = rc (wu f γ x) (ri (wu f γ x) (B n))) :
    let C := rc (wu f γ x) (⋃ n, B n)
    IsCompact C ∧ B 0 ⊆ C ∧ C ⊆ wu f r x ∧
      C = rc (wu f γ x) (ri (wu f γ x) C) ∧ C = closure (⋃ n, B n) := by
  have hU : (⋃ n, B n) ⊆ wu f r x := iUnion_subset hB
  have hUγ : (⋃ n, B n) ⊆ wu f γ x := fun q hq t ↦ (hU hq t).trans hr
  have hC := rc_compact_contains f.symm γ x (B 0) (⋃ n, B n)
    (fun q hq t ↦ (hB 0 hq t).trans hr) (subset_iUnion B 0)
  refine ⟨hC.1, hC.2,
    rc_subset_closed _ _ _ (BowenRegularClosedPreparation.isClosed_stable f.symm r x) hU,
    ?_, rc_eq_closure _ _ (BowenRegularClosedPreparation.isClosed_stable f.symm γ x) hUγ⟩
  have hpre (n : ℕ) : (Subtype.val : wu f γ x → X) ⁻¹' B n =
      closure (interior ((Subtype.val : wu f γ x → X) ⁻¹' B n)) := by
    have hh := congrArg (fun U : Set X ↦ (Subtype.val : wu f γ x → X) ⁻¹' U) (hreg n)
    simpa only [rc, ri, preimage_image_eq _ Subtype.val_injective] using hh
  have hregular : closure (⋃ n, (Subtype.val : wu f γ x → X) ⁻¹' B n) =
      closure (interior (closure (⋃ n, (Subtype.val : wu f γ x → X) ⁻¹' B n))) := by
    apply Subset.antisymm
    · apply closure_minimal _ isClosed_closure
      apply iUnion_subset
      intro n
      rw [hpre n]
      apply closure_mono
      exact interior_mono ((subset_iUnion
        (fun n ↦ (Subtype.val : wu f γ x → X) ⁻¹' B n) n).trans subset_closure)
    · exact closure_minimal interior_subset isClosed_closure
  simp only [rc, ri, preimage_image_eq _ Subtype.val_injective, preimage_iUnion]
  rw [← hregular]

private theorem image_closure_union
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (B : ℕ → Set X) (C : Set X) (hC : C = closure (⋃ n, B n))
    (hc : IsCompact C) (hg : ContinuousOn g C) :
    g '' C = closure (⋃ n, g '' B n) := by
  have himage : g '' (⋃ n, B n) = ⋃ n, g '' B n := image_iUnion
  apply Subset.antisymm
  · rw [hC] at hg ⊢
    simpa only [himage] using hg.image_closure
  · apply closure_minimal _ (hc.image_of_continuousOn hg).isClosed
    rw [← himage]
    apply image_mono
    rw [hC]
    exact subset_closure

private theorem bi_singleton_image {X : Type*} (b : X → X → X) (C : Set X) (z : X) :
    bi b C {z} = (fun c ↦ b c z) '' C := by
  ext q
  constructor
  · rintro ⟨c, hc, d, hd, he⟩
    have hd : d = z := hd
    exact ⟨c,hc,hd ▸ he⟩
  · rintro ⟨c,hc,rfl⟩; exact ⟨c,hc,z,rfl,rfl⟩

private theorem slice_closure_union
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (b : X → X → X) (B : ℕ → Set X) (C : Set X) (z : X)
    (hC : C = closure (⋃ n, B n)) (hc : IsCompact C)
    (hb : ContinuousOn (fun c ↦ b c z) C) :
    bi b C {z} = closure (⋃ n, bi b (B n) {z}) := by
  simp only [bi_singleton_image]
  exact image_closure_union _ _ _ hC hc hb

private theorem finiteToLimitTransport
    {X J : Type*} [TopologicalSpace X] [Finite J]
    (h : X ≃ₜ X) (B : ℕ → Set X) (E : J → ℕ → Set X)
    (C : Set X) (D : J → Set X)
    (hB : B 0 ⊆ B 1) (hC : C = closure (⋃ n, B n))
    (hD : ∀ j, D j = closure (⋃ n, E j n))
    (hstep : ∀ n, h '' B (n + 1) = ⋃ j, E j n) : h '' C = ⋃ j, D j := by
  have hshift : (⋃ n, B n) = ⋃ n, B (n + 1) := by
    apply Subset.antisymm
    · intro p hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      cases n with
      | zero => exact mem_iUnion.mpr ⟨0, hB hn⟩
      | succ n => exact mem_iUnion.mpr ⟨n, hn⟩
    · exact iUnion_subset (fun n ↦ subset_iUnion B (n + 1))
  rw [hC, hshift, h.image_closure, image_iUnion]
  simp_rw [hstep]
  rw [iUnion_comm, closure_iUnion_of_finite]
  congr 1
  funext j
  exact (hD j).symm

private theorem regularClosureUnion {Y : Type*} [TopologicalSpace Y]
    (B : ℕ → Set Y) (hB : ∀ n, B n = closure (interior (B n))) :
    closure (⋃ n, B n) = closure (interior (closure (⋃ n, B n))) := by
  apply Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    apply iUnion_subset
    intro n
    rw [hB n]
    apply closure_mono
    exact interior_mono ((subset_iUnion B n).trans subset_closure)
  · exact closure_minimal interior_subset isClosed_closure

/-- Relative closure and interior obey the regular-closed union law, without
changing from the full plaque to a smaller ambient carrier. -/
private theorem rc_regular_union {X : Type*} [TopologicalSpace X]
    (S : Set X) (B : ℕ → Set X)
    (hB : ∀ n, B n = rc S (ri S (B n))) :
    rc S (⋃ n, B n) = rc S (ri S (rc S (⋃ n, B n))) := by
  have hpre (n : ℕ) : (Subtype.val : S → X) ⁻¹' B n =
      closure (interior ((Subtype.val : S → X) ⁻¹' B n)) := by
    have hh := congrArg (fun U : Set X ↦ (Subtype.val : S → X) ⁻¹' U) (hB n)
    simpa only [rc, ri, preimage_image_eq _ Subtype.val_injective] using hh
  simp only [rc, ri, preimage_image_eq _ Subtype.val_injective, preimage_iUnion]
  rw [← regularClosureUnion _ hpre]

/-- A homeomorphism between relative open neighborhoods transports a compact
regular closed factor without changing either full ambient carrier. -/
private theorem regular_rebase_image
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (S T U C : Set X) (g : X → X) (hU : U ⊆ S) (hC : C ⊆ U)
    (himg : g '' U ⊆ T)
    (hUopen : IsOpen ((Subtype.val : S → X) ⁻¹' U))
    (hBopen : IsOpen ((Subtype.val : T → X) ⁻¹' (g '' U)))
    (h : Homeomorph {s : S // (s:X)∈U} {t : T // (t:X)∈g '' U})
    (hf : ∀ s, (h s).val.val = g s.val.val)
    (hcompact : IsCompact C) (hreg : C = rc S (ri S C)) :
    IsCompact (g '' C) ∧ g '' C = rc T (ri T (g '' C)) := by
  let Cp : Set {s : S // (s:X)∈U} := {s | s.val.val∈C}
  let F : {s : S // (s:X)∈U} → T := Subtype.val ∘ h
  have hpre : (Subtype.val : S → X) ⁻¹' C =
      closure (interior ((Subtype.val : S → X) ⁻¹' C)) := by
    have hh := congrArg (fun B : Set X ↦ (Subtype.val : S → X) ⁻¹' B) hreg
    simpa only [rc, ri, preimage_image_eq _ Subtype.val_injective] using hh
  have hCpReg : Cp = closure (interior Cp) :=
    BowenRegularClosedPreparation.regular_preimage continuous_subtype_val
      hUopen.isOpenMap_subtype_val hpre
  have hCpCompact : IsCompact Cp := by
    apply (_root_.Topology.IsEmbedding.subtypeVal.comp
      _root_.Topology.IsEmbedding.subtypeVal).isCompact_iff.mpr
    have heq : (fun s : {s : S // (s:X)∈U} ↦ s.val.val) '' Cp = C := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩; exact hc
      · intro hc; exact ⟨⟨⟨x, hU (hC hc)⟩, hC hc⟩, hc, rfl⟩
    change IsCompact ((fun s : {s : S // (s:X)∈U} ↦ s.val.val) '' Cp)
    rw [heq]
    exact hcompact
  have hFcont : Continuous F := continuous_subtype_val.comp h.continuous
  have hFopen : IsOpenMap F := hBopen.isOpenMap_subtype_val.comp h.isOpenMap
  have heq : F '' Cp = (Subtype.val : T → X) ⁻¹' (g '' C) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨s.val.val, hs, (hf s).symm⟩
    · rintro ⟨s, hs, hst⟩
      let s' : {s : S // (s:X)∈U} := ⟨⟨s,hU (hC hs)⟩,hC hs⟩
      exact ⟨s',hs,Subtype.ext ((hf s').trans hst)⟩
  have hsub : g '' C ⊆ T := image_mono hC |>.trans himg
  have hval : (Subtype.val : T → X) '' (F '' Cp) = g '' C := by
    rw [heq, image_preimage_eq_of_subset]
    simpa only [Subtype.range_coe] using hsub
  refine ⟨hval ▸ (hCpCompact.image hFcont).image continuous_subtype_val, ?_⟩
  have hregular := BowenRegularClosedPreparation.regular_image hFcont hFopen hCpReg hCpCompact
  rw [heq] at hregular
  rw [rc, ri, preimage_image_eq _ Subtype.val_injective, ← hregular]
  rw [image_preimage_eq_of_subset]
  simpa only [Subtype.range_coe] using hsub

private theorem compactRegularSlice
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x z : X) (hz : z ∈ ws f (2 * α 5) x) (C : Set X)
    (hC : C ⊆ wu f (2 * α 5) x) (hcompact : IsCompact C)
    (hreg : C = rc (wu f γ x) (ri (wu f γ x) C)) :
    IsCompact (bi bracket C {z}) ∧
      bi bracket C {z} = rc (wu f γ z) (ri (wu f γ z) (bi bracket C {z})) ∧
      ContinuousOn (fun c ↦ bracket c z) C := by
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hag (i : Fin 8) : α i ≤ γ := hα0 ▸ hmono (Fin.zero_le i)
  have hscale (i : Fin 7) : 9 * α i.succ < α i.castSucc := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have h53 : 2 * α 5 < α 3 := by
    have hh : 9 * α 5 < α 4 := hscale 4
    have hh' := hmono (show (3 : Fin 8) ≤ 4 by decide)
    linarith [hαpos 5]
  have h32 : α 3 < α 2 := hαdesc 2
  have h2γ : 2 * α 5 ≤ γ := h53.le.trans (hag 3)
  let U := wu f γ x ∩ Metric.ball x (α 3)
  have hCU : C ⊆ U := by
    intro c hc
    refine ⟨fun n ↦ (hC hc n).trans h2γ, ?_⟩
    exact (hC hc 0).trans_lt h53
  have hUguard : U ⊆ wu f (α 2) x := by
    intro c hc n
    have hh := hfact_u x c x n hc.1 (fun _ ↦ by simpa using hγ.le)
    have hd : dist c x < α 3 := hc.2
    exact (hh.trans ((mul_le_of_le_one_left dist_nonneg
      (pow_le_one₀ hlam.1.le hlam.2.le)).trans hd.le)).trans h32.le
  have hUopen : IsOpen ((Subtype.val : wu f γ x → X) ⁻¹' U) := by
    have heq : (Subtype.val : wu f γ x → X) ⁻¹' U = Subtype.val ⁻¹' Metric.ball x (α 3) := by
      ext c; exact and_iff_right c.property
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hxy : dist x z ≤ α 3 := by
    have hh : dist z x ≤ 2 * α 5 := hz 0
    rw [dist_comm]; exact hh.trans h53.le
  have hh := (bowen_fact1_plaque_rebase_g6 f lam γ ε hlam.1 hlam.2 hγ hε
    (fun i : Fin 5 ↦ α ⟨i.val, by omega⟩) εmod
    (fun δ hδ hδγ ↦ (hmod δ hδ hδγ).1) hα0
    (fun i ↦ hαpos ⟨i.val, by omega⟩)
    (fun i ↦ hαrec ⟨i.val, by omega⟩)
    (fun i ↦ hαmargin ⟨i.val, by omega⟩) bracket
    (by
      intro a u v n hu hv
      rw [← BowenRegularClosedPreparation.pow_apply_iterate,
        ← BowenRegularClosedPreparation.pow_apply_iterate]
      exact hfact_s a u v n
        (fun k ↦ by simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hu k)
        (fun k ↦ by simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hv k))
    (by
      intro a u v n hu hv
      rw [← BowenRegularClosedPreparation.pow_apply_iterate,
        ← BowenRegularClosedPreparation.pow_apply_iterate]
      exact hfact_u a u v n
        (fun k ↦ by simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hu k)
        (fun k ↦ by simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hv k))
    (by
      intro a b hab
      refine ⟨bracket a b, ⟨?_, ?_⟩, ?_⟩
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using (hbracket_mem a b hab).1 n
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using (hbracket_mem a b hab).2 n
      · intro c hc
        exact hbracket_unique a b c hab
          (fun k ↦ by simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hc.1 k)
          (fun k ↦ by simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hc.2 k))
    (by
      intro a b hab
      constructor
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using (hbracket_mem a b hab).1 n
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using (hbracket_mem a b hab).2 n)
    hbracket_cont
    (by
      intro δ hδ hδγ a b hab
      constructor
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using ((hmod δ hδ hδγ).2 a b hab).1 n
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using ((hmod δ hδ hδγ).2 a b hab).2 n)
    x z hxy).1
  change ∀ U : Set X,
    U ⊆ {c | ∀ n : ℕ, dist ((f.symm : X → X)^[n] c) ((f.symm : X → X)^[n] x) ≤ α 2} →
    IsOpen ((Subtype.val : {c | ∀ n : ℕ, dist ((f.symm : X → X)^[n] c)
      ((f.symm : X → X)^[n] x) ≤ γ} → X) ⁻¹' U) →
    let B := (fun c ↦ bracket c z) '' U
    B ⊆ {c | ∀ n : ℕ, dist ((f.symm : X → X)^[n] c) ((f.symm : X → X)^[n] z) ≤ γ} ∧
    IsOpen ((Subtype.val : {c | ∀ n : ℕ, dist ((f.symm : X → X)^[n] c)
      ((f.symm : X → X)^[n] z) ≤ γ} → X) ⁻¹' B) ∧
    ∃ h : Homeomorph
      {c : {c | ∀ n : ℕ, dist ((f.symm : X → X)^[n] c) ((f.symm : X → X)^[n] x) ≤ γ} // (c : X) ∈ U}
      {c : {c | ∀ n : ℕ, dist ((f.symm : X → X)^[n] c) ((f.symm : X → X)^[n] z) ≤ γ} // (c : X) ∈ B},
      (∀ c, (h c).val.val = bracket c.val.val z) ∧
      (∀ c, (h.symm c).val.val = bracket c.val.val x) at hh
  have huE : ∀ a δ, {c : X | ∀ n : ℕ, dist ((f.symm : X → X)^[n] c)
      ((f.symm : X → X)^[n] a) ≤ δ} = wu f δ a := by
    intro a δ; ext c; simp only [wu, BowenRegularClosedPreparation.pow_apply_iterate]
  rw [huE x γ, huE z γ, huE x (α 2)] at hh
  obtain ⟨hBU, hBopen, h, hf, _⟩ := hh U hUguard hUopen
  have hresult := regular_rebase_image (wu f γ x) (wu f γ z) U C (fun c ↦ bracket c z)
    inter_subset_left hCU hBU hUopen hBopen h hf hcompact hreg
  have himage : (fun c ↦ bracket c z) '' C = bi bracket C {z} := by
    ext q
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, z, rfl, rfl⟩
    · rintro ⟨c, hc, d, hd, he⟩
      have hd : d = z := hd
      exact ⟨c, hc, hd ▸ he⟩
  have hcontinuous : ContinuousOn (fun c ↦ bracket c z) C := by
    rw [continuousOn_iff_continuous_domRestrict]
    let lift : C → {c : wu f γ x // (c : X) ∈ U} :=
      fun c ↦ ⟨⟨c.val, (hCU c.property).1⟩, hCU c.property⟩
    have hlift : Continuous lift := (continuous_subtype_val.subtype_mk _).subtype_mk _
    have hcomp := continuous_subtype_val.comp
      (continuous_subtype_val.comp (h.continuous.comp hlift))
    exact hcomp.congr (fun c ↦ hf (lift c))
  exact ⟨by simpa only [himage] using hresult.1,
    by simpa only [himage] using hresult.2, hcontinuous⟩

private theorem limitRectangleProperties
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x : X) (C D : Set X) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hCc : IsCompact C) (hDc : IsCompact D)
    (hC : C ⊆ wu f ((3 / 2) * α 5) x) (hD : D ⊆ ws f ((3 / 2) * α 5) x)
    (hCr : C = rc (wu f γ x) (ri (wu f γ x) C))
    (hDr : D = rc (ws f γ x) (ri (ws f γ x) D)) :
    proper bracket (α 3) (bi bracket C D) ∧ Metric.diam (bi bracket C D) < α 4 := by
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hag (i : Fin 8) : α i ≤ γ := hα0 ▸ hmono (Fin.zero_le i)
  have hscale (i : Fin 7) : 9 * α i.succ < α i.castSucc := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hmodscale (i : Fin 7) : 3 * α i.succ < εmod (α i.castSucc / 3) := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have h54 : 9 * α 5 < α 4 := hscale 4
  have h65 : 9 * α 6 < α 5 := hscale 5
  have hpreC : (Subtype.val : wu f γ x → X) ⁻¹' C =
      closure (interior ((Subtype.val : wu f γ x → X) ⁻¹' C)) := by
    have hh := congrArg (fun B : Set X ↦ (Subtype.val : wu f γ x → X) ⁻¹' B) hCr
    simpa only [rc, ri, preimage_image_eq _ Subtype.val_injective] using hh
  have hpreD : (Subtype.val : ws f γ x → X) ⁻¹' D =
      closure (interior ((Subtype.val : ws f γ x → X) ⁻¹' D)) := by
    have hh := congrArg (fun B : Set X ↦ (Subtype.val : ws f γ x → X) ⁻¹' B) hDr
    simpa only [rc, ri, preimage_image_eq _ Subtype.val_injective] using hh
  have hh := dynamics_bowen_fact1_regular_closed_product_g6 f lam γ ε bracket εmod
    (fun i : Fin 5 ↦ α ⟨i.val, by omega⟩) x hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod hα0
    (fun i ↦ hαpos ⟨i.val, by omega⟩) (fun i ↦ hαdesc ⟨i.val, by omega⟩)
    (fun i ↦ hαrec ⟨i.val, by omega⟩) (fun i ↦ hαmargin ⟨i.val, by omega⟩)
    C D hCne hDne hCc hDc
    (fun c hc n ↦ (hC hc n).trans (by change (3 / 2) * α 5 ≤ α 4; linarith [hαpos 5]))
    (fun d hd n ↦ (hD hd n).trans (by change (3 / 2) * α 5 ≤ α 4; linarith [hαpos 5])) hpreC hpreD
  refine ⟨⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩, ?_⟩
  have hpoint' (q : X) (hq : q ∈ bi bracket C D) : dist q x ≤ α 4 / 3 + (3 / 2) * α 5 := by
    obtain ⟨c, hc, d, hd, rfl⟩ := hq
    have hc0 : dist c x ≤ (3 / 2) * α 5 := hC hc 0
    have hd0 : dist d x ≤ (3 / 2) * α 5 := hD hd 0
    have hcd : dist c d ≤ 3 * α 5 := by
      have ht := dist_triangle c x d
      rw [dist_comm x d] at ht
      linarith
    have hsmall' := (hmod (α 4 / 3) (by linarith [hαpos 4]) (by linarith [hag 4])).2 c d
      (by
        have hm5 : 3 * α 5 < εmod (α 4 / 3) := hmodscale 4
        linarith)
    have hq0 : dist (bracket c d) c ≤ α 4 / 3 := hsmall'.1 0
    exact (dist_triangle _ c x).trans (add_le_add hq0 hc0)
  have hdiam : Metric.diam (bi bracket C D) ≤ 2 * (α 4 / 3 + (3 / 2) * α 5) := by
    apply Metric.diam_le_of_forall_dist_le (by linarith [hαpos 4, hαpos 5])
    intro p hp q hq
    have ht := dist_triangle p x q
    rw [dist_comm x q] at ht
    linarith [hpoint' p hp, hpoint' q hq]
  exact hdiam.trans_lt (by linarith)

/-- Bowen Lemma 14: project the centers of a compact unstable slice subcover to the
receiving stable factor, then pull them back. The backward contraction bounds the source
labels, and the slice formula transfers the selected seed's stable saturation. -/
private theorem finiteReceivingLabels
    {X I : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [Fintype I] [Nonempty I]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x₀ : I → X) (C₀ D₀ : I → Set X)
    (hC₀ : ∀ i, (C₀ i).Nonempty ∧ IsCompact (C₀ i) ∧ C₀ i ⊆ wu f (α 7) (x₀ i) ∧
      C₀ i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C₀ i)) ∧
      x₀ i ∈ ri (wu f γ (x₀ i)) (C₀ i))
    (hD₀ : ∀ i, (D₀ i).Nonempty ∧ IsCompact (D₀ i) ∧ D₀ i ⊆ ws f (α 7) (x₀ i) ∧
      D₀ i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D₀ i)) ∧
      x₀ i ∈ ri (ws f γ (x₀ i)) (D₀ i))
    (hproper₀ : ∀ i, proper bracket (α 3) (bi bracket (C₀ i) (D₀ i)))
    (_hcover₀ : (univ : Set X) ⊆ ⋃ i, interior (bi bracket (C₀ i) (D₀ i)))
    (hdiam₀ : ∀ i, Metric.diam (bi bracket (C₀ i) (D₀ i)) < α 5 / 2)
    (_hseed_u : ∀ i y, y ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (C₀ i) {y} ⊆ wu f (α 5) y)
    (_hseed_s : ∀ i y, y ∈ wu f (2 * α 5) (x₀ i) →
      bi bracket {y} (D₀ i) ⊆ ws f (α 5) y)
    (a : ℝ) (ha : 0 < a ∧ a < min γ (α 3)) (F : X → I)
    (hFmem : ∀ x, x ∈ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFs : ∀ x z, z ∈ wu f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      ws f a z ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFu : ∀ x y, y ∈ ws f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      wu f a y ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (m : ℕ) (hm : 1 ≤ m)
    (_hsum : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) :
    ∃ (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
      (y : (i : I) → Fin (k i) → X),
      (∀ i j, y i j ∈ wu f (α 5) (x₀ i) ∧ (f ^ m) (y i j) ∈ D₀ (T i j) ∧
        ((f ^ m) '' C₀ i ∩ bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}).Nonempty ∧
        ∀ z, z ∈ wu f γ ((f ^ m) (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
          ws f a z ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j))) ∧
      (∀ i, (f ^ m) '' C₀ i ⊆ ⋃ j, bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}) := by
  classical
  have hαmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hαγ : ∀ j, α j ≤ γ := fun j ↦ hα0 ▸ hαmono (Fin.zero_le j)
  have hscale (i : Fin 7) : 9 * α i.succ < α i.castSucc := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hscaleMod (i : Fin 7) : 3 * α i.succ < εmod (α i.castSucc / 3) := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hselfS (r : ℝ) (hr : 0 ≤ r) (x : X) : x ∈ ws f r x :=
    fun n ↦ by simpa using hr
  have hselfU (r : ℝ) (hr : 0 ≤ r) (x : X) : x ∈ wu f r x :=
    fun n ↦ by simpa using hr
  have hdiag (x z : X) (hs : z ∈ ws f γ x) (hu : z ∈ wu f γ x) : z = x :=
    (hbracket_unique x x z (by simpa using hε.le) hs hu).trans
      (hbracket_unique x x x (by simpa using hε.le)
        (hselfS γ hγ.le x) (hselfU γ hγ.le x)).symm
  have hbaseC (i : I) : x₀ i ∈ C₀ i := by
    obtain ⟨v, hv, he⟩ := (hC₀ i).2.2.2.2
    have hv' : v ∈ (Subtype.val : wu f γ (x₀ i) → X) ⁻¹' C₀ i := interior_subset hv
    exact he ▸ hv'
  have hbaseD (i : I) : x₀ i ∈ D₀ i := by
    obtain ⟨v, hv, he⟩ := (hD₀ i).2.2.2.2
    have hv' : v ∈ (Subtype.val : ws f γ (x₀ i) → X) ⁻¹' D₀ i := interior_subset hv
    exact he ▸ hv'
  have hβpos : 0 < lam ^ m := pow_pos hlam.1 m
  have hβlt : lam ^ m < 1 := pow_lt_one₀ hlam.1.le hlam.2 (by omega)
  have hfactor (i : I) (c d : X) (hc : c ∈ C₀ i) (hd : d ∈ D₀ i) :
      bracket c d ∈ ws f (α 6 / 3) c ∩ wu f (α 6 / 3) d := by
    apply (hmod (α 6 / 3) (div_pos (hαpos 6) (by norm_num)) (by linarith [hαγ 6])).2
    have hc0 : dist c (x₀ i) ≤ α 7 := (hC₀ i).2.2.1 hc 0
    have hd0 : dist d (x₀ i) ≤ α 7 := (hD₀ i).2.2.1 hd 0
    have htri := dist_triangle c (x₀ i) d
    rw [dist_comm (x₀ i) d] at htri
    have hh := hscaleMod 6
    norm_num at hh
    linarith [hαpos 7]
  have hfixC (i : I) (c : X) (hc : c ∈ C₀ i) : bracket c (x₀ i) = c := by
    have hb := hfactor i c (x₀ i) hc (hbaseD i)
    apply hdiag c _ (fun n ↦ (hb.1 n).trans (by linarith [hαγ 6]))
    intro n
    have hh := dist_triangle ((f.symm ^ n) (bracket c (x₀ i)))
      ((f.symm ^ n) (x₀ i)) ((f.symm ^ n) c)
    rw [dist_comm ((f.symm ^ n) (x₀ i)) ((f.symm ^ n) c)] at hh
    have h1 := hb.2 n
    have h2 := (hC₀ i).2.2.1 hc n
    have hhscale := hscale 6
    norm_num at hhscale
    linarith [hαγ 6]
  have hfixD (i : I) (d : X) (hd : d ∈ D₀ i) : bracket (x₀ i) d = d := by
    have hb := hfactor i (x₀ i) d (hbaseC i) hd
    apply hdiag d _ ?_ (fun n ↦ (hb.2 n).trans (by linarith [hαγ 6]))
    intro n
    have hh := dist_triangle ((f ^ n) (bracket (x₀ i) d))
      ((f ^ n) (x₀ i)) ((f ^ n) d)
    rw [dist_comm ((f ^ n) (x₀ i)) ((f ^ n) d)] at hh
    have h1 := hb.1 n
    have h2 := (hD₀ i).2.2.1 hd n
    have hhscale := hscale 6
    norm_num at hhscale
    linarith [hαγ 6]
  have hCinA (i : I) : C₀ i ⊆ bi bracket (C₀ i) (D₀ i) :=
    fun c hc ↦ ⟨c, hc, x₀ i, hbaseD i, hfixC i c hc⟩
  have hDinA (i : I) : D₀ i ⊆ bi bracket (C₀ i) (D₀ i) :=
    fun d hd ↦ ⟨x₀ i, hbaseC i, d, hd, hfixD i d hd⟩
  /- Bowen Lemma 14's seed-slice identity.  The cited regular-closed product theorem
     is exactly the published product/slice assertion used in Bowen's p.732 proof. -/
  have hseedSlices : ∀ i q, q ∈ bi bracket (C₀ i) (D₀ i) →
      bi bracket (C₀ i) (D₀ i) ∩ wu f γ q = bi bracket (C₀ i) {q} := by
    intro i
    let α' : Fin 5 → ℝ := fun j ↦ α ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩
    have hCreg : (Subtype.val : wu f γ (x₀ i) → X) ⁻¹' C₀ i =
        closure (interior ((Subtype.val : wu f γ (x₀ i) → X) ⁻¹' C₀ i)) := by
      have heq := congrArg (fun S : Set X ↦
        (Subtype.val : wu f γ (x₀ i) → X) ⁻¹' S) (hC₀ i).2.2.2.1
      simpa only [rc, ri, Set.preimage_image_eq _ Subtype.val_injective] using heq
    have hDreg : (Subtype.val : ws f γ (x₀ i) → X) ⁻¹' D₀ i =
        closure (interior ((Subtype.val : ws f γ (x₀ i) → X) ⁻¹' D₀ i)) := by
      have heq := congrArg (fun S : Set X ↦
        (Subtype.val : ws f γ (x₀ i) → X) ⁻¹' S) (hD₀ i).2.2.2.1
      simpa only [rc, ri, Set.preimage_image_eq _ Subtype.val_injective] using heq
    have hp := dynamics_bowen_fact1_regular_closed_product_g6
      f lam γ ε bracket εmod α' (x₀ i) hlam hγ hε hfact_s hfact_u
      hbracket_mem hbracket_unique hbracket_cont hmod hα0
      (fun j ↦ hαpos _) (fun j ↦ hαdesc ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩)
      (fun j ↦ hαrec ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩)
      (fun j ↦ hαmargin ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩)
      (C₀ i) (D₀ i) (hC₀ i).1 (hD₀ i).1 (hC₀ i).2.1 (hD₀ i).2.1
      (fun z hz n ↦ ((hC₀ i).2.2.1 hz n).trans (hαmono (show (4 : Fin 8) ≤ 7 by decide)))
      (fun z hz n ↦ ((hD₀ i).2.2.1 hz n).trans (hαmono (show (4 : Fin 8) ≤ 7 by decide)))
      hCreg hDreg
    exact hp.2.2.2.2.2.1
  /- Bowen Lemma 14's finite receiving-slice cover. The finite-prefix/tail local
     calculation is packaged in the existing source-backed compact-cover lemma. -/
  have hfiniteSlices : ∀ i, ∃ s : Finset (C₀ i),
      (f ^ m) '' C₀ i ⊆ ⋃ z ∈ s, bi bracket (C₀ (F ((f ^ m) z))) {(f ^ m) z} := by
    intro i
    obtain ⟨s, hs⟩ := RectangleSlicesPreparation.finite_unstable_slice_cover
      f hlam.1.le hlam.2.le ha.1 (ha.2.trans_le (min_le_left _ _)).le hfact_u
      (hC₀ i).2.1 (fun z hz n ↦ ((hC₀ i).2.2.1 hz n).trans (hαγ 7))
      m (fun j ↦ bi bracket (C₀ j) (D₀ j)) F (fun z hz ↦
        hFu ((f ^ m) z) ((f ^ m) z)
          ⟨fun n ↦ by simpa using hγ.le, hFmem ((f ^ m) z)⟩)
    refine ⟨s, ?_⟩
    change (f ^ m) '' C₀ i ⊆ ⋃ z ∈ s,
      bi bracket (C₀ (F ((f ^ m) z))) (D₀ (F ((f ^ m) z))) ∩
        wu f γ ((f ^ m) z) at hs
    simpa only [hseedSlices _ _ (hFmem _)] using hs
  /- Enumerate the actual compact subcover, retaining an anchor in every chosen
     source slice. This is the finite-label choice in Bowen Lemma 14, p.732. -/
  have hindexedSlices : ∀ i, ∃ (k : ℕ) (z : Fin k → C₀ i),
      ((f ^ m) '' C₀ i ⊆ ⋃ j, bi bracket (C₀ (F ((f ^ m) (z j)))) {(f ^ m) (z j)}) ∧
      ∀ j, ((f ^ m) '' C₀ i ∩
        bi bracket (C₀ (F ((f ^ m) (z j)))) {(f ^ m) (z j)}).Nonempty := by
    intro i
    obtain ⟨s, hs⟩ := hfiniteSlices i
    let e := s.equivFin
    let z : Fin s.card → C₀ i := fun j ↦ (e.symm j).val
    refine ⟨s.card, z, ?_, ?_⟩
    · intro v hv
      obtain ⟨u, hu, hvu⟩ := Set.mem_iUnion₂.mp (hs hv)
      refine Set.mem_iUnion.mpr ⟨e ⟨u, hu⟩, ?_⟩
      simpa only [z, Equiv.symm_apply_apply] using hvu
    · intro j
      refine ⟨(f ^ m) (z j), ⟨z j, (z j).property, rfl⟩, ?_⟩
      rw [← hseedSlices _ _ (hFmem ((f ^ m) (z j)))]
      exact ⟨hFmem _, fun n ↦ by simpa using hγ.le⟩
  have hseedDist (i : I) (p q : X) (hp : p ∈ bi bracket (C₀ i) (D₀ i))
      (hq : q ∈ bi bracket (C₀ i) (D₀ i)) : dist p q < α 5 / 2 :=
    (Metric.dist_le_diam_of_mem (hproper₀ i).2.1.isBounded hp hq).trans_lt (hdiam₀ i)
  have hseedRecenter (i : I) (p q : X)
      (hp : p ∈ bi bracket (C₀ i) (D₀ i))
      (hq : q ∈ bi bracket (C₀ i) (D₀ i)) (hpq : q ∈ wu f γ p) :
      bi bracket (C₀ i) {p} = bi bracket (C₀ i) {q} := by
    rw [← hseedSlices i p hp, ← hseedSlices i q hq]
    ext z
    constructor
    · rintro ⟨hz, hzp⟩
      refine ⟨hz, ?_⟩
      exact BowenRegularClosedPreparation.contraction_bound f.symm ⟨hlam.1.le, hlam.2.le⟩
        hfact_u hzp hpq ((hseedDist i z q hz hq).le.trans (by linarith [hαγ 5]))
    · rintro ⟨hz, hzq⟩
      refine ⟨hz, ?_⟩
      exact BowenRegularClosedPreparation.contraction_bound f.symm ⟨hlam.1.le, hlam.2.le⟩
        hfact_u hzq (fun n ↦ by simpa only [dist_comm] using hpq n)
        ((hseedDist i z p hz hp).le.trans (by linarith [hαγ 5]))
  choose k z hzcover hzmeet using hindexedSlices
  let T : (i : I) → Fin (k i) → I := fun i j ↦ F ((f ^ m) (z i j))
  have hcoords : ∀ i j, ∃ c ∈ C₀ (T i j), ∃ d ∈ D₀ (T i j),
      bracket c d = (f ^ m) (z i j) := fun i j ↦ hFmem _
  choose c hc d hd hcd using hcoords
  let y : (i : I) → Fin (k i) → X := fun i j ↦ (f ^ m).symm (d i j)
  have hdU (i : I) (j : Fin (k i)) : d i j ∈ wu f γ ((f ^ m) (z i j)) := by
    intro n
    have hh := (hfactor (T i j) (c i j) (d i j) (hc i j) (hd i j)).2 n
    rw [hcd i j, dist_comm] at hh
    exact hh.trans (by linarith [hαγ 6])
  have hdy (i : I) (j : Fin (k i)) : (f ^ m) (y i j) = d i j :=
    Homeomorph.apply_symm_apply _ _
  have hyU (i : I) (j : Fin (k i)) : y i j ∈ wu f (α 5) (x₀ i) := by
    intro n
    have hcontract := hfact_u ((f ^ m) (z i j)) (d i j) ((f ^ m) (z i j))
      (n + m) (hdU i j) (hselfU γ hγ.le _)
    have hdistance := hseedDist (T i j) (d i j) ((f ^ m) (z i j))
      (hDinA _ (hd i j)) (hFmem _)
    have hbound : lam ^ (n + m) * dist (d i j) ((f ^ m) (z i j)) ≤ α 5 / 2 :=
      (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.1.le hlam.2.le)).trans
        hdistance.le
    have hnorm : dist ((f.symm ^ n) (y i j)) ((f.symm ^ n) (z i j)) ≤ α 5 / 2 := by
      have hi : f.symm ^ m = (f ^ m).symm := inv_pow f m
      simpa only [y, pow_add, Homeomorph.mul_apply, hi,
        Homeomorph.symm_apply_apply] using hcontract.trans hbound
    have hseed := (hC₀ i).2.2.1 (z i j).property n
    have htriangle := dist_triangle ((f.symm ^ n) (y i j))
      ((f.symm ^ n) (z i j)) ((f.symm ^ n) (x₀ i))
    have h75 := hαmono (show (6 : Fin 8) ≤ 7 by decide)
    have h65 := hscale 5
    norm_num at h65
    linarith [hαpos 6]
  have hyData (i : I) (j : Fin (k i)) :
      y i j ∈ wu f (α 5) (x₀ i) ∧ (f ^ m) (y i j) ∈ D₀ (T i j) ∧
      ((f ^ m) '' C₀ i ∩ bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}).Nonempty ∧
      ∀ v, v ∈ wu f γ ((f ^ m) (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
        ws f a v ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j)) := by
    rw [hdy]
    refine ⟨hyU i j, hd i j, ?_, ?_⟩
    · rw [← hseedRecenter (T i j) ((f ^ m) (z i j)) (d i j)
        (hFmem _) (hDinA _ (hd i j)) (hdU i j)]
      exact hzmeet i j
    · intro v hv
      apply hFs ((f ^ m) (z i j)) v
      refine ⟨?_, hv.2⟩
      exact BowenRegularClosedPreparation.contraction_bound f.symm ⟨hlam.1.le, hlam.2.le⟩
        hfact_u hv.1 (fun n ↦ by simpa only [dist_comm] using hdU i j n)
        ((hseedDist _ v _ hv.2 (hFmem _)).le.trans (by linarith [hαγ 5]))
  have hyCover (i : I) : (f ^ m) '' C₀ i ⊆
      ⋃ j, bi bracket (C₀ (T i j)) {(f ^ m) (y i j)} := by
    intro v hv
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hzcover i hv)
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [hdy, ← hseedRecenter (T i j) ((f ^ m) (z i j)) (d i j)
      (hFmem _) (hDinA _ (hd i j)) (hdU i j)]
    exact hj
  exact ⟨k, T, y, hyData, hyCover⟩

/-- One step of Bowen's enlargement: a bounded family of factors remains in
the source collar, and its slices satisfy the exact finite transport formula. -/
private theorem enlargementStep
    {X I : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [Fintype I] [Nonempty I]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (_hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (_hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (_hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x₀ : I → X) (C₀ D₀ : I → Set X)
    (hC₀ : ∀ i, (C₀ i).Nonempty ∧ IsCompact (C₀ i) ∧ C₀ i ⊆ wu f (α 7) (x₀ i) ∧
      C₀ i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C₀ i)) ∧
      x₀ i ∈ ri (wu f γ (x₀ i)) (C₀ i))
    (hD₀ : ∀ i, (D₀ i).Nonempty ∧ IsCompact (D₀ i) ∧ D₀ i ⊆ ws f (α 7) (x₀ i) ∧
      D₀ i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D₀ i)) ∧
      x₀ i ∈ ri (ws f γ (x₀ i)) (D₀ i))
    (_hproper₀ : ∀ i, proper bracket (α 3) (bi bracket (C₀ i) (D₀ i)))
    (_hcover₀ : (univ : Set X) ⊆ ⋃ i, interior (bi bracket (C₀ i) (D₀ i)))
    (_hdiam₀ : ∀ i, Metric.diam (bi bracket (C₀ i) (D₀ i)) < α 5 / 2)
    (_hseed_u : ∀ i y, y ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (C₀ i) {y} ⊆ wu f (α 5) y)
    (_hseed_s : ∀ i y, y ∈ wu f (2 * α 5) (x₀ i) →
      bi bracket {y} (D₀ i) ⊆ ws f (α 5) y)
    (a : ℝ) (ha : 0 < a ∧ a < min γ (α 3)) (F : X → I)
    (_hFmem : ∀ x, x ∈ bi bracket (C₀ (F x)) (D₀ (F x)))
    (_hFs : ∀ x z, z ∈ wu f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      ws f a z ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (_hFu : ∀ x y, y ∈ ws f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      wu f a y ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (m : ℕ) (hm : 1 ≤ m)
    (hsum : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) 
    (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X)
    (hy : ∀ i j, y i j ∈ wu f (α 5) (x₀ i) ∧ (f ^ m) (y i j) ∈ D₀ (T i j) ∧
      ((f ^ m) '' C₀ i ∩ bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}).Nonempty ∧
      ∀ z, z ∈ wu f γ ((f ^ m) (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
        ws f a z ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j)))
    (V : I → Set X)
    (hV : ∀ i, V i ⊆ wu f (2 * α 5) (x₀ i))
    (hVs : ∀ i z, z ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (V i) {z} ⊆ wu f (2 * α 5) z) :
    let B := fun i ↦ ⋃ j, (f ^ m).symm '' bi bracket (V (T i j)) {(f ^ m) (y i j)}
    (∀ i, B i ⊆ wu f (2 * α 5) (x₀ i)) ∧
    (∀ i z, z ∈ ws f (2 * α 5) (x₀ i) →
      (∀ j, (f ^ m) (bracket (y i j) z) ∈ D₀ (T i j)) ∧
      (f ^ m) '' bi bracket (B i) {z} =
        ⋃ j, bi bracket (V (T i j)) {(f ^ m) (bracket (y i j) z)} ∧
      ∀ j c, c ∈ V (T i j) →
        (f ^ m) (bracket ((f ^ m).symm (bracket c ((f ^ m) (y i j)))) z) =
          bracket c ((f ^ m) (bracket (y i j) z))) := by
  classical
  have hαmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hαγ : ∀ j, α j ≤ γ := fun j ↦ hα0 ▸ hαmono (Fin.zero_le j)
  have hscale (i : Fin 7) : 9 * α i.succ < α i.castSucc := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hscaleMod (i : Fin 7) : 3 * α i.succ < εmod (α i.castSucc / 3) := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hselfS (r : ℝ) (hr : 0 ≤ r) (x : X) : x ∈ ws f r x :=
    fun n ↦ by simpa using hr
  have hselfU (r : ℝ) (hr : 0 ≤ r) (x : X) : x ∈ wu f r x :=
    fun n ↦ by simpa using hr
  have hdiag (x z : X) (hs : z ∈ ws f γ x) (hu : z ∈ wu f γ x) : z = x :=
    (hbracket_unique x x z (by simpa using hε.le) hs hu).trans
      (hbracket_unique x x x (by simpa using hε.le)
        (hselfS γ hγ.le x) (hselfU γ hγ.le x)).symm
  have hbaseC (i : I) : x₀ i ∈ C₀ i := by
    obtain ⟨v, hv, he⟩ := (hC₀ i).2.2.2.2
    have hv' : v ∈ (Subtype.val : wu f γ (x₀ i) → X) ⁻¹' C₀ i := interior_subset hv
    exact he ▸ hv'
  have hbaseD (i : I) : x₀ i ∈ D₀ i := by
    obtain ⟨v, hv, he⟩ := (hD₀ i).2.2.2.2
    have hv' : v ∈ (Subtype.val : ws f γ (x₀ i) → X) ⁻¹' D₀ i := interior_subset hv
    exact he ▸ hv'
  have hβpos : 0 < lam ^ m := pow_pos hlam.1 m
  have hβlt : lam ^ m < 1 := pow_lt_one₀ hlam.1.le hlam.2 (by omega)
  have hfactor (i : I) (c d : X) (hc : c ∈ C₀ i) (hd : d ∈ D₀ i) :
      bracket c d ∈ ws f (α 6 / 3) c ∩ wu f (α 6 / 3) d := by
    apply (hmod (α 6 / 3) (div_pos (hαpos 6) (by norm_num)) (by linarith [hαγ 6])).2
    have hc0 : dist c (x₀ i) ≤ α 7 := (hC₀ i).2.2.1 hc 0
    have hd0 : dist d (x₀ i) ≤ α 7 := (hD₀ i).2.2.1 hd 0
    have htri := dist_triangle c (x₀ i) d
    rw [dist_comm (x₀ i) d] at htri
    have hh := hscaleMod 6
    norm_num at hh
    linarith [hαpos 7]
  have hfixC (i : I) (c : X) (hc : c ∈ C₀ i) : bracket c (x₀ i) = c := by
    have hb := hfactor i c (x₀ i) hc (hbaseD i)
    apply hdiag c _ (fun n ↦ (hb.1 n).trans (by linarith [hαγ 6]))
    intro n
    have hh := dist_triangle ((f.symm ^ n) (bracket c (x₀ i)))
      ((f.symm ^ n) (x₀ i)) ((f.symm ^ n) c)
    rw [dist_comm ((f.symm ^ n) (x₀ i)) ((f.symm ^ n) c)] at hh
    have h1 := hb.2 n
    have h2 := (hC₀ i).2.2.1 hc n
    have hhscale := hscale 6
    norm_num at hhscale
    linarith [hαγ 6]
  have hfixD (i : I) (d : X) (hd : d ∈ D₀ i) : bracket (x₀ i) d = d := by
    have hb := hfactor i (x₀ i) d (hbaseC i) hd
    apply hdiag d _ ?_ (fun n ↦ (hb.2 n).trans (by linarith [hαγ 6]))
    intro n
    have hh := dist_triangle ((f ^ n) (bracket (x₀ i) d))
      ((f ^ n) (x₀ i)) ((f ^ n) d)
    rw [dist_comm ((f ^ n) (x₀ i)) ((f ^ n) d)] at hh
    have h1 := hb.1 n
    have h2 := (hD₀ i).2.2.1 hd n
    have hhscale := hscale 6
    norm_num at hhscale
    linarith [hαγ 6]
  have hCinA (i : I) : C₀ i ⊆ bi bracket (C₀ i) (D₀ i) :=
    fun c hc ↦ ⟨c, hc, x₀ i, hbaseD i, hfixC i c hc⟩
  have hDinA (i : I) : D₀ i ⊆ bi bracket (C₀ i) (D₀ i) :=
    fun d hd ↦ ⟨x₀ i, hbaseC i, d, hd, hfixD i d hd⟩
  have h53 : 9 * α 5 < α 3 := (hscale 4).trans_le (hαmono (by decide))
  have h32 : 9 * α 3 < α 2 := hscale 2
  have h10 : 9 * α 1 < γ := hα0 ▸ hscale 0
  have haγ : a < γ / 2 := by
    have ha3 := ha.2.trans_le (min_le_right _ _)
    have h31 := hαmono (show (1 : Fin 8) ≤ 3 by decide)
    linarith [hαpos 1]
  obtain ⟨hβ0, hβhalf, hβa, hpartial⟩ :=
    enlargement_numeric_bounds lam γ a hlam hγ ha.1 haγ m hm hsum
  have h2γ : 2 * α 5 ≤ γ := by linarith [hαγ 3, hαpos 5]
  have hDsmall (i : I) (d : X) (hd : d ∈ D₀ i) : d ∈ ws f (2 * α 5) (x₀ i) :=
    fun n ↦ ((hD₀ i).2.2.1 hd n).trans (by
      have hh := hαmono (show (5 : Fin 8) ≤ 7 by decide)
      linarith [hαpos 5])
  let B := fun i ↦ ⋃ j, (f ^ m).symm '' bi bracket (V (T i j)) {(f ^ m) (y i j)}
  have hB (i : I) : B i ⊆ wu f (2 * α 5) (x₀ i) := by
    intro v hv
    obtain ⟨j, q, hq, rfl⟩ := mem_iUnion.mp hv
    have hqp := hVs (T i j) _ (hDsmall _ _ (hy i j).2.1) hq
    have hh := unstable_pullback_radius f lam γ (2 * α 5) ⟨hlam.1.le, hlam.2.le⟩
      hγ.le h2γ hfact_u hqp m
    intro n
    have hp := hh n
    rw [Homeomorph.symm_apply_apply] at hp
    have ht := dist_triangle ((f.symm ^ n) ((f ^ m).symm q))
      ((f.symm ^ n) (y i j)) ((f.symm ^ n) (x₀ i))
    have hj := (hy i j).1 n
    nlinarith [hαpos 5]
  refine ⟨hB, ?_⟩
  intro i z hz
  have hsD (j : Fin (k i)) : (f ^ m) (bracket (y i j) z) ∈ D₀ (T i j) := by
    have hpair : dist (y i j) z ≤ 3 * α 5 := by
      have hy0 : dist (y i j) (x₀ i) ≤ α 5 := (hy i j).1 0
      have hz0 : dist z (x₀ i) ≤ 2 * α 5 := hz 0
      have hh := dist_triangle (y i j) (x₀ i) z
      rw [dist_comm (x₀ i) z] at hh
      linarith
    have he5 : 3 * α 5 < εmod (α 4 / 3) := hscaleMod 4
    have hb := (hmod (α 4 / 3) (div_pos (hαpos 4) (by norm_num))
      (by linarith [hαγ 4])).2 (y i j) z (hpair.trans he5.le)
    have hstable : (f ^ m) (bracket (y i j) z) ∈ ws f a ((f ^ m) (y i j)) := by
      intro n
      have hc := hfact_s (y i j) (bracket (y i j) z) (y i j) (n + m)
        (fun t ↦ (hb.1 t).trans (by linarith [hαγ 4])) (hselfS γ hγ.le _)
      have hd : dist (bracket (y i j) z) (y i j) ≤ γ :=
        (hb.1 0).trans (by linarith [hαγ 4])
      have hp : lam ^ (n + m) * dist (bracket (y i j) z) (y i j) ≤ lam ^ m * γ := by
        rw [pow_add]
        calc
          lam ^ n * lam ^ m * dist (bracket (y i j) z) (y i j) =
              lam ^ m * (lam ^ n * dist (bracket (y i j) z) (y i j)) := by ring
          _ ≤ lam ^ m * dist (bracket (y i j) z) (y i j) :=
            mul_le_mul_of_nonneg_left
              (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.1.le hlam.2.le)) hβ0.le
          _ ≤ lam ^ m * γ := mul_le_mul_of_nonneg_left hd hβ0.le
      simpa only [pow_add, Homeomorph.mul_apply] using (hc.trans hp).trans hβa.le
    have hsA := (hy i j).2.2.2 ((f ^ m) (y i j))
      ⟨hselfU γ hγ.le _, hDinA _ (hy i j).2.1⟩ hstable
    obtain ⟨c, hc, d, hd, heq⟩ := hsA
    have hcEq : c = x₀ (T i j) := by
      apply hdiag (x₀ (T i j)) c ?_ (fun n ↦ ((hC₀ _).2.2.1 hc n).trans (hαγ 7))
      intro n
      have hfac := (hfactor _ c d hc hd).1 n
      rw [heq] at hfac
      have hst := hstable n
      have ht0 := (hD₀ _).2.2.1 (hy i j).2.1 n
      have ht := dist_triangle ((f ^ n) c) ((f ^ n) ((f ^ m) (bracket (y i j) z)))
        ((f ^ n) (x₀ (T i j)))
      have ht' := dist_triangle ((f ^ n) ((f ^ m) (bracket (y i j) z)))
        ((f ^ n) ((f ^ m) (y i j))) ((f ^ n) (x₀ (T i j)))
      rw [dist_comm ((f ^ n) c) ((f ^ n) ((f ^ m) (bracket (y i j) z)))] at ht
      have ha3 := ha.2.trans_le (min_le_right _ _)
      have h73 := hαmono (show (3 : Fin 8) ≤ 7 by decide)
      have h63 := hαmono (show (3 : Fin 8) ≤ 6 by decide)
      linarith [hαγ 2, hαpos 3]
    rw [hcEq, hfixD _ d hd] at heq
    exact heq ▸ hd
  refine ⟨hsD, ?_⟩
  have habs (j : Fin (k i)) (c : X) (hc : c ∈ V (T i j)) :
      bracket (bracket c ((f ^ m) (y i j))) ((f ^ m) (bracket (y i j) z)) =
        bracket c ((f ^ m) (bracket (y i j) z)) := by
    have hcp : c ∈ wu f (2 * α 5) (x₀ (T i j)) := hV _ hc
    have hdp := hDsmall _ _ (hy i j).2.1
    have hsp := hDsmall _ _ (hsD j)
    have hc0 : dist c (x₀ (T i j)) ≤ 2 * α 5 := hcp 0
    have hd0 : dist ((f ^ m) (y i j)) (x₀ (T i j)) ≤ α 7 :=
      (hD₀ _).2.2.1 (hy i j).2.1 0
    have hs0 : dist ((f ^ m) (bracket (y i j) z)) (x₀ (T i j)) ≤ α 7 :=
      (hD₀ _).2.2.1 (hsD j) 0
    have h75 := hαmono (show (5 : Fin 8) ≤ 7 by decide)
    have hcd : dist c ((f ^ m) (y i j)) ≤ α 3 := by
      have hh := dist_triangle c (x₀ (T i j)) ((f ^ m) (y i j))
      rw [dist_comm (x₀ (T i j)) ((f ^ m) (y i j))] at hh
      linarith [hαpos 5]
    have hcs : dist c ((f ^ m) (bracket (y i j) z)) ≤ α 3 := by
      have hh := dist_triangle c (x₀ (T i j)) ((f ^ m) (bracket (y i j) z))
      rw [dist_comm (x₀ (T i j)) ((f ^ m) (bracket (y i j) z))] at hh
      linarith [hαpos 5]
    have hbs := hVs _ _ hdp ⟨c, hc, _, rfl, rfl⟩
    have hb0 : dist (bracket c ((f ^ m) (y i j))) ((f ^ m) (y i j)) ≤ 2 * α 5 := hbs 0
    have houter : dist (bracket c ((f ^ m) (y i j))) ((f ^ m) (bracket (y i j) z)) ≤ α 3 := by
      have ht := dist_triangle (bracket c ((f ^ m) (y i j))) ((f ^ m) (y i j))
        ((f ^ m) (bracket (y i j) z))
      have ht' := dist_triangle ((f ^ m) (y i j)) (x₀ (T i j))
        ((f ^ m) (bracket (y i j) z))
      rw [dist_comm (x₀ (T i j)) ((f ^ m) (bracket (y i j) z))] at ht'
      linarith [hαpos 5]
    apply bracket_absorb_left f γ ε (α 2 / 3) (α 3) bracket hγ.le hε.le
      (by linarith [hαpos 2]) (by linarith [hαγ 2]) hbracket_unique
      (fun p q hpq ↦ (hmod (α 2 / 3) (div_pos (hαpos 2) (by norm_num))
        (by linarith [hαγ 2])).2 p q (hpq.trans (by
          have he3 : 3 * α 3 < εmod (α 2 / 3) := hscaleMod 2
          linarith [hαpos 3]))) c _ _ hcs hcd houter
  have hpoint (j : Fin (k i)) (c : X) (hc : c ∈ V (T i j)) :
      (f ^ m) (bracket ((f ^ m).symm (bracket c ((f ^ m) (y i j)))) z) =
        bracket c ((f ^ m) (bracket (y i j) z)) := by
    have hv : (f ^ m).symm (bracket c ((f ^ m) (y i j))) ∈ B i :=
      mem_iUnion.mpr ⟨j, _, ⟨c, hc, _, rfl, rfl⟩, rfl⟩
    have htarget := hVs _ _ (hDsmall _ _ (hy i j).2.1) ⟨c, hc, _, rfl, rfl⟩
    have hh := scaledSliceCovariance f lam γ ε bracket εmod α hlam hγ hε
      hα0 hαpos hαdesc hαrec hfact_s hfact_u hbracket_unique hmod
      (x₀ i) ((f ^ m).symm (bracket c ((f ^ m) (y i j)))) (y i j) z m
      (hB i hv) (hy i j).1 hz (by
        rw [Homeomorph.apply_symm_apply]
        exact fun n ↦ (htarget n).trans (by linarith [hαpos 5]))
    rw [Homeomorph.apply_symm_apply, habs j c hc] at hh
    exact hh
  refine ⟨?_, hpoint⟩
  ext q
  constructor
  · rintro ⟨p, ⟨v, hv, z', hz', rfl⟩, rfl⟩
    have hz' : z' = z := hz'
    subst z'
    obtain ⟨j, p, ⟨c, hc, d, hd, rfl⟩, rfl⟩ := mem_iUnion.mp hv
    have hd : d = (f ^ m) (y i j) := hd
    subst d
    exact mem_iUnion.mpr ⟨j, c, hc, _, rfl, (hpoint j c hc).symm⟩
  · intro hq
    obtain ⟨j, c, hc, d, hd, rfl⟩ := mem_iUnion.mp hq
    have hd : d = (f ^ m) (bracket (y i j) z) := hd
    subst d
    refine ⟨bracket ((f ^ m).symm (bracket c ((f ^ m) (y i j)))) z,
      ⟨_, mem_iUnion.mpr ⟨j, _, ⟨c, hc, _, rfl, rfl⟩, rfl⟩, z, rfl, rfl⟩, hpoint j c hc⟩

private theorem finiteStageBounds
    {X I : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [Fintype I] [Nonempty I]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x₀ : I → X) (C₀ D₀ : I → Set X)
    (hC₀ : ∀ i, (C₀ i).Nonempty ∧ IsCompact (C₀ i) ∧ C₀ i ⊆ wu f (α 7) (x₀ i) ∧
      C₀ i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C₀ i)) ∧
      x₀ i ∈ ri (wu f γ (x₀ i)) (C₀ i))
    (hD₀ : ∀ i, (D₀ i).Nonempty ∧ IsCompact (D₀ i) ∧ D₀ i ⊆ ws f (α 7) (x₀ i) ∧
      D₀ i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D₀ i)) ∧
      x₀ i ∈ ri (ws f γ (x₀ i)) (D₀ i))
    (hproper₀ : ∀ i, proper bracket (α 3) (bi bracket (C₀ i) (D₀ i)))
    (hcover₀ : (univ : Set X) ⊆ ⋃ i, interior (bi bracket (C₀ i) (D₀ i)))
    (hdiam₀ : ∀ i, Metric.diam (bi bracket (C₀ i) (D₀ i)) < α 5 / 2)
    (hseed_u : ∀ i y, y ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (C₀ i) {y} ⊆ wu f (α 5) y)
    (hseed_s : ∀ i y, y ∈ wu f (2 * α 5) (x₀ i) →
      bi bracket {y} (D₀ i) ⊆ ws f (α 5) y)
    (a : ℝ) (ha : 0 < a ∧ a < min γ (α 3)) (F : X → I)
    (hFmem : ∀ x, x ∈ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFs : ∀ x z, z ∈ wu f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      ws f a z ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFu : ∀ x y, y ∈ ws f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      wu f a y ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (m : ℕ) (hm : 1 ≤ m)
    (hsum : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) 
    (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X)
    (hy : ∀ i j, y i j ∈ wu f (α 5) (x₀ i) ∧ (f ^ m) (y i j) ∈ D₀ (T i j) ∧
      ((f ^ m) '' C₀ i ∩ bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}).Nonempty ∧
      ∀ z, z ∈ wu f γ ((f ^ m) (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
        ws f a z ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j)))
    (hcover : ∀ i, (f ^ m) '' C₀ i ⊆
      ⋃ j, bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}) :
    let Cn := stage (f ^ m) bracket C₀ k T y
    (∀ n i, Cn n i ⊆ wu f (2 * α 5) (x₀ i)) ∧
    (∀ n i z, z ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (Cn n i) {z} ⊆
        wu f ((∑ j ∈ Finset.range (n + 1), (lam ^ m) ^ j) * α 5) z) ∧
    (∀ n, 1 ≤ n → ∀ i z, z ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (Cn (n - 1) i) {z} ⊆ bi bracket (Cn n i) {z} ∧
      bi bracket (Cn n i) {z} ⊆ pu (wu f) ((lam ^ m) ^ n * α 5)
        (bi bracket (Cn (n - 1) i) {z}) ∧
      pu (wu f) ((lam ^ m) ^ n * α 5) (bi bracket (Cn (n - 1) i) {z}) ⊆
        wu f ((∑ j ∈ Finset.range (n + 1), (lam ^ m) ^ j) * α 5) z) := by
  classical
  let Cn := stage (f ^ m) bracket C₀ k T y
  let ρ := fun n : ℕ ↦ (∑ j ∈ Finset.range (n + 1), (lam ^ m) ^ j) * α 5
  have hαmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hαγ : ∀ j, α j ≤ γ := fun j ↦ hα0 ▸ hαmono (Fin.zero_le j)
  have h10 : 9 * α 1 < γ := by
    have hh := (hαrec 0).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num [hα0] at hh
    linarith
  have haγ : a < γ / 2 := by
    have ha3 := ha.2.trans_le (min_le_right _ _)
    have h31 := hαmono (show (1 : Fin 8) ≤ 3 by decide)
    linarith [hαpos 1]
  obtain ⟨hβ0, hβhalf, hβa, hpartial⟩ :=
    enlargement_numeric_bounds lam γ a hlam hγ ha.1 haγ m hm hsum
  have hρsmall (n : ℕ) : ρ n ≤ 2 * α 5 := by
    dsimp [ρ]
    nlinarith [hpartial n, hαpos 5]
  have hρnonneg (n : ℕ) : 0 ≤ ρ n :=
    mul_nonneg (Finset.sum_nonneg fun j _ ↦ pow_nonneg hβ0.le _) (hαpos 5).le
  have hρsucc (n : ℕ) : ρ (n + 1) = ρ n + (lam ^ m) ^ (n + 1) * α 5 := by
    simp only [ρ, Finset.sum_range_succ, add_mul]
  have h2γ : 2 * α 5 ≤ γ := by
    have h51 := hαmono (show (1 : Fin 8) ≤ 5 by decide)
    linarith [hαpos 1]
  have hDsmall (i : I) (d : X) (hd : d ∈ D₀ i) : d ∈ ws f (2 * α 5) (x₀ i) :=
    fun n ↦ ((hD₀ i).2.2.1 hd n).trans (by
      have hh := hαmono (show (5 : Fin 8) ≤ 7 by decide)
      linarith [hαpos 5])
  have hmono := stage_monotone (f ^ m) bracket C₀ k T y hcover
  have hstep := enlargementStep f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hy
  have hmain : ∀ n,
      (∀ i, Cn n i ⊆ wu f (2 * α 5) (x₀ i)) ∧
      (∀ i z, z ∈ ws f (2 * α 5) (x₀ i) →
        bi bracket (Cn n i) {z} ⊆ wu f (ρ n) z) ∧
      (1 ≤ n → ∀ i z, z ∈ ws f (2 * α 5) (x₀ i) →
        bi bracket (Cn n i) {z} ⊆ pu (wu f) ((lam ^ m) ^ n * α 5)
          (bi bracket (Cn (n - 1) i) {z})) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
        refine ⟨?_, ?_, by omega⟩
        · intro i c hc t
          exact ((hC₀ i).2.2.1 hc t).trans (by
            have hh := hαmono (show (5 : Fin 8) ≤ 7 by decide)
            linarith [hαpos 5])
        · intro i z hz
          simpa [Cn, stage, ρ] using hseed_u i z hz
      | succ n =>
        obtain ⟨hbase, hradius, hinc⟩ := ih n (by omega)
        have hsl (i : I) (z : X) (hz : z ∈ ws f (2 * α 5) (x₀ i)) :
            bi bracket (Cn n i) {z} ⊆ wu f (2 * α 5) z :=
          fun p hp t ↦ (hradius i z hz hp t).trans (hρsmall n)
        obtain ⟨hnextbase, hnextslice⟩ := hstep (Cn n) hbase hsl
        have hnextinc (i : I) (z : X) (hz : z ∈ ws f (2 * α 5) (x₀ i)) :
            bi bracket (Cn (n + 1) i) {z} ⊆
              pu (wu f) ((lam ^ m) ^ (n + 1) * α 5) (bi bracket (Cn n i) {z}) := by
          intro p hp
          have htransport := (hnextslice i z hz).2.1
          have hpt : (f ^ m) p ∈ ⋃ j,
              bi bracket (Cn n (T i j)) {(f ^ m) (bracket (y i j) z)} := by
            rw [← htransport]
            exact ⟨p, hp, rfl⟩
          obtain ⟨j, hj⟩ := mem_iUnion.mp hpt
          let s := (f ^ m) (bracket (y i j) z)
          have hsD : s ∈ D₀ (T i j) := (hnextslice i z hz).1 j
          have hs := hDsmall _ _ hsD
          cases n with
          | zero =>
            obtain ⟨v, hvA, hvB⟩ := (hy i j).2.2.1
            obtain ⟨v₀, hv₀, hvEq⟩ := hvA
            obtain ⟨c, hc, d, hd, hcEq⟩ := hvB
            have hd : d = (f ^ m) (y i j) := hd
            subst d
            have hvpre : (f ^ m).symm (bracket c ((f ^ m) (y i j))) = v₀ := by
              rw [hcEq, ← hvEq, Homeomorph.symm_apply_apply]
            have hanchor := (hnextslice i z hz).2.2 j c hc
            rw [hvpre] at hanchor
            have hpA : (f ^ m) p ∈ bi bracket (C₀ (T i j)) (D₀ (T i j)) := by
              obtain ⟨c', hc', d', hd', he'⟩ := hj
              have hd' : d' = s := hd'
              exact ⟨c', hc', d', hd'.symm ▸ hsD, he'⟩
            have hvA : (f ^ m) (bracket v₀ z) ∈ bi bracket (C₀ (T i j)) (D₀ (T i j)) :=
              ⟨c, hc, s, hsD, hanchor.symm⟩
            have hdist : dist ((f ^ m) p) ((f ^ m) (bracket v₀ z)) ≤ α 5 := by
              have hh := Metric.dist_le_diam_of_mem (hproper₀ (T i j)).2.1.isBounded hpA hvA
              linarith [hdiam₀ (T i j), hαpos 5]
            have hqU := hseed_u (T i j) s hs hj
            have hvU := hseed_u (T i j) s hs
              (show (f ^ m) (bracket v₀ z) ∈ bi bracket (C₀ (T i j)) {s} from
                ⟨c, hc, s, rfl, hanchor.symm⟩)
            have hpv : (f ^ m) p ∈ wu f (α 5) ((f ^ m) (bracket v₀ z)) := by
              intro t
              have hh := hfact_u s ((f ^ m) p) ((f ^ m) (bracket v₀ z)) t
                (fun t ↦ (hqU t).trans (by linarith [hαγ 5, hαpos 5]))
                (fun t ↦ (hvU t).trans (by linarith [hαγ 5, hαpos 5]))
              exact hh.trans ((mul_le_of_le_one_left dist_nonneg
                (pow_le_one₀ hlam.1.le hlam.2.le)).trans hdist)
            have hback := unstable_pullback_radius f lam γ (α 5) ⟨hlam.1.le, hlam.2.le⟩
              hγ.le (hαγ 5) hfact_u hpv m
            refine ⟨bracket v₀ z, ⟨v₀, hv₀, z, rfl, rfl⟩, ?_⟩
            simpa only [Homeomorph.symm_apply_apply, Nat.zero_add, pow_one] using hback
          | succ t =>
            obtain ⟨q, hq, hpq⟩ := hinc (by omega) (T i j) s hs hj
            obtain ⟨hbprev, hrprev, _⟩ := ih t (by omega)
            have hslprev (i : I) (z : X) (hz : z ∈ ws f (2 * α 5) (x₀ i)) :
                bi bracket (Cn t i) {z} ⊆ wu f (2 * α 5) z :=
              fun p hp n ↦ (hrprev i z hz hp n).trans (hρsmall t)
            have hprevtrans : (f ^ m) '' bi bracket (Cn (t + 1) i) {z} =
                ⋃ j, bi bracket (Cn t (T i j)) {(f ^ m) (bracket (y i j) z)} :=
              ((hstep (Cn t) hbprev hslprev).2 i z hz).2.1
            have hq' : q ∈ (f ^ m) '' bi bracket (Cn (t + 1) i) {z} := by
              rw [hprevtrans]
              exact mem_iUnion.mpr ⟨j, hq⟩
            obtain ⟨q₀, hq₀, rfl⟩ := hq'
            have hrγ : (lam ^ m) ^ (t + 1) * α 5 ≤ γ := by
              have hh := pow_le_one₀ hβ0.le (by linarith : lam ^ m ≤ 1) (n := t + 1)
              exact (mul_le_of_le_one_left (hαpos 5).le hh).trans (hαγ 5)
            have hback := unstable_pullback_radius f lam γ ((lam ^ m) ^ (t + 1) * α 5)
              ⟨hlam.1.le, hlam.2.le⟩ hγ.le hrγ hfact_u hpq m
            refine ⟨q₀, hq₀, ?_⟩
            simpa only [Homeomorph.symm_apply_apply, pow_succ, mul_assoc, mul_left_comm,
              mul_comm] using hback
        refine ⟨hnextbase, ?_, fun _ i z hz ↦ by simpa using hnextinc i z hz⟩
        intro i z hz p hp
        have hh := pu_unstable_subset f (hradius i z hz) (hρnonneg n)
          (mul_nonneg (pow_nonneg hβ0.le _) (hαpos 5).le) (hnextinc i z hz hp)
        simpa only [hρsucc] using hh
  refine ⟨fun n ↦ (hmain n).1, fun n ↦ (hmain n).2.1, ?_⟩
  intro n hn i z hz
  refine ⟨?_, (hmain n).2.2 hn i z hz, ?_⟩
  · rintro p ⟨c, hc, d, hd, he⟩
    exact ⟨c, hmono i (by omega) hc, d, hd, he⟩
  · have hh := pu_unstable_subset f ((hmain (n - 1)).2.1 i z hz) (hρnonneg (n - 1))
      (mul_nonneg (pow_nonneg hβ0.le n) (hαpos 5).le)
    have hn' : n = n - 1 + 1 := by omega
    have heq : ρ (n - 1) + (lam ^ m) ^ n * α 5 = ρ n := by
      conv_rhs => rw [hn', hρsucc]
      rw [← hn']
    simpa only [heq] using hh

private theorem finiteStageRegular
    {X I : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [Fintype I] [Nonempty I]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x₀ : I → X) (C₀ D₀ : I → Set X)
    (hC₀ : ∀ i, (C₀ i).Nonempty ∧ IsCompact (C₀ i) ∧ C₀ i ⊆ wu f (α 7) (x₀ i) ∧
      C₀ i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C₀ i)) ∧
      x₀ i ∈ ri (wu f γ (x₀ i)) (C₀ i))
    (hD₀ : ∀ i, (D₀ i).Nonempty ∧ IsCompact (D₀ i) ∧ D₀ i ⊆ ws f (α 7) (x₀ i) ∧
      D₀ i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D₀ i)) ∧
      x₀ i ∈ ri (ws f γ (x₀ i)) (D₀ i))
    (hproper₀ : ∀ i, proper bracket (α 3) (bi bracket (C₀ i) (D₀ i)))
    (hcover₀ : (univ : Set X) ⊆ ⋃ i, interior (bi bracket (C₀ i) (D₀ i)))
    (hdiam₀ : ∀ i, Metric.diam (bi bracket (C₀ i) (D₀ i)) < α 5 / 2)
    (hseed_u : ∀ i y, y ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (C₀ i) {y} ⊆ wu f (α 5) y)
    (hseed_s : ∀ i y, y ∈ wu f (2 * α 5) (x₀ i) →
      bi bracket {y} (D₀ i) ⊆ ws f (α 5) y)
    (a : ℝ) (ha : 0 < a ∧ a < min γ (α 3)) (F : X → I)
    (hFmem : ∀ x, x ∈ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFs : ∀ x z, z ∈ wu f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      ws f a z ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFu : ∀ x y, y ∈ ws f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      wu f a y ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (m : ℕ) (hm : 1 ≤ m)
    (hsum : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) 
    (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X)
    (hy : ∀ i j, y i j ∈ wu f (α 5) (x₀ i) ∧ (f ^ m) (y i j) ∈ D₀ (T i j) ∧
      ((f ^ m) '' C₀ i ∩ bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}).Nonempty ∧
      ∀ z, z ∈ wu f γ ((f ^ m) (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
        ws f a z ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j)))
    (hcover : ∀ i, (f ^ m) '' C₀ i ⊆
      ⋃ j, bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}) :
    let Cn := stage (f ^ m) bracket C₀ k T y
    (∀ n i, IsCompact (Cn n i) ∧ Cn n i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (Cn n i))) ∧
    (∀ n i z, z ∈ ws f (2 * α 5) (x₀ i) →
      IsCompact (bi bracket (Cn n i) {z}) ∧
      bi bracket (Cn n i) {z} = rc (wu f γ z) (ri (wu f γ z) (bi bracket (Cn n i) {z}))) := by
  classical
  let Cn := stage (f ^ m) bracket C₀ k T y
  have hbounds := finiteStageBounds f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hy hcover
  have hslice := compactRegularSlice f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
  have hαmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hαγ : ∀ j, α j ≤ γ := fun j ↦ hα0 ▸ hαmono (Fin.zero_le j)
  have h10 : 9 * α 1 < γ := by
    have hh := (hαrec 0).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num [hα0] at hh
    linarith
  have h2γ : 2 * α 5 < γ := by
    have hh := hαmono (show (1 : Fin 8) ≤ 5 by decide)
    linarith [hαpos 1]
  have haγ : a < γ / 2 := by
    have ha3 := ha.2.trans_le (min_le_right _ _)
    have hh := hαmono (show (1 : Fin 8) ≤ 3 by decide)
    linarith [hαpos 1]
  have hpartial := (enlargement_numeric_bounds lam γ a hlam hγ ha.1 haγ m hm hsum).2.2.2
  have hDsmall (i : I) (d : X) (hd : d ∈ D₀ i) : d ∈ ws f (2 * α 5) (x₀ i) :=
    fun n ↦ ((hD₀ i).2.2.1 hd n).trans (by
      have hh := hαmono (show (5 : Fin 8) ≤ 7 by decide)
      linarith [hαpos 5])
  have hslbound (n : ℕ) (i : I) (z : X) (hz : z ∈ ws f (2 * α 5) (x₀ i)) :
      bi bracket (Cn n i) {z} ⊆ wu f (2 * α 5) z := by
    intro q hq t
    exact (hbounds.2.1 n i z hz hq t).trans (by nlinarith [hpartial n, hαpos 5])
  have hmain : ∀ n i, IsCompact (Cn n i) ∧
      Cn n i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (Cn n i)) := by
    intro n
    induction n with
    | zero => exact fun i ↦ ⟨(hC₀ i).2.1, (hC₀ i).2.2.2.1⟩
    | succ n ih =>
      intro i
      let B := fun j : Fin (k i) ↦ (f ^ m).symm ''
        bi bracket (Cn n (T i j)) {(f ^ m) (y i j)}
      have hb (j : Fin (k i)) := hslice (x₀ (T i j)) ((f ^ m) (y i j))
        (hDsmall _ _ (hy i j).2.1) (Cn n (T i j))
        (hbounds.1 n (T i j)) (ih (T i j)).1 (ih (T i j)).2
      have hBc (j : Fin (k i)) : IsCompact (B j) :=
        (hb j).1.image (f ^ m).symm.continuous
      have hBr (j : Fin (k i)) : B j = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (B j)) := by
        apply unstable_pullback_regular f γ lam (2 * α 5) hγ ⟨hlam.1.le, hlam.2.le⟩
          h2γ hfact_u ((f ^ m) (y i j)) (x₀ i)
          (bi bracket (Cn n (T i j)) {(f ^ m) (y i j)}) m
          (hslbound n _ _ (hDsmall _ _ (hy i j).2.1)) ?_ (hb j).1 (hb j).2.1
        intro q hq
        exact hbounds.1 (n + 1) i (mem_iUnion.mpr ⟨j, hq⟩)
      exact regular_finite_union (wu f γ (x₀ i))
        (BowenRegularClosedPreparation.isClosed_stable f.symm γ (x₀ i)) B hBc hBr
  refine ⟨hmain, ?_⟩
  intro n i z hz
  have hh := hslice (x₀ i) z hz (Cn n i) (hbounds.1 n i) (hmain n i).1 (hmain n i).2
  exact ⟨hh.1, hh.2.1⟩

private theorem limitFactorSharpBound
    {X I : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [Fintype I] [Nonempty I]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x₀ : I → X) (C₀ D₀ : I → Set X)
    (hC₀ : ∀ i, (C₀ i).Nonempty ∧ IsCompact (C₀ i) ∧ C₀ i ⊆ wu f (α 7) (x₀ i) ∧
      C₀ i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C₀ i)) ∧
      x₀ i ∈ ri (wu f γ (x₀ i)) (C₀ i))
    (hD₀ : ∀ i, (D₀ i).Nonempty ∧ IsCompact (D₀ i) ∧ D₀ i ⊆ ws f (α 7) (x₀ i) ∧
      D₀ i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D₀ i)) ∧
      x₀ i ∈ ri (ws f γ (x₀ i)) (D₀ i))
    (hproper₀ : ∀ i, proper bracket (α 3) (bi bracket (C₀ i) (D₀ i)))
    (hcover₀ : (univ : Set X) ⊆ ⋃ i, interior (bi bracket (C₀ i) (D₀ i)))
    (hdiam₀ : ∀ i, Metric.diam (bi bracket (C₀ i) (D₀ i)) < α 5 / 2)
    (hseed_u : ∀ i y, y ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (C₀ i) {y} ⊆ wu f (α 5) y)
    (hseed_s : ∀ i y, y ∈ wu f (2 * α 5) (x₀ i) →
      bi bracket {y} (D₀ i) ⊆ ws f (α 5) y)
    (a : ℝ) (ha : 0 < a ∧ a < min γ (α 3)) (F : X → I)
    (hFmem : ∀ x, x ∈ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFs : ∀ x z, z ∈ wu f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      ws f a z ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFu : ∀ x y, y ∈ ws f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      wu f a y ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (m : ℕ) (hm : 1 ≤ m)
    (hsum : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) 
    (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X)
    (hy : ∀ i j, y i j ∈ wu f (α 5) (x₀ i) ∧ (f ^ m) (y i j) ∈ D₀ (T i j) ∧
      ((f ^ m) '' C₀ i ∩ bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}).Nonempty ∧
      ∀ z, z ∈ wu f γ ((f ^ m) (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
        ws f a z ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j)))
    (hcover : ∀ i, (f ^ m) '' C₀ i ⊆
      ⋃ j, bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}) :
    ∀ i, rc (wu f γ (x₀ i)) (⋃ n, stage (f ^ m) bracket C₀ k T y n i) ⊆
      wu f ((3 / 2) * α 5) (x₀ i) := by
  have hbounds := finiteStageBounds f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hy hcover
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have h10 : 9 * α 1 < γ := by
    have hh := (hαrec 0).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num [hα0] at hh
    linarith
  have haγ : a < γ / 2 := by
    have ha3 := ha.2.trans_le (min_le_right _ _)
    have hh := hmono (show (1 : Fin 8) ≤ 3 by decide)
    linarith [hαpos 1]
  have hpartial := (enlargement_numeric_bounds lam γ a hlam hγ ha.1 haγ m hm hsum).2.2.2
  have h2γ : 2 * α 5 ≤ γ := by
    have hh := hmono (show (1 : Fin 8) ≤ 5 by decide)
    linarith [hαpos 1]
  have hseed (i : I) : C₀ i ⊆ wu f (α 5) (x₀ i) :=
    fun c hc n ↦ ((hC₀ i).2.2.1 hc n).trans (hmono (by decide))
  have hsl := stage_base_radius f lam γ (α 5) ⟨hlam.1.le, hlam.2.le⟩ hγ.le hfact_u
    bracket C₀ k T y x₀ m hseed (fun i j ↦ (hy i j).1)
    (fun n ↦ by nlinarith [hpartial n, hαpos 5])
    (fun n i j ↦ hbounds.2.1 n (T i j) ((f ^ m) (y i j)) (fun t ↦
      ((hD₀ _).2.2.1 (hy i j).2.1 t).trans (by
        have hh := hmono (show (5 : Fin 8) ≤ 7 by decide)
        linarith [hαpos 5])))
  intro i
  apply rc_subset_closed _ _ _ (BowenRegularClosedPreparation.isClosed_stable f.symm _ _)
  apply iUnion_subset
  intro n c hc t
  exact (hsl n i hc t).trans (by nlinarith [hpartial n, hαpos 5])

private theorem limitSliceTransport
    {X I : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [Fintype I] [Nonempty I]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x₀ : I → X) (C₀ D₀ : I → Set X)
    (hC₀ : ∀ i, (C₀ i).Nonempty ∧ IsCompact (C₀ i) ∧ C₀ i ⊆ wu f (α 7) (x₀ i) ∧
      C₀ i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C₀ i)) ∧
      x₀ i ∈ ri (wu f γ (x₀ i)) (C₀ i))
    (hD₀ : ∀ i, (D₀ i).Nonempty ∧ IsCompact (D₀ i) ∧ D₀ i ⊆ ws f (α 7) (x₀ i) ∧
      D₀ i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D₀ i)) ∧
      x₀ i ∈ ri (ws f γ (x₀ i)) (D₀ i))
    (hproper₀ : ∀ i, proper bracket (α 3) (bi bracket (C₀ i) (D₀ i)))
    (hcover₀ : (univ : Set X) ⊆ ⋃ i, interior (bi bracket (C₀ i) (D₀ i)))
    (hdiam₀ : ∀ i, Metric.diam (bi bracket (C₀ i) (D₀ i)) < α 5 / 2)
    (hseed_u : ∀ i y, y ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (C₀ i) {y} ⊆ wu f (α 5) y)
    (hseed_s : ∀ i y, y ∈ wu f (2 * α 5) (x₀ i) →
      bi bracket {y} (D₀ i) ⊆ ws f (α 5) y)
    (a : ℝ) (ha : 0 < a ∧ a < min γ (α 3)) (F : X → I)
    (hFmem : ∀ x, x ∈ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFs : ∀ x z, z ∈ wu f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      ws f a z ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFu : ∀ x y, y ∈ ws f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      wu f a y ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (m : ℕ) (hm : 1 ≤ m)
    (hsum : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) 
    (k : I → ℕ) (T : (i : I) → Fin (k i) → I)
    (y : (i : I) → Fin (k i) → X)
    (hy : ∀ i j, y i j ∈ wu f (α 5) (x₀ i) ∧ (f ^ m) (y i j) ∈ D₀ (T i j) ∧
      ((f ^ m) '' C₀ i ∩ bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}).Nonempty ∧
      ∀ z, z ∈ wu f γ ((f ^ m) (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
        ws f a z ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j)))
    (hcover : ∀ i, (f ^ m) '' C₀ i ⊆
      ⋃ j, bi bracket (C₀ (T i j)) {(f ^ m) (y i j)}) :
    let C := fun i ↦ rc (wu f γ (x₀ i)) (⋃ n, stage (f ^ m) bracket C₀ k T y n i)
    ∀ i z, z ∈ ws f (2 * α 5) (x₀ i) →
      (∀ j, (f ^ m) (bracket (y i j) z) ∈ D₀ (T i j)) ∧
      (f ^ m) '' bi bracket (C i) {z} =
        ⋃ j, bi bracket (C (T i j)) {(f ^ m) (bracket (y i j) z)} := by
  let Cn := stage (f ^ m) bracket C₀ k T y
  let C := fun i ↦ rc (wu f γ (x₀ i)) (⋃ n, Cn n i)
  have hbounds := finiteStageBounds f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hy hcover
  have hregular := finiteStageRegular f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hy hcover
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have h10 : 9 * α 1 < γ := by
    have hh := (hαrec 0).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num [hα0] at hh
    linarith
  have haγ : a < γ / 2 := by
    have ha3 := ha.2.trans_le (min_le_right _ _)
    have hh := hmono (show (1 : Fin 8) ≤ 3 by decide)
    linarith [hαpos 1]
  have hpartial := (enlargement_numeric_bounds lam γ a hlam hγ ha.1 haγ m hm hsum).2.2.2
  have h2γ : 2 * α 5 ≤ γ := by
    have hh := hmono (show (1 : Fin 8) ≤ 5 by decide)
    linarith [hαpos 1]
  have hprops (i : I) := limitFactorProperties f γ (2 * α 5) h2γ (x₀ i) (fun n ↦ Cn n i)
    (fun n ↦ hbounds.1 n i) (fun n ↦ (hregular.1 n i).2)
  have hDsmall (i : I) (d : X) (hd : d ∈ D₀ i) : d ∈ ws f (2 * α 5) (x₀ i) :=
    fun n ↦ ((hD₀ i).2.2.1 hd n).trans (by
      have hh := hmono (show (5 : Fin 8) ≤ 7 by decide)
      linarith [hαpos 5])
  have hslbound (n : ℕ) (i : I) (z : X) (hz : z ∈ ws f (2 * α 5) (x₀ i)) :
      bi bracket (Cn n i) {z} ⊆ wu f (2 * α 5) z := by
    intro q hq t
    exact (hbounds.2.1 n i z hz hq t).trans (by nlinarith [hpartial n, hαpos 5])
  have hstep (n : ℕ) := enlargementStep f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hy (Cn n) (hbounds.1 n) (hslbound n)
  have hclosure (i : I) (z : X) (hz : z ∈ ws f (2 * α 5) (x₀ i)) :
      bi bracket (C i) {z} = closure (⋃ n, bi bracket (Cn n i) {z}) := by
    have hcont := (compactRegularSlice f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
      hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
      (x₀ i) z hz (C i) (hprops i).2.2.1 (hprops i).1 (hprops i).2.2.2.1).2.2
    exact slice_closure_union bracket (fun n ↦ Cn n i) (C i) z
      (hprops i).2.2.2.2 (hprops i).1 hcont
  dsimp [C]
  intro i z hz
  have hsD := ((hstep 0).2 i z hz).1
  refine ⟨hsD, ?_⟩
  exact finiteToLimitTransport (f ^ m) (fun n ↦ bi bracket (Cn n i) {z})
    (fun j n ↦ bi bracket (Cn n (T i j)) {(f ^ m) (bracket (y i j) z)})
    (bi bracket (C i) {z}) (fun j ↦ bi bracket (C (T i j)) {(f ^ m) (bracket (y i j) z)})
    (by simpa using (hbounds.2.2 1 (by omega) i z hz).1)
    (hclosure i z hz) (fun j ↦ hclosure (T i j) _ (hDsmall _ _ (hsD j)))
    (fun n ↦ ((hstep n).2 i z hz).2.1)

/-- Bowen's collar argument, with transport supplied for the completed factors. -/
private theorem collarFromTransport
    {X I : Type*} [MetricSpace X] (f : X ≃ₜ X) (lam γ ε : ℝ)
    (b : X → X → X) (εmod : ℝ → ℝ) (hlam : 0 < lam ∧ lam < 1)
    (hγ : 0 < γ) (hε : 0 < ε)
    (hs : ∀ x y z n, y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hu : ∀ x y z n, y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hun : ∀ x y z, dist x y ≤ ε → z ∈ ws f γ x → z ∈ wu f γ y → z = b x y)
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → b x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (x : I → X) (C D : I → Set X)
    (hC : ∀ i, C i ⊆ wu f (2 * α 5) (x i))
    (hD : ∀ i, D i ⊆ ws f (2 * α 5) (x i))
    (hxC : ∀ i, x i ∈ C i) (hxD : ∀ i, x i ∈ D i)
    (hmesh : ∀ i, ∀ u ∈ bi b (C i) (D i), ∀ v ∈ bi b (C i) (D i), dist u v < α 4)
    (hrect : ∀ i, ∀ u ∈ bi b (C i) (D i), ∀ v ∈ bi b (C i) (D i),
      b u v ∈ bi b (C i) (D i))
    (a : ℝ) (ha : a < α 3) (F : X → I)
    (hFmem : ∀ q, q ∈ bi b (C (F q)) (D (F q)))
    (hFs : ∀ q, ws f a q ⊆ bi b (C (F q)) (D (F q)))
    (m : ℕ) (hβ : lam ^ m * γ < a)
    (htrans : ∀ i z, z ∈ bi b (C i) (ws f (2 * α 5) (x i)) →
      ∃ j, (f ^ m) z ∈ bi b (C j) (D j) ∧
        bi b (C j) {(f ^ m) z} ⊆ (f ^ m) '' bi b (C i) {z}) :
    ∀ i q, dist q (x i) < 3 * α 4 → b q (x i) ∈ C i →
      ∃ j, (∃ t, (bi b (C j) (D j) ∩ bi b (C t) (D t)).Nonempty ∧
          (f ^ m) q ∈ bi b (C t) (D t)) ∧
        (f ^ m) q ∈ bi b (C j) {(f ^ m) q} ∧
        bi b (C j) {(f ^ m) q} ⊆ (f ^ m) '' bi b (C i) {q} ∧
        (f ^ m).symm '' ri (wu f γ ((f ^ m) q)) (bi b (C j) {(f ^ m) q}) ⊆
          ri (wu f γ q) (bi b (C i) {q}) := by
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have hag (i : Fin 8) : α i ≤ γ := by simpa only [hα0] using hmono (show 0 ≤ i by omega)
  have hscale (i : Fin 7) : 9 * α i.succ < α i.castSucc := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have hsm (i : Fin 7) : 3 * α i.succ < εmod (α i.castSucc / 3) := by
    have hh := (hαrec i).trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    linarith
  have h54 : 9 * α 5 < α 4 := hscale 4
  have h43 : 9 * α 4 < α 3 := hscale 3
  have h32 : 9 * α 3 < α 2 := hscale 2
  have hb (i : Fin 7) (u v : X) (hd : dist u v ≤ 3 * α i.succ) :
      b u v ∈ ws f (α i.castSucc / 3) u ∩ wu f (α i.castSucc / 3) v :=
    (hmod _ (div_pos (hαpos _) (by norm_num)) (by linarith [hag i.castSucc])).2
      u v (hd.trans (hsm i).le)
  have hself (i : I) (u v : X) (huC : u ∈ C i) (hvC : v ∈ C i) : b u v = u := by
    apply smallUnstableBracketSelf f γ ε (α 3 / 3) (2 * α 5) b hγ.le hε.le
      (by linarith [hαpos 5]) (by linarith [hag 3, hαpos 5]) hun
      (fun p q hpq ↦ hb 3 p q (by norm_num; linarith [hαpos 5])) (x i) u v
      (hC i huC) (hC i hvC)
  have hCmem (i : I) (u : X) (huC : u ∈ C i) : u ∈ bi b (C i) (D i) :=
    ⟨u, huC, x i, hxD i, hself i u (x i) huC (hxC i)⟩
  intro i q hqx hvC
  let v := b q (x i)
  have hv : v ∈ C i := hvC
  have hvq : v ∈ ws f (α 3 / 3) q := (hb 3 q (x i) hqx.le).1
  have hvqγ : v ∈ ws f γ q := fun n ↦ (hvq n).trans (by linarith [hag 3])
  have hqself : q ∈ ws f γ q := fun n ↦ by simpa using hγ.le
  have hinput : v ∈ bi b (C i) (ws f (2 * α 5) (x i)) :=
    ⟨v, hv, x i, (fun n ↦ by simpa using (show 0 ≤ 2 * α 5 by linarith [hαpos 5])),
      hself i v (x i) hv (hxC i)⟩
  obtain ⟨j, hj, hji⟩ := htrans i v hinput
  have hsource : bi b (C i) {v} = C i := by
    ext u
    constructor
    · rintro ⟨c, hc, d, hd, he⟩
      have hd' : d = v := hd
      rw [hd', hself i c v hc hv] at he
      exact he ▸ hc
    · intro huC
      exact ⟨u, huC, v, rfl, hself i u v huC hv⟩
  rw [hsource] at hji
  have hvhqγ : (f ^ m) v ∈ ws f γ ((f ^ m) q) := by
    intro n
    simpa only [pow_add, Homeomorph.mul_apply] using hvqγ (n + m)
  have hdvq : dist ((f ^ m) v) ((f ^ m) q) < a :=
    (hs q v q m hvqγ hqself).trans_lt ((mul_le_mul_of_nonneg_left
      (hvqγ 0) (pow_nonneg hlam.1.le m)).trans_lt hβ)
  have hvhq : (f ^ m) v ∈ ws f a ((f ^ m) q) := by
    intro n
    exact (hs _ _ _ n hvhqγ (fun k ↦ by simpa using hγ.le)).trans
      ((mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.1.le hlam.2.le)).trans hdvq.le)
  have hnear : dist ((f ^ m) v) ((f ^ m) q) < α 3 := hdvq.trans ha
  have htarget (c : X) (hc : c ∈ C j) :
      dist c ((f ^ m) q) < α 4 + α 3 :=
    (dist_triangle c ((f ^ m) v) ((f ^ m) q)).trans_lt
      (add_lt_add (hmesh j c (hCmem j c hc) _ hj) hnear)
  have habs (c : X) (hc : c ∈ C j) :
      b (b c ((f ^ m) v)) ((f ^ m) q) = b c ((f ^ m) q) := by
    apply bracket_absorb_left f γ ε (α 1 / 3) (α 2) b hγ.le hε.le
      (by linarith [hαpos 1]) (by linarith [hag 1]) hun
      (fun p t hpt ↦ hb 1 p t (by norm_num; linarith [hαpos 2]))
    · linarith [htarget c hc, hαpos 4]
    · linarith [hmesh j c (hCmem j c hc) _ hj, hαpos 3]
    · have hh := hmesh j (b c ((f ^ m) v)) (hrect j c (hCmem j c hc) _ hj) _ hj
      have ht := dist_triangle (b c ((f ^ m) v)) ((f ^ m) v) ((f ^ m) q)
      linarith [hαpos 4]
  have hinc : bi b (C j) {(f ^ m) q} ⊆ (f ^ m) '' bi b (C i) {q} := by
    rintro t ⟨c, hc, d, hd, rfl⟩
    have hd' : d = (f ^ m) q := hd
    subst d
    obtain ⟨u, huC, he⟩ := hji ⟨c, hc, _, rfl, rfl⟩
    have hendpoint : (f ^ m) u ∈ wu f (α 3 / 3) ((f ^ m) v) := by
      rw [he]
      exact (hb 3 c _ (by
        have hh := hmesh j c (hCmem j c hc) _ hj
        norm_num; linarith [hαpos 4])).2
    have hprefix := forward_distance_of_unstable_endpoint f lam γ (α 3 / 3)
      ⟨hlam.1.le, hlam.2.le⟩ hγ.le hu u v m
      (fun n ↦ (hendpoint n).trans (by linarith [hag 3])) (hendpoint 0)
    have hcov : (f ^ m) (b u q) = b ((f ^ m) u) ((f ^ m) q) := by
      apply finiteBracketCovariance f γ ε (α 1 / 3) (α 2) b hγ.le hε.le
        (by linarith [hαpos 1]) (by linarith [hag 1]) hun
        (fun p t hpt ↦ hb 1 p t (by norm_num; linarith [hαpos 2])) m
      intro n hn
      have hh := dist_triangle ((f ^ n) u) ((f ^ n) v) ((f ^ n) q)
      linarith [hprefix n hn, hvq n, hαpos 3]
    exact ⟨b u q, ⟨u, huC, q, rfl, rfl⟩, by rw [hcov, he, habs c hc]⟩
  have hmem : (f ^ m) q ∈ bi b (C j) {(f ^ m) q} := by
    obtain ⟨c, hc, d, hd, he⟩ := hj
    have hslice : (f ^ m) v ∈ bi b (C j) {d} := ⟨c, hc, d, rfl, he⟩
    have heq := smallSliceAbsorption f γ ε b εmod hγ hε hun hmod α hα0 hαpos hαdesc
      hαrec (x j) d (C j) (hC j) (hD j hd) c hc
    rw [he] at heq
    rw [← heq] at hslice
    obtain ⟨c', hc', d', hd', he'⟩ := hslice
    have hd'' : d' = (f ^ m) v := hd'
    rw [hd''] at he'
    have hfix : b ((f ^ m) v) ((f ^ m) q) = (f ^ m) q := by
      have hh := hb 2 ((f ^ m) v) ((f ^ m) q) (by norm_num; linarith [hαpos 3])
      norm_num at hh
      apply BowenRegularClosedPreparation.diagonal_separation f b hγ.le hε.le
        (fun p z hp hs ht ↦ hun p p z hp hs ht)
      · intro n
        exact (dist_triangle _ ((f ^ n) ((f ^ m) v)) _).trans
          ((add_le_add (hh.1 n) (hvhq n)).trans (by linarith [hag 2, hαpos 3]))
      · exact fun n ↦ (hh.2 n).trans (by linarith [hag 2])
    exact ⟨c', hc', _, rfl, by rw [← habs c' hc', he', hfix]⟩
  refine ⟨j, ⟨F ((f ^ m) q), ⟨(f ^ m) v, hj, hFs _ hvhq⟩, hFmem _⟩, hmem, hinc, ?_⟩
  apply unstableInteriorPullbackSubset f γ lam (α 2 / 3) hγ ⟨hlam.1.le, hlam.2.le⟩
    (by linarith [hag 2, hαpos 2]) hu q _ _ m
  · rintro t ⟨c, hc, d, hd, rfl⟩
    have hd' : d = q := hd
    rw [hd']
    apply (hb 2 c q ?_).2
    have hh := dist_triangle c (x i) q
    rw [dist_comm (x i) q] at hh
    have hc0 : dist c (x i) ≤ 2 * α 5 := hC i hc 0
    norm_num; linarith [hαpos 5]
  · rintro t ⟨c, hc, d, hd, rfl⟩
    have hd' : d = (f ^ m) q := hd
    rw [hd']
    exact (hb 2 c _ (by norm_num; linarith [htarget c hc, hαpos 4])).2
  · exact hinc

/-- Bowen's simultaneous unstable and stable enlargement for every admissible iterate.

Source: Bowen (1970), Lemmas 14-18 pp.732-735 and the collar argument of
Lemma 22 pp.737-738; Fact 1 and scales pp.726-728.

All orbit conditions use the original homeomorphism. The inverse enlargement
uses the same m and the exchanged bracket. Closures and interiors are taken in
the full gamma-plaque subtype, and set-valued plaque neighborhoods are unions.
The bracket is only constrained on the displayed small domains. Empty X and
empty I are excluded exactly as in the statement; empty finite label sets cannot
cover the nonempty seed. No manifold, connectedness or new return-time premise
is imposed. This declaration admits only its proof at the statement stage.

Natural-language proof from the current DAG:

1. Write s=Σ_{k≥1}βᵏ. The hypotheses give βγ<a, β<1/2 and s<a/γ<α₃/γ<1/729<1/2. The exact sum is
β/(1−β). Although the theorem fixes any admissible m, such integers exist: λᵐ→0, and β/(1−β)→0.
Define ρₙ=(1+β+⋯+βⁿ)α and ρ∞=(1+s)α<3α/2. These stronger radii, in addition to the stated weaker 2α
bound, will give the mesh bound.

2. Plaque calculus directly from Fact1: Wδᵘ(x)=Wγᵘ(x)∩closedBall(x,δ), since backward contraction
bounds all later distances by their initial value; similarly stable. Also Wδᵘ(Wηᵘ(x))⊂W_(δ+η)ᵘ(x)
by triangle inequalities at every negative iterate, and h⁻¹Wδᵘ(x)⊂W_(βδ)ᵘ(h⁻¹x) by contraction,
with the forward stable dual. Every plaque is closed as an intersection of closed orbit-distance
conditions. Finally bracket absorption in the small domains follows from intersection uniqueness:
each iterated bracket has the same unstable coordinate of its first surviving argument and stable
coordinate of its last surviving argument, with sums of the small modulus radii strictly below γ.
These facts prove Bowen Lemmas2 and6 in each usage below.

3. Here is the local inverse-openness calculation needed throughout; it does not assert h maps
entire γ-plaques onto entire γ-plaques. Let K⊂W_rᵘ(b), r<γ, with hK contained in W_tᵘ(c), t<γ. Fix
w∈K and a relatively open neighborhood O of hw in Wγᵘ(c). For x∈Wγᵘ(b) near w, the negative target
distances for n≥m obey d(f⁻ⁿhx,f⁻ⁿc)≤t+λ^(n−m)d(x,w)<γ if d(x,w)<γ−t; the finitely many n<m remain
<γ by continuity, because hw∈W_tᵘ(c). Thus locally h maps this source plaque into the target plaque
and the inverse image of O is source relatively open. Conversely for z∈Wγᵘ(c) near hw,
d(f⁻ⁿh⁻¹z,f⁻ⁿb)≤r+λ^(n+m)d(z,hw)<γ for all n≥0, so h⁻¹z lies in the source plaque. The two
restricted maps therefore give a local homeomorphism along K. The same calculation works pointwise
for different centers c on finitely many pieces, and for f⁻¹ with the plaques exchanged. It
transfers dense interiors of compact pieces through h⁻¹ whenever the displayed strict collars have
been established.

4. Fix i and z∈Cᵢ⁰. Put t=F(hz) and Y_z=A_t⁰∩Wγᵘ(hz)=[C_t⁰,hz] by the product-slice theorem.
Saturation with base hz gives W_aᵘ(hz)⊂Y_z, so hz is interior in the full target γ-plaque. All of
Y_z lies within W_(α/2)ᵘ(hz), since its points and hz belong to the seed of diameter<α/2 and
contraction recentering applies. Its inverse lies in W_(βα/2)ᵘ(z), and hence in
W_(α₇+βα/2)ᵘ(xᵢ)⊂Wαᵘ(xᵢ). The local calculation of the preceding step gives a source relative
neighborhood of z in h⁻¹Y_z; these sets are compact closed subsets in the source γ-plaque. Their
interiors form an open cover of compact Cᵢ⁰, so select finitely many zⱼ. Put Tᵢⱼ=F(hzⱼ),
yᵢⱼ=h⁻¹[x_Tᵢⱼ,hzⱼ]. Seed bracket closure puts h(yᵢⱼ) in D_Tᵢⱼ⁰, and the backward estimate puts yᵢⱼ
in Wαᵘ(xᵢ). Absorption gives [C_Tᵢⱼ⁰,h(yᵢⱼ)]=Y_zⱼ. The chosen zⱼ witness intersection and finite
covering. For target z∈Wγᵘ(h(yᵢⱼ))∩A_Tᵢⱼ⁰, the full plaque agrees with the hzⱼ plaque along this
small seed slice by strict-collar triangle estimates; hence z∈Wγᵘ(hzⱼ)∩A_Tᵢⱼ⁰. The assumed
F-saturation at hzⱼ gives W_aˢ(z)⊂A_Tᵢⱼ⁰. This proves every assertion of Lemma14.

5. We inline Bowen Lemma11, rather than using the removed finite-orbit wrapper. (a) If
d(fʳx,fʳy)≤α₂ for 0≤r≤m, put w_r=[fʳx,fʳy]. The modulus puts w_r in both α₁/3 plaques. Then fw_r is
stable-related to fʳ⁺¹x. Its negative unstable iterates relative to fʳ⁺¹y are controlled by the
unstable membership of w_r for n≥1, while n=0 is <γ by the one-step continuity scale α₁. Thus fw_r
belongs to both γ-plaques, and uniqueness gives fw_r=w_(r+1). Induction yields h[x,y]=[hx,hy]. (b)
Suppose V⊂Wα₃ᵘ(z), y∈Wα₃ˢ(z), hV=⋃V_k with V_k⊂Wα₃ᵘ(hz_k) and z_k∈Wα₃ᵘ(z). For w∈V_k, set v=h⁻¹w.
Then d(fʳv,fʳz_k)≤λ^(m−r)α₃<α₂/3; also d(fʳz_k,fʳ[z_k,y])≤α₂/3, by the stable modulus and
2α₃<ε(α₂/3). Therefore (a) applies to v,[z_k,y]. Absorption gives h[v,y]=[w,h[z_k,y]]. Taking
images of all w gives h[V,y]=⋃[V_k,h[z_k,y]]. The identical argument with one piece contained in hV
gives its inclusion version. Only these guarded equalities are used.

6. Define Cᵢⁿ by the stated finite union. Its brackets and source strict collars can be checked
before using covariance: at n=1 every target piece lies in Wαᵘ(hyᵢⱼ), so its inverse lies in
W_(βα)ᵘ(yᵢⱼ)⊂W_(1+β)αᵘ(xᵢ). At n≥2 the induction bound for target slices at the seed point
hyᵢⱼ∈D_Tᵢⱼ⁰ puts the target pieces in W₂αᵘ(hyᵢⱼ); their inverses lie in
W_(2βα)ᵘ(yᵢⱼ)⊂W_(1+2β)αᵘ(xᵢ)⊂W₂αᵘ(xᵢ). Thus V=Cᵢⁿ and the anchor points yᵢⱼ satisfy every α₃ guard
of the previous step. For y∈W₂αˢ(xᵢ), sᵢⱼ(y)=h[yᵢⱼ,y] lies in W_(βγ)ˢ(hyᵢⱼ)⊂W_aˢ(hyᵢⱼ)⊂A_Tᵢⱼ⁰ by
Lemma14(d). Together with hyᵢⱼ∈D_Tᵢⱼ⁰ this puts sᵢⱼ(y) in D_Tᵢⱼ⁰, using the strict γ triangle bound
and the product slice formula. The guarded covariance gives h[Cᵢⁿ,y]=⋃ⱼ[C_Tᵢⱼⁿ⁻¹,sᵢⱼ(y)].

7. For n=1, finite covering gives Cᵢ⁰⊂Cᵢ¹. For each j choose an anchor hz₀∈hCᵢ⁰∩[C_Tᵢⱼ⁰,hyᵢⱼ]. The
preceding covariance puts v=h[z₀,y] in h[Cᵢ⁰,y]∩[C_Tᵢⱼ⁰,sᵢⱼ(y)]. This latter slice is inside the
target seed, so every one of its points lies within Wαᵘ(v), by seed diameter<α/2 and contraction
recentering. Pulling back contracts that unstable displacement to βα. Thus
[Cᵢ⁰,y]⊂[Cᵢ¹,y]⊂W_(βα)ᵘ([Cᵢ⁰,y])⊂W_(1+β)αᵘ(y). For n≥2, apply the already established target stage
increment at sᵢⱼ(y)∈D_Tᵢⱼ⁰⊂W₂αˢ(x_Tᵢⱼ): [C_Tᵢⱼⁿ⁻²,sᵢⱼ]⊂[C_Tᵢⱼⁿ⁻¹,sᵢⱼ]⊂W_(βⁿ⁻¹α)ᵘ([C_Tᵢⱼⁿ⁻²,sᵢⱼ]).
Finite union covariance and backward contraction give the source increment βⁿα and monotonicity.
Triangle inequalities give W_(ρₙ)ᵘ(y). This simultaneous induction over all i proves the entire
displayed recursion estimate with the actual factor βⁿα.

8. The seed slices have dense full-plaque interior by the product-slice and rebase theorems. Each
target piece [C_Tᵢⱼⁿ⁻¹,sᵢⱼ(y)] has dense relative interior by the inductive assertion. Its inverse
and the whole source slice lie in W_(ρₙ)ᵘ(y) with ρₙ<3α/2<γ; the target piece lies in W₂αᵘ(sᵢⱼ(y)),
also a strict γ collar. The local inverse calculation transfers each target interior point to a
source interior point. Its continuity also takes the dense target interiors to dense subsets of the
inverse pieces. A finite union of such closed pieces consequently has dense interior. Taking y=xᵢ
gives the assertion for Cᵢⁿ themselves.

9. The increasing union ⋃ₙCᵢⁿ lies in W_(ρ∞)ᵘ(xᵢ), a closed subset of compact X. Its closure Cᵢ
there is compact and remains in that plaque. Since Cᵢⁿ=closure(int Cᵢⁿ) and each stage interior is
contained in int Cᵢ, the closure of int Cᵢ contains every stage and hence Cᵢ. The reverse
containment follows from closedness; thus Cᵢ is regular closed in the full γ-plaque. For
y∈W₂αˢ(xᵢ), the map [,y] is a homeomorphism on an open plaque neighborhood of all factors by the
rebase theorem, since d(xᵢ,y)≤2α<α₃. Its restriction carries Cᵢ onto the closure of ⋃ₙ[Cᵢⁿ,y]; the
common chart contains these compact strict-collar sets, so relative closures here agree with
full-plaque closures. Continuity of h and h⁻¹ carries their closures to each other. Closure of a
finite union equals the union of the closures (finite union of closed sets is closed, and each
closure is minimal). Hence h[Cᵢ,y]=⋃ⱼ[C_Tᵢⱼ,sᵢⱼ(y)]. All closures use the appropriate source or
target plaque neighborhoods; no arbitrary continuous-map closure equality is assumed.

10. For z∈[Cᵢ,W₂αˢ(xᵢ)] set y=[xᵢ,z]∈W₂αˢ(xᵢ), so [Cᵢ,z]=[Cᵢ,y]. The preceding finite union selects
j=Tᵢₗ with hz∈[Cⱼ,sᵢₗ(y)]⊂[Cⱼ,Dⱼ⁰]. Absorption gives [Cⱼ,hz]=[Cⱼ,sᵢₗ(y)]⊂h[Cᵢ,z]. This is Lemma16
including boundary points. Repeat every step for f⁻¹, swapping the two plaque types and bracket
arguments, the same seeds a,F and the same m. The two given saturation conditions exchange, so all
hypotheses remain valid. It produces Dᵢ and the dual Lemma17 without changing Cᵢ.

11. The factors Cᵢ,Dᵢ are nonempty compact regular closed and lie in W_(ρ∞)ᵘ/ˢ(xᵢ), with
ρ∞<3α/2<α₄. The product theorem therefore gives proper rectangles Aᵢ=[Cᵢ,Dᵢ]. Seeds are contained,
so these rectangles cover X. For the stronger mesh estimate, any two factor points have
distance≤2ρ∞<3α=3α₅<ε(α₄/3). Each product point lies in the stable α₄/3 plaque of its unstable
factor and unstable α₄/3 plaque of its stable factor. Thus for two product points a,b with unstable
factors c,c′, d(a,b)≤2α₄/3+d(c,c′)≤2α₄/3+2ρ∞<2α₄/3+3α₅<α₄, since α₅<α₄/9. Restricting Lemmas16–17
to z∈Aᵢ gives both inclusions of Lemma18.

12. For the collar, assume d(q,xᵢ)<3α₄ and v=[q,xᵢ]∈Cᵢ. The modulus gives q∈W_(α₃/3)ˢ(v), and v∈Aᵢ
because xᵢ∈Dᵢ and v=[v,xᵢ]. Select j at v by Lemma18: hv∈Aⱼ and [Cⱼ,hv]⊂hCᵢ. Since v∈Wγˢ(q),
contraction gives hv∈W_(βγ)ˢ(hq)⊂W_aˢ(hq); F-saturation at hq puts hv,hq together in the seed
A_F(hq)⁰. Consequently Aⱼ meets A_F(hq), hq∈A_F(hq), and j∈N(hq). Put K=h⁻¹[Cⱼ,hv]⊂Cᵢ. Points of K
and v have backward distance≤2ρ∞<3α<α₃, because they lie in the common plaque based at xᵢ; hence
K⊂Wα₃ᵘ(v). The target slice lies in Wα₃ᵘ(hv), since hv∈Aⱼ and mesh<α₄. Apply the inclusion version
of the explicitly proved Lemma11(b) with source center v, source stable point q∈Wα₃ˢ(v), and this
single target piece. It gives h[K,q]=[[Cⱼ,hv],h[v,q]]=[Cⱼ,hq]⊂h[Cᵢ,q]. The equality h[v,q]=hq and
hq=[hv,hq] follow from the stable relation and intersection uniqueness. In particular hq∈[Cⱼ,hq].

13. Finally the collar inclusion transfers the exact full-plaque interior. Every point of [Cᵢ,q]
lies in W_(α₂/3)ᵘ(q), since d(c,q)≤ρ∞+3α₄<α₃<ε(α₂/3). Every point of [Cⱼ,hq] lies in W_(α₂/3)ᵘ(hq):
hv∈Aⱼ gives d(hv,xⱼ)<α₄, d(hq,hv)≤βγ<a<α₃, and d(c,hq)≤ρ∞+α₄+α₃<3α₃<ε(α₂/3). Thus both source and
target slices have a strict γ margin. Fix t∈int_(Wγᵘ(hq))[Cⱼ,hq] and w=h⁻¹t∈[Cᵢ,q]. The
finite-prefix/tail local calculation above gives a relative source neighborhood of w whose image
lies in the target γ-plaque and in the given target slice interior. Every point of this
neighborhood then lies in h⁻¹[Cⱼ,hq]⊂[Cᵢ,q]. Hence w is in int_(Wγᵘ(q))[Cᵢ,q], proving the
displayed interior inclusion. Exchanging f,f⁻¹ and both factors yields the asserted stable collar
for the very same Aᵢ. This argument neither uses nor claims global openness of h⁻¹ between full
γ-plaques.
-/
theorem manning_bowen_iterate_g3_enlarged_rectangles_remaining_gap
    {X I : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [Fintype I] [Nonempty I]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X) (εmod : ℝ → ℝ)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ (x y z : X) (n : ℕ), y ∈ ws f γ x → z ∈ ws f γ x →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ (x y z : X) (n : ℕ), y ∈ wu f γ x → z ∈ wu f γ x →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ x y, dist x y ≤ ε → bracket x y ∈ ws f γ x ∩ wu f γ y)
    (hbracket_unique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f γ x → z ∈ wu f γ y → z = bracket x y)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket x y ∈ ws f δ x ∩ wu f δ y)
    (α : Fin 8 → ℝ) (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαdesc : ∀ i : Fin 7, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 7, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 7, ∀ x y, dist x y ≤ α i.succ →
      dist (f x) (f y) < α i.castSucc ∧ dist (f.symm x) (f.symm y) < α i.castSucc)
    (x₀ : I → X) (C₀ D₀ : I → Set X)
    (hC₀ : ∀ i, (C₀ i).Nonempty ∧ IsCompact (C₀ i) ∧ C₀ i ⊆ wu f (α 7) (x₀ i) ∧
      C₀ i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C₀ i)) ∧
      x₀ i ∈ ri (wu f γ (x₀ i)) (C₀ i))
    (hD₀ : ∀ i, (D₀ i).Nonempty ∧ IsCompact (D₀ i) ∧ D₀ i ⊆ ws f (α 7) (x₀ i) ∧
      D₀ i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D₀ i)) ∧
      x₀ i ∈ ri (ws f γ (x₀ i)) (D₀ i))
    (hproper₀ : ∀ i, proper bracket (α 3) (bi bracket (C₀ i) (D₀ i)))
    (hcover₀ : (univ : Set X) ⊆ ⋃ i, interior (bi bracket (C₀ i) (D₀ i)))
    (hdiam₀ : ∀ i, Metric.diam (bi bracket (C₀ i) (D₀ i)) < α 5 / 2)
    (hseed_u : ∀ i y, y ∈ ws f (2 * α 5) (x₀ i) →
      bi bracket (C₀ i) {y} ⊆ wu f (α 5) y)
    (hseed_s : ∀ i y, y ∈ wu f (2 * α 5) (x₀ i) →
      bi bracket {y} (D₀ i) ⊆ ws f (α 5) y)
    (a : ℝ) (ha : 0 < a ∧ a < min γ (α 3)) (F : X → I)
    (hFmem : ∀ x, x ∈ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFs : ∀ x z, z ∈ wu f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      ws f a z ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (hFu : ∀ x y, y ∈ ws f γ x ∩ bi bracket (C₀ (F x)) (D₀ (F x)) →
      wu f a y ⊆ bi bracket (C₀ (F x)) (D₀ (F x)))
    (m : ℕ) (hm : 1 ≤ m)
    (hsum : (∑' k : ℕ, (lam ^ m) ^ (k + 1)) < min 1 (a / γ)) :
    let h := f ^ m
    let β := lam ^ m
    ∃ (k l : I → ℕ) (T : (i : I) → Fin (k i) → I)
      (y : (i : I) → Fin (k i) → X) (R : (i : I) → Fin (l i) → I)
      (w : (i : I) → Fin (l i) → X),
      (∀ i j, y i j ∈ wu f (α 5) (x₀ i) ∧ h (y i j) ∈ D₀ (T i j) ∧
        (h '' C₀ i ∩ bi bracket (C₀ (T i j)) {h (y i j)}).Nonempty ∧
        ∀ z, z ∈ wu f γ (h (y i j)) ∩ bi bracket (C₀ (T i j)) (D₀ (T i j)) →
          ws f a z ⊆ bi bracket (C₀ (T i j)) (D₀ (T i j))) ∧
      (∀ i, h '' C₀ i ⊆ ⋃ j, bi bracket (C₀ (T i j)) {h (y i j)}) ∧
      (∀ i j, w i j ∈ ws f (α 5) (x₀ i) ∧ h.symm (w i j) ∈ C₀ (R i j) ∧
        (h.symm '' D₀ i ∩ bi bracket {h.symm (w i j)} (D₀ (R i j))).Nonempty ∧
        ∀ z, z ∈ ws f γ (h.symm (w i j)) ∩ bi bracket (C₀ (R i j)) (D₀ (R i j)) →
          wu f a z ⊆ bi bracket (C₀ (R i j)) (D₀ (R i j))) ∧
      (∀ i, h.symm '' D₀ i ⊆ ⋃ j, bi bracket {h.symm (w i j)} (D₀ (R i j))) ∧
      (let Cn := stage h bracket C₀ k T y
       let Dn := stage h.symm (fun x y ↦ bracket y x) D₀ l R w
       let C := fun i ↦ rc (wu f γ (x₀ i)) (⋃ n, Cn n i)
       let D := fun i ↦ rc (ws f γ (x₀ i)) (⋃ n, Dn n i)
       let A := fun i ↦ bi bracket (C i) (D i)
       let V := fun i ↦ {q | ∃ j, (A i ∩ A j).Nonempty ∧ q ∈ A j}
       let N := fun q ↦ {i | q ∈ V i}
       (∀ i, IsCompact (C i) ∧ C₀ i ⊆ C i ∧ C i ⊆ wu f (2 * α 5) (x₀ i) ∧
         C i = rc (wu f γ (x₀ i)) (ri (wu f γ (x₀ i)) (C i))) ∧
       (∀ i, IsCompact (D i) ∧ D₀ i ⊆ D i ∧ D i ⊆ ws f (2 * α 5) (x₀ i) ∧
         D i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D i))) ∧
       (∀ n, 1 ≤ n → ∀ i z, z ∈ ws f (2 * α 5) (x₀ i) →
         bi bracket (Cn (n - 1) i) {z} ⊆ bi bracket (Cn n i) {z} ∧
         bi bracket (Cn n i) {z} ⊆ pu (wu f) (β ^ n * α 5)
           (bi bracket (Cn (n - 1) i) {z}) ∧
         pu (wu f) (β ^ n * α 5) (bi bracket (Cn (n - 1) i) {z}) ⊆
           wu f ((∑ j ∈ Finset.range (n + 1), β ^ j) * α 5) z) ∧
       (∀ n, 1 ≤ n → ∀ i z, z ∈ wu f (2 * α 5) (x₀ i) →
         bi bracket {z} (Dn (n - 1) i) ⊆ bi bracket {z} (Dn n i) ∧
         bi bracket {z} (Dn n i) ⊆ pu (ws f) (β ^ n * α 5)
           (bi bracket {z} (Dn (n - 1) i)) ∧
         pu (ws f) (β ^ n * α 5) (bi bracket {z} (Dn (n - 1) i)) ⊆
           ws f ((∑ j ∈ Finset.range (n + 1), β ^ j) * α 5) z) ∧
       (∀ n i z, z ∈ ws f (2 * α 5) (x₀ i) →
         bi bracket (Cn n i) {z} =
           rc (wu f γ z) (ri (wu f γ z) (bi bracket (Cn n i) {z}))) ∧
       (∀ n i z, z ∈ wu f (2 * α 5) (x₀ i) →
         bi bracket {z} (Dn n i) =
           rc (ws f γ z) (ri (ws f γ z) (bi bracket {z} (Dn n i)))) ∧
       (∀ i, proper bracket (α 3) (A i) ∧ Metric.diam (A i) < α 4) ∧
       ((univ : Set X) ⊆ ⋃ i, A i) ∧
       (∀ i z, z ∈ bi bracket (C i) (ws f (2 * α 5) (x₀ i)) →
         ∃ j, h z ∈ bi bracket (C j) (D₀ j) ∧
           bi bracket (C j) {h z} ⊆ h '' bi bracket (C i) {z}) ∧
       (∀ i z, z ∈ bi bracket (wu f (2 * α 5) (x₀ i)) (D i) →
         ∃ j, h.symm z ∈ bi bracket (C₀ j) (D j) ∧
           bi bracket {h.symm z} (D j) ⊆ h.symm '' bi bracket {z} (D i)) ∧
       (∀ i q, dist q (x₀ i) < 3 * α 4 → bracket q (x₀ i) ∈ C i →
         ∃ j ∈ N (h q), h q ∈ bi bracket (C j) {h q} ∧
           bi bracket (C j) {h q} ⊆ h '' bi bracket (C i) {q} ∧
           h.symm '' ri (wu f γ (h q)) (bi bracket (C j) {h q}) ⊆
             ri (wu f γ q) (bi bracket (C i) {q})) ∧
       (∀ i q, dist q (x₀ i) < 3 * α 4 → bracket (x₀ i) q ∈ D i →
         ∃ j ∈ N (h.symm q), h.symm q ∈ bi bracket {h.symm q} (D j) ∧
           bi bracket {h.symm q} (D j) ⊆ h.symm '' bi bracket {q} (D i) ∧
           h '' ri (ws f γ (h.symm q)) (bi bracket {h.symm q} (D j)) ⊆
             ri (ws f γ q) (bi bracket {q} (D i)))) := by
  classical
  obtain ⟨k, T, y, hyData, hyCover⟩ := finiteReceivingLabels
    f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u hbracket_mem hbracket_unique
    hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin x₀ C₀ D₀ hC₀ hD₀
    hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu m hm hsum
  have hreverseMem : ∀ x y, dist x y ≤ ε →
      bracket y x ∈ ws f.symm γ x ∩ wu f.symm γ y := by
    intro x y hxy
    have hb := hbracket_mem y x (by simpa only [dist_comm] using hxy)
    exact ⟨hb.2, by simpa only [wu_symm] using hb.1⟩
  have hreverseUnique : ∀ x y z, dist x y ≤ ε →
      z ∈ ws f.symm γ x → z ∈ wu f.symm γ y → z = bracket y x := by
    intro x y z hxy hs hu
    exact hbracket_unique y x z (by simpa only [dist_comm] using hxy)
      (by simpa only [wu_symm] using hu) hs
  have hreverseCont : ContinuousOn (fun p : X × X ↦ bracket p.2 p.1)
      {p | dist p.1 p.2 ≤ ε} :=
    hbracket_cont.comp continuous_swap.continuousOn (fun p hp ↦ by
      simpa only [mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap, dist_comm] using hp)
  have hreverseMod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ x y, dist x y ≤ εmod δ → bracket y x ∈ ws f.symm δ x ∩ wu f.symm δ y := by
    intro δ hδ hδγ
    refine ⟨(hmod δ hδ hδγ).1, ?_⟩
    intro x y hxy
    have hb := (hmod δ hδ hδγ).2 y x (by simpa only [dist_comm] using hxy)
    exact ⟨hb.2, by simpa only [wu_symm] using hb.1⟩
  obtain ⟨l, R, w, hwData, hwCover⟩ := finiteReceivingLabels
    f.symm lam γ ε (fun x y ↦ bracket y x) εmod hlam hγ hε hfact_u
    (by simpa only [wu_symm, Homeomorph.symm_symm] using hfact_s)
    hreverseMem hreverseUnique hreverseCont hreverseMod α hα0 hαpos hαdesc hαrec
    (fun i x y hxy ↦ ⟨(hαmargin i x y hxy).2, (hαmargin i x y hxy).1⟩)
    x₀ D₀ C₀ (by simpa only [wu_symm] using hD₀) hC₀
    (by simpa only [bi_flip, proper_flip] using hproper₀)
    (by simpa only [bi_flip] using hcover₀) (by simpa only [bi_flip] using hdiam₀)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_s)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_u)
    a ha F (by simpa only [bi_flip] using hFmem)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFu)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFs) m hm hsum
  have hcoverC : ∀ i, (f ^ m) '' C₀ i ⊆
      ⋃ j, bi bracket (C₀ (T i j)) {(f ^ m) (y i j)} := hyCover
  have hstageC := finiteStageBounds f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hyData hcoverC
  have hregC := finiteStageRegular f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hyData hcoverC
  have hstageD := finiteStageBounds
    f.symm lam γ ε (fun x y ↦ bracket y x) εmod hlam hγ hε hfact_u
    (by simpa only [wu_symm, Homeomorph.symm_symm] using hfact_s)
    hreverseMem hreverseUnique hreverseCont hreverseMod α hα0 hαpos hαdesc hαrec
    (fun i x y hxy ↦ ⟨(hαmargin i x y hxy).2, (hαmargin i x y hxy).1⟩)
    x₀ D₀ C₀ (by simpa only [wu_symm] using hD₀) hC₀
    (by simpa only [bi_flip, proper_flip] using hproper₀)
    (by simpa only [bi_flip] using hcover₀) (by simpa only [bi_flip] using hdiam₀)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_s)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_u)
    a ha F (by simpa only [bi_flip] using hFmem)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFu)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFs) m hm hsum l R w hwData hwCover
  have hregD := finiteStageRegular
    f.symm lam γ ε (fun x y ↦ bracket y x) εmod hlam hγ hε hfact_u
    (by simpa only [wu_symm, Homeomorph.symm_symm] using hfact_s)
    hreverseMem hreverseUnique hreverseCont hreverseMod α hα0 hαpos hαdesc hαrec
    (fun i x y hxy ↦ ⟨(hαmargin i x y hxy).2, (hαmargin i x y hxy).1⟩)
    x₀ D₀ C₀ (by simpa only [wu_symm] using hD₀) hC₀
    (by simpa only [bi_flip, proper_flip] using hproper₀)
    (by simpa only [bi_flip] using hcover₀) (by simpa only [bi_flip] using hdiam₀)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_s)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_u)
    a ha F (by simpa only [bi_flip] using hFmem)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFu)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFs) m hm hsum l R w hwData hwCover
  have hsharpC := limitFactorSharpBound f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hyData hcoverC
  have hsharpD := limitFactorSharpBound
    f.symm lam γ ε (fun x y ↦ bracket y x) εmod hlam hγ hε hfact_u
    (by simpa only [wu_symm, Homeomorph.symm_symm] using hfact_s)
    hreverseMem hreverseUnique hreverseCont hreverseMod α hα0 hαpos hαdesc hαrec
    (fun i x y hxy ↦ ⟨(hαmargin i x y hxy).2, (hαmargin i x y hxy).1⟩)
    x₀ D₀ C₀ (by simpa only [wu_symm] using hD₀) hC₀
    (by simpa only [bi_flip, proper_flip] using hproper₀)
    (by simpa only [bi_flip] using hcover₀) (by simpa only [bi_flip] using hdiam₀)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_s)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_u)
    a ha F (by simpa only [bi_flip] using hFmem)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFu)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFs) m hm hsum l R w hwData hwCover
  have hinv : f.symm ^ m = (f ^ m).symm := inv_pow f m
  refine ⟨k, l, T, y, R, w, hyData, hyCover, ?_, ?_, ?_⟩
  · simpa only [ws_symm, wu_symm, bi_flip, hinv] using hwData
  · simpa only [bi_flip, hinv] using hwCover
  let Cn := stage (f ^ m) bracket C₀ k T y
  let Dn := stage (f ^ m).symm (fun x y ↦ bracket y x) D₀ l R w
  let C := fun i ↦ rc (wu f γ (x₀ i)) (⋃ n, Cn n i)
  let D := fun i ↦ rc (ws f γ (x₀ i)) (⋃ n, Dn n i)
  have hmono : Antitone α := Fin.antitone_iff_succ_le.mpr (fun i ↦ (hαdesc i).le)
  have h10 : 9 * α 1 < γ := by
    have hh := (hαrec 0).trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 1 / 3))
    norm_num [hα0] at hh
    linarith
  have h2γ : 2 * α 5 ≤ γ := by
    have hh := hmono (show (1 : Fin 8) ≤ 5 by decide)
    linarith [hαpos 1]
  have hCprops (i : I) := limitFactorProperties f γ (2 * α 5) h2γ (x₀ i)
    (fun n ↦ Cn n i) (fun n ↦ hstageC.1 n i) (fun n ↦ (hregC.1 n i).2)
  have htransC := limitSliceTransport f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
    hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
    x₀ C₀ D₀ hC₀ hD₀ hproper₀ hcover₀ hdiam₀ hseed_u hseed_s a ha F hFmem hFs hFu
    m hm hsum k T y hyData hcoverC
  have htransD := limitSliceTransport
    f.symm lam γ ε (fun x y ↦ bracket y x) εmod hlam hγ hε hfact_u
    (by simpa only [wu_symm, Homeomorph.symm_symm] using hfact_s)
    hreverseMem hreverseUnique hreverseCont hreverseMod α hα0 hαpos hαdesc hαrec
    (fun i x y hxy ↦ ⟨(hαmargin i x y hxy).2, (hαmargin i x y hxy).1⟩)
    x₀ D₀ C₀ (by simpa only [wu_symm] using hD₀) hC₀
    (by simpa only [bi_flip, proper_flip] using hproper₀)
    (by simpa only [bi_flip] using hcover₀) (by simpa only [bi_flip] using hdiam₀)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_s)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hseed_u)
    a ha F (by simpa only [bi_flip] using hFmem)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFu)
    (by simpa only [ws_symm, wu_symm, bi_flip] using hFs) m hm hsum l R w hwData hwCover
  have hDprops (i : I) := limitFactorProperties f.symm γ (2 * α 5) h2γ (x₀ i)
    (fun n ↦ stage (f.symm ^ m) (fun x y ↦ bracket y x) D₀ l R w n i)
    (fun n ↦ hstageD.1 n i) (fun n ↦ (hregD.1 n i).2)
  refine ⟨?_, ?_, hstageC.2.2, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hCprops i).1, (hCprops i).2.1, (hCprops i).2.2.1, (hCprops i).2.2.2.1⟩
  · intro i
    have hh := hDprops i
    have hpack := And.intro hh.1 (And.intro hh.2.1 (And.intro hh.2.2.1 hh.2.2.2.1))
    simpa only [wu_symm, hinv, stage] using hpack
  · simpa only [ws_symm, wu_symm, bi_flip, hinv, pu] using hstageD.2.2
  · exact fun n i z hz ↦ (hregC.2 n i z hz).2
  · have hh := fun n i z hz ↦ (hregD.2 n i z hz).2
    simpa only [ws_symm, wu_symm, bi_flip, hinv] using hh
  · have hDprops' (i : I) : IsCompact (D i) ∧ D₀ i ⊆ D i ∧
        D i ⊆ ws f (2 * α 5) (x₀ i) ∧
        D i = rc (ws f γ (x₀ i)) (ri (ws f γ (x₀ i)) (D i)) := by
      have hh := hDprops i
      have hpack := And.intro hh.1 (And.intro hh.2.1 (And.intro hh.2.2.1 hh.2.2.2.1))
      simpa only [wu_symm, hinv, stage] using hpack
    have hDsharp (i : I) : D i ⊆ ws f ((3 / 2) * α 5) (x₀ i) := by
      simpa only [wu_symm, hinv] using hsharpD i
    have hA (i : I) : proper bracket (α 3) (bi bracket (C i) (D i)) ∧
        Metric.diam (bi bracket (C i) (D i)) < α 4 :=
      limitRectangleProperties f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
        hbracket_mem hbracket_unique hbracket_cont hmod α hα0 hαpos hαdesc hαrec hαmargin
        (x₀ i) (C i) (D i)
        ((hC₀ i).1.mono (hCprops i).2.1) ((hD₀ i).1.mono (hDprops' i).2.1)
        (hCprops i).1 (hDprops' i).1 (hsharpC i) (hDsharp i)
        (hCprops i).2.2.2.1 (hDprops' i).2.2.2
    have hTC := transportFromSlices f (f ^ m) γ ε bracket εmod hγ hε hbracket_unique hmod
      α hα0 hαpos hαdesc hαrec x₀ C D₀ (fun i ↦ (hCprops i).2.2.1)
      (fun i d hd n ↦ ((hD₀ i).2.2.1 hd n).trans (by
        have hh := hmono (show (5 : Fin 8) ≤ 7 by decide); linarith [hαpos 5]))
      k T y htransC
    have hTD := transportFromSlices f.symm (f.symm ^ m) γ ε (fun x y ↦ bracket y x)
      εmod hγ hε hreverseUnique hreverseMod α hα0 hαpos hαdesc hαrec x₀
      (fun i ↦ rc (wu f.symm γ (x₀ i))
        (⋃ n, stage (f.symm ^ m) (fun x y ↦ bracket y x) D₀ l R w n i)) C₀
      (fun i ↦ (hDprops i).2.2.1)
      (fun i c hc n ↦ ((hC₀ i).2.2.1 hc n).trans (by
        have hh := hmono (show (5 : Fin 8) ≤ 7 by decide); linarith [hαpos 5]))
      l R w htransD
    have hseedA (i : I) : bi bracket (C₀ i) (D₀ i) ⊆ bi bracket (C i) (D i) := by
      rintro z ⟨c, hc, d, hd, he⟩
      exact ⟨c, (hCprops i).2.1 hc, d, (hDprops' i).2.1 hd, he⟩
    have hxC (i : I) : x₀ i ∈ C i :=
      (hCprops i).2.1 (ri_subset _ _ (hC₀ i).2.2.2.2)
    have hxD (i : I) : x₀ i ∈ D i :=
      (hDprops' i).2.1 (ri_subset _ _ (hD₀ i).2.2.2.2)
    have hmesh (i : I) (u : X) (hu : u ∈ bi bracket (C i) (D i))
        (v : X) (hv : v ∈ bi bracket (C i) (D i)) : dist u v < α 4 :=
      (Metric.dist_le_diam_of_mem (hA i).1.2.1.isBounded hu hv).trans_lt (hA i).2
    have hFA (q : X) : q ∈ bi bracket (C (F q)) (D (F q)) := hseedA _ (hFmem q)
    have hFsa (q : X) : ws f a q ⊆ bi bracket (C (F q)) (D (F q)) :=
      (hFs q q ⟨(fun n ↦ by simpa using hγ.le), hFmem q⟩).trans (hseedA _)
    have hFua (q : X) : wu f a q ⊆ bi bracket (C (F q)) (D (F q)) :=
      (hFu q q ⟨(fun n ↦ by simpa using hγ.le), hFmem q⟩).trans (hseedA _)
    have ha3 : a < α 3 := ha.2.trans_le (min_le_right _ _)
    have haγ : a < γ / 2 := by
      have hh := hmono (show (1 : Fin 8) ≤ 3 by decide)
      linarith [hαpos 1]
    have hβ : lam ^ m * γ < a :=
      (enlargement_numeric_bounds lam γ a hlam hγ ha.1 haγ m hm hsum).2.2.1
    have hTCA : ∀ i z, z ∈ bi bracket (C i) (ws f (2 * α 5) (x₀ i)) →
        ∃ j, (f ^ m) z ∈ bi bracket (C j) (D j) ∧
          bi bracket (C j) {(f ^ m) z} ⊆ (f ^ m) '' bi bracket (C i) {z} := by
      intro i z hz
      obtain ⟨j, ⟨c, hc, d, hd, he⟩, ht⟩ := hTC i z hz
      exact ⟨j, ⟨c, hc, d, (hDprops' j).2.1 hd, he⟩, ht⟩
    have hTDA : ∀ i z, z ∈ bi (fun x y ↦ bracket y x) (D i)
        (ws f.symm (2 * α 5) (x₀ i)) →
        ∃ j, (f.symm ^ m) z ∈ bi (fun x y ↦ bracket y x) (D j) (C j) ∧
          bi (fun x y ↦ bracket y x) (D j) {(f.symm ^ m) z} ⊆
            (f.symm ^ m) '' bi (fun x y ↦ bracket y x) (D i) {z} := by
      have hh : ∀ i z, z ∈ bi (fun x y ↦ bracket y x) (D i)
          (ws f.symm (2 * α 5) (x₀ i)) →
          ∃ j, (f.symm ^ m) z ∈ bi (fun x y ↦ bracket y x) (D j) (C₀ j) ∧
            bi (fun x y ↦ bracket y x) (D j) {(f.symm ^ m) z} ⊆
              (f.symm ^ m) '' bi (fun x y ↦ bracket y x) (D i) {z} := by
        simpa only [wu_symm, hinv] using hTD
      intro i z hz
      obtain ⟨j, ⟨d, hd, c, hc, he⟩, ht⟩ := hh i z hz
      exact ⟨j, ⟨d, hd, c, (hCprops j).2.1 hc, he⟩, ht⟩
    refine ⟨hA, ?_, hTC, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover₀ hq)
      exact mem_iUnion.mpr ⟨i, hseedA i (interior_subset hi)⟩
    · simpa only [ws_symm, wu_symm, bi_flip, hinv] using hTD
    · exact collarFromTransport f lam γ ε bracket εmod hlam hγ hε hfact_s hfact_u
        hbracket_unique hmod α hα0 hαpos hαdesc hαrec x₀ C D
        (fun i ↦ (hCprops i).2.2.1) (fun i ↦ (hDprops' i).2.2.1) hxC hxD
        hmesh (fun i ↦ (hA i).1.2.2.1) a ha3 F hFA hFsa m hβ hTCA
    · have hh := collarFromTransport f.symm lam γ ε (fun x y ↦ bracket y x) εmod
        hlam hγ hε hfact_u
        (by simpa only [wu_symm, Homeomorph.symm_symm] using hfact_s)
        hreverseUnique hreverseMod α hα0 hαpos hαdesc hαrec x₀ D C
        (by simpa only [wu_symm] using (fun i ↦ (hDprops' i).2.2.1))
        (fun i ↦ (hCprops i).2.2.1) hxD hxC
        (by simpa only [bi_flip] using hmesh)
        (by
          intro i u hu v hv
          simpa only [bi_flip] using (hA i).1.2.2.1 v (by simpa only [bi_flip] using hv)
            u (by simpa only [bi_flip] using hu))
        a ha3 F (by simpa only [bi_flip] using hFA)
        (by simpa only [ws_symm, bi_flip] using hFua) m hβ hTDA
      dsimp [C, D, Cn, Dn] at hh
      simpa only [ws_symm, wu_symm, bi_flip, hinv, Homeomorph.symm_symm,
        mem_ofPred_eq] using hh

end HolomorphicAnosov.Bowen
