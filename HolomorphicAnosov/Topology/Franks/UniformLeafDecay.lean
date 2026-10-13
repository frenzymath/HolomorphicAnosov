import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Logic.Relation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Floor.Ring

open Filter Set
open scoped Topology

namespace HolomorphicAnosov.FranksOriginalCover

/-- Uniform orbit decay on generating plaques propagates along finite native
plaque chains. This is the topological version of the transported-anchor
argument in Franks (1969), §1.8. For a two-leg chain move its middle anchor
with the continuous global crossing J. The two local estimates with error
ε/2 then hold on one neighborhood; the triangle inequality gives error ε.
Only the generator estimates use the native hyperbolic dynamics. -/
theorem locally_uniform_decay_eqvGen
    {P : Type*} [TopologicalSpace P]
    (G : P → P → Prop) (d : ℕ → P → P → ℝ)
    (hsymm : ∀ n x y, Relation.EqvGen G x y → d n x y = d n y x)
    (htri : ∀ n x y z, Relation.EqvGen G x y → Relation.EqvGen G y z →
      d n x z ≤ d n x y + d n y z)
    (J : P × P → P) (hJ : Continuous J)
    (hJleaf : ∀ x y, Relation.EqvGen G x (J (x,y)))
    (hJfix : ∀ x y, Relation.EqvGen G x y → J (x,y) = y)
    (hdiag : ∀ x, ∀ ε > 0, ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,x),
      Relation.EqvGen G z.1 z.2 → ∀ n ≥ N, d n z.1 z.2 < ε)
    (hgen : ∀ x y, G x y → ∀ ε > 0, ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,y),
      Relation.EqvGen G z.1 z.2 → ∀ n ≥ N, d n z.1 z.2 < ε)
    {x y : P} (hxy : Relation.EqvGen G x y) :
    ∀ ε > 0, ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,y),
      Relation.EqvGen G z.1 z.2 → ∀ n ≥ N, d n z.1 z.2 < ε := by
  induction hxy with
  | rel x y hxy => exact hgen x y hxy
  | refl x => exact hdiag x
  | symm x y hxy ih =>
    intro ε hε
    obtain ⟨N, hN⟩ := ih ε hε
    refine ⟨N, ?_⟩
    have ht : Tendsto Prod.swap (𝓝 (y,x)) (𝓝 (x,y)) := continuous_swap.tendsto _
    filter_upwards [ht hN] with z hz hrel n hn
    rw [hsymm n z.1 z.2 hrel]
    exact hz (Relation.EqvGen.symm _ _ hrel) n hn
  | trans x y z hxy hyz ih₁ ih₂ =>
    intro ε hε
    obtain ⟨N, hN⟩ := ih₁ (ε/2) (half_pos hε)
    obtain ⟨M, hM⟩ := ih₂ (ε/2) (half_pos hε)
    have hmid : Continuous (fun w : P × P ↦ J (w.1,y)) :=
      hJ.comp (continuous_fst.prodMk continuous_const)
    have hleft : Tendsto (fun w : P × P ↦ (w.1,J (w.1,y)))
        (𝓝 (x,z)) (𝓝 (x,y)) := by
      simpa only [hJfix x y hxy] using
        (continuous_fst.prodMk hmid).tendsto (x,z)
    have hright : Tendsto (fun w : P × P ↦ (J (w.1,y),w.2))
        (𝓝 (x,z)) (𝓝 (y,z)) := by
      simpa only [hJfix x y hxy] using
        (hmid.prodMk continuous_snd).tendsto (x,z)
    refine ⟨max N M, ?_⟩
    filter_upwards [hleft hN, hright hM] with w hw₁ hw₂ hrel n hn
    have hu := hJleaf w.1 y
    have hv := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hu) hrel
    have h₁ := hw₁ hu n ((le_max_left N M).trans hn)
    have h₂ := hw₂ hv n ((le_max_right N M).trans hn)
    have h₃ := htri n _ _ _ hu hv
    linarith

/-- Local uniform decay is uniform on a compact set of related pairs. For
fixed ε, the interiors of the eventual ε-bounds form an increasing open cover
of the compact carrier; one member covers it. This uses no intrinsic metric
or derivative estimate beyond the supplied native local orbit decay. -/
theorem uniform_decay_on_compact_relation
    {P : Type*} [TopologicalSpace P] (R : P → P → Prop)
    (d : ℕ → P → P → ℝ) (K : Set (P × P)) (hK : IsCompact K)
    (hR : ∀ z ∈ K, R z.1 z.2)
    (hloc : ∀ z ∈ K, ∀ ε > 0, ∃ N : ℕ, ∀ᶠ w : P × P in 𝓝 z,
      R w.1 w.2 → ∀ n ≥ N, d n w.1 w.2 < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ z ∈ K, ∀ n ≥ N, d n z.1 z.2 < ε := by
  intro ε hε
  let W : ℕ → Set (P × P) :=
    fun N ↦ interior {z | R z.1 z.2 → ∀ n ≥ N, d n z.1 z.2 < ε}
  have hcover : K ⊆ ⋃ N, W N := by
    intro z hz
    obtain ⟨N, hN⟩ := hloc z hz ε hε
    exact mem_iUnion.2 ⟨N, mem_interior_iff_mem_nhds.2 hN⟩
  have hmono : Monotone W := by
    intro N M hNM
    apply interior_mono
    intro z hz hzR n hn
    exact hz hzR n (hNM.trans hn)
  obtain ⟨N, hN⟩ := hK.elim_directed_cover W (fun _ ↦ isOpen_interior) hcover
    (fun N M ↦ ⟨max N M, hmono (le_max_left N M), hmono (le_max_right N M)⟩)
  refine ⟨N, ?_⟩
  intro z hz n hn
  exact interior_subset (hN hz) (hR z hz) n hn

/-- Normalize backward iterates of an equal-image leaf pair into a fixed
carrier with uniform forward decay. Normalization preserves the downstairs
endpoints (as an actual deck transformation does). Forward iteration cancels
the backward iterates, so the original downstairs distance is below every
positive ε. This is the uniform-decay substitute for the intrinsic-distance
expansion contradiction in Franks (1969), §1.8. -/
theorem projection_eq_of_backward_normalized_decay
    {P M V : Type*} [MetricSpace M]
    (R : P → P → Prop) (H : P → V) (p : P → M) (G : P → P) (f : M ≃ M)
    (hsem : Function.Semiconj p G f.symm)
    (hR : ∀ x y, R x y → R (G x) (G y))
    (hH : ∀ x y, H x = H y → H (G x) = H (G y))
    (K : Set (P × P))
    (hnormalize : ∀ x y, R x y → H x = H y →
      ∃ z ∈ K, p z.1 = p x ∧ p z.2 = p y)
    (hdecay : ∀ ε > 0, ∃ N : ℕ, ∀ z ∈ K, ∀ n ≥ N,
      dist ((f : M → M)^[n] (p z.1)) ((f : M → M)^[n] (p z.2)) < ε)
    {x y : P} (hxy : R x y) (himage : H x = H y) : p x = p y := by
  have hiter : ∀ n : ℕ, R (G^[n] x) (G^[n] y) ∧ H (G^[n] x) = H (G^[n] y) := by
    intro n
    induction n with
    | zero => exact ⟨hxy, himage⟩
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using ⟨hR _ _ ih.1, hH _ _ ih.2⟩
  have hcancel (n : ℕ) (w : P) : (f : M → M)^[n] (p (G^[n] w)) = p w := by
    rw [hsem.iterate_right n w]
    exact (show Function.LeftInverse (f : M → M) f.symm from f.apply_symm_apply).iterate n (p w)
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨N, hN⟩ := hdecay ε hε
  obtain ⟨z, hz, hxz, hyz⟩ := hnormalize _ _ (hiter N).1 (hiter N).2
  have hb := hN z hz N le_rfl
  simpa only [hxz, hyz, hcancel, zero_add] using hb

/-- A native lifted leaf whose projection is injective has no two equal-image
points once the backward-normalized decay criterion holds. -/
theorem eq_of_backward_normalized_leaf_decay
    {P M V : Type*} [MetricSpace M]
    (R : P → P → Prop) (H : P → V) (p : P → M) (G : P → P) (f : M ≃ M)
    (hsem : Function.Semiconj p G f.symm)
    (hR : ∀ x y, R x y → R (G x) (G y))
    (hH : ∀ x y, H x = H y → H (G x) = H (G y))
    (K : Set (P × P))
    (hnormalize : ∀ x y, R x y → H x = H y →
      ∃ z ∈ K, p z.1 = p x ∧ p z.2 = p y)
    (hdecay : ∀ ε > 0, ∃ N : ℕ, ∀ z ∈ K, ∀ n ≥ N,
      dist ((f : M → M)^[n] (p z.1)) ((f : M → M)^[n] (p z.2)) < ε)
    (hpinj : ∀ x y, R x y → p x = p y → x = y)
    {x y : P} (hxy : R x y) (himage : H x = H y) : x = y :=
  hpinj x y hxy (projection_eq_of_backward_normalized_decay
    R H p G f hsem hR hH K hnormalize hdecay hxy himage)

/-- One integer deck translation normalizes both endpoints of an equal-image
leaf pair into a fixed compact pair relation. Translate by minus the coordinate
floors of their common H-image. Every translated coordinate lies in [0,1),
hence in the closed unit sup-norm ball. Properness supplies its compact
preimage; closedness of the leaf relation supplies a compact pair carrier.
Deck projection invariance retains the actual downstairs endpoints. -/
theorem compact_deck_normalized_equal_image_pairs
    {P M : Type*} [TopologicalSpace P] {n : ℕ}
    (R : P → P → Prop) (hRclosed : IsClosed {z : P × P | R z.1 z.2})
    (H : P → (Fin n → ℝ)) (hproper : IsProperMap H) (p : P → M)
    (δ : (Fin n → ℤ) → P → P)
    (hdeck : ∀ k x, H (δ k x) = H x + fun i ↦ (k i : ℝ))
    (hproj : ∀ k x, p (δ k x) = p x)
    (hRdeck : ∀ k x y, R x y → R (δ k x) (δ k y)) :
    ∃ K : Set (P × P), IsCompact K ∧ (∀ z ∈ K, R z.1 z.2) ∧
      ∀ x y, R x y → H x = H y → ∃ z ∈ K, p z.1 = p x ∧ p z.2 = p y := by
  let C := H ⁻¹' Metric.closedBall 0 1
  have hC : IsCompact C := hproper.isCompact_preimage (isCompact_closedBall _ _)
  refine ⟨(C ×ˢ C) ∩ {z | R z.1 z.2}, (hC.prod hC).inter_right hRclosed,
    fun z hz ↦ hz.2, ?_⟩
  intro x y hxy hHxy
  let k : Fin n → ℤ := fun i ↦ -⌊H x i⌋
  have hx : δ k x ∈ C := by
    change H (δ k x) ∈ Metric.closedBall 0 1
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2
    intro i
    rw [hdeck]
    change ‖H x i + ((-⌊H x i⌋ : ℤ) : ℝ)‖ ≤ 1
    rw [Int.cast_neg, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Int.floor_le (H x i), Int.lt_floor_add_one (H x i)]
  have hy : δ k y ∈ C := by
    have he : H (δ k y) = H (δ k x) := by rw [hdeck, hdeck, hHxy]
    change H (δ k y) ∈ Metric.closedBall 0 1
    rw [he]
    exact hx
  exact ⟨(δ k x, δ k y), ⟨⟨hx, hy⟩, hRdeck k x y hxy⟩,
    hproj k x, hproj k y⟩

/-- Consumer assembly of the uniform-decay injectivity argument. Native
generator estimates, continuous global crossings, closed leaf relation, proper
integer-equivariant H, and actual inverse dynamics imply injectivity on each
generated leaf. Every compactness and normalization step is constructed here. -/
theorem eq_of_proper_equivariant_leaf_decay
    {P M : Type*} [TopologicalSpace P] [MetricSpace M] {n : ℕ}
    (G : P → P → Prop)
    (hclosed : IsClosed {z : P × P | Relation.EqvGen G z.1 z.2})
    (H : P → (Fin n → ℝ)) (hproper : IsProperMap H) (p : P → M)
    (δ : (Fin n → ℤ) → P → P)
    (hdeck : ∀ k x, H (δ k x) = H x + fun i ↦ (k i : ℝ))
    (hproj : ∀ k x, p (δ k x) = p x)
    (hRdeck : ∀ k x y, Relation.EqvGen G x y → Relation.EqvGen G (δ k x) (δ k y))
    (J : P × P → P) (hJ : Continuous J)
    (hJleaf : ∀ x y, Relation.EqvGen G x (J (x,y)))
    (hJfix : ∀ x y, Relation.EqvGen G x y → J (x,y) = y)
    (B : P → P) (f : M ≃ M) (hsem : Function.Semiconj p B f.symm)
    (hRB : ∀ x y, Relation.EqvGen G x y → Relation.EqvGen G (B x) (B y))
    (hHB : ∀ x y, H x = H y → H (B x) = H (B y))
    (hdiag : ∀ x, ∀ ε > 0, ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,x),
      Relation.EqvGen G z.1 z.2 → ∀ m ≥ N,
        dist ((f : M → M)^[m] (p z.1)) ((f : M → M)^[m] (p z.2)) < ε)
    (hgen : ∀ x y, G x y → ∀ ε > 0, ∃ N : ℕ, ∀ᶠ z : P × P in 𝓝 (x,y),
      Relation.EqvGen G z.1 z.2 → ∀ m ≥ N,
        dist ((f : M → M)^[m] (p z.1)) ((f : M → M)^[m] (p z.2)) < ε)
    (hpinj : ∀ x y, Relation.EqvGen G x y → p x = p y → x = y)
    {x y : P} (hxy : Relation.EqvGen G x y) (himage : H x = H y) : x = y := by
  let d : ℕ → P → P → ℝ := fun m x y ↦
    dist ((f : M → M)^[m] (p x)) ((f : M → M)^[m] (p y))
  obtain ⟨K, hK, hKR, hnormalize⟩ := compact_deck_normalized_equal_image_pairs
    (Relation.EqvGen G) hclosed H hproper p δ hdeck hproj hRdeck
  have hlocal : ∀ z ∈ K, ∀ ε > 0, ∃ N : ℕ, ∀ᶠ w : P × P in 𝓝 z,
      Relation.EqvGen G w.1 w.2 → ∀ m ≥ N, d m w.1 w.2 < ε := by
    intro z hz
    exact locally_uniform_decay_eqvGen G d (fun _ _ _ _ ↦ dist_comm _ _)
      (fun _ _ _ _ _ _ ↦ dist_triangle _ _ _) J hJ hJleaf hJfix hdiag hgen (hKR z hz)
  have hdecay := uniform_decay_on_compact_relation (Relation.EqvGen G) d K hK hKR hlocal
  exact eq_of_backward_normalized_leaf_decay (Relation.EqvGen G) H p B f hsem hRB hHB
    K hnormalize hdecay hpinj hxy himage

/-- The final Franks injectivity deduction once uniform decay has proved
injectivity on each leaf. The global opposite-leaf intersection has the same
H-image as both endpoints because its displacement lies in two disjoint
linear subspaces. Leafwise injectivity identifies all three points. -/
theorem injective_of_global_product_and_leaf_injectivity
    {P V : Type*} [AddCommGroup V] [Module ℝ V]
    (Lu Ls : P → P → Prop) (H : P → V)
    (hproduct : ∀ x y, ∃ z, Lu x z ∧ Ls y z)
    (U S : Submodule ℝ V) (hUS : Disjoint U S)
    (hu : ∀ x y, Lu x y → H y - H x ∈ U)
    (hs : ∀ x y, Ls x y → H y - H x ∈ S)
    (hinju : ∀ x y, Lu x y → H x = H y → x = y)
    (hinjs : ∀ x y, Ls x y → H x = H y → x = y) : Function.Injective H := by
  intro x y hxy
  obtain ⟨z, hxz, hyz⟩ := hproduct x y
  have hzero : H z - H x = 0 := Submodule.disjoint_def.mp hUS _
    (hu x z hxz) (by simpa only [hxy] using hs y z hyz)
  have hzx : H z = H x := sub_eq_zero.mp hzero
  exact (hinju x z hxz hzx.symm).trans
    (hinjs y z hyz (hxy.symm.trans hzx.symm)).symm


end HolomorphicAnosov.FranksOriginalCover
