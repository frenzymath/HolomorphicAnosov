import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.unstablePlaque
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Finite

open Set Filter Topology _root_.Topology

namespace HolomorphicAnosov.Bowen.RectangleSlicesPreparation

/-- Finite cover by receiving unstable slices, the covering step of Bowen's Lemma 14
(*Markov Partitions for Axiom A Diffeomorphisms*, 1970, p.732). The explicit local-domain
argument is an agent expansion of the source's assertion that the inverse slice interiors
cover the seed. At a seed point, continuity controls the finitely many backward iterates
before time `m`. Thereafter inverse and forward iterates cancel, and contraction on the
common source plaque bounds all distances by the original distance. A relative neighborhood
therefore maps into the receiving `a`-plaque, which saturation puts in `A`. Compactness
selects finitely many such neighborhoods. This theorem asserts no bracket identity and
requires no global map between full plaques. -/
theorem finite_unstable_slice_cover
    {X I : Type*} [MetricSpace X] (f : X ≃ₜ X) {γ a lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (ha : 0 < a) (haγ : a ≤ γ)
    (hcontract : ∀ (b y z : X) (n : ℕ),
      y ∈ unstablePlaque f γ b → z ∈ unstablePlaque f γ b →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    {C : Set X} (hC : IsCompact C) {b : X} (hCb : C ⊆ unstablePlaque f γ b)
    (m : ℕ) (A : I → Set X) (F : X → I)
    (hsat : ∀ z ∈ C, unstablePlaque f a ((f ^ m) z) ⊆ A (F ((f ^ m) z))) :
    ∃ s : Finset C, (f ^ m) '' C ⊆ ⋃ z ∈ s,
      A (F ((f ^ m) z)) ∩ unstablePlaque f γ ((f ^ m) z) := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let U : C → Set C := fun z ↦ {v | (f ^ m) v ∈
    A (F ((f ^ m) z)) ∩ unstablePlaque f γ ((f ^ m) z)}
  have hU : ∀ z : C, U z ∈ 𝓝 z := by
    intro z
    have hprefix : ∀ n : Fin m, ∀ᶠ v : C in 𝓝 z,
        dist ((f.symm ^ (n : ℕ)) ((f ^ m) v))
          ((f.symm ^ (n : ℕ)) ((f ^ m) z)) < a := by
      intro n
      have hc : Continuous (fun v : C ↦
          dist ((f.symm ^ (n : ℕ)) ((f ^ m) v))
            ((f.symm ^ (n : ℕ)) ((f ^ m) z))) :=
        (((f.symm ^ (n : ℕ)).continuous.comp (f ^ m).continuous).comp
          continuous_subtype_val).dist continuous_const
      exact hc.continuousAt.eventually_lt_const (by simpa using ha)
    have hall : ∀ᶠ v : C in 𝓝 z, ∀ n : Fin m,
        dist ((f.symm ^ (n : ℕ)) ((f ^ m) v))
          ((f.symm ^ (n : ℕ)) ((f ^ m) z)) < a :=
      Filter.eventually_all.mpr hprefix
    have hball : ∀ᶠ v : C in 𝓝 z, dist (v : X) z < a :=
      (continuous_subtype_val.dist continuous_const).continuousAt.eventually_lt_const
        (by simpa using ha)
    filter_upwards [hall, hball] with v hv hvz
    have hsmall : (f ^ m) v ∈ unstablePlaque f a ((f ^ m) z) := by
      intro n
      by_cases hnm : n < m
      · exact (hv ⟨n, hnm⟩).le
      · have hmn : m ≤ n := Nat.le_of_not_gt hnm
        have hcancel : ∀ w : X,
            (f.symm ^ n) ((f ^ m) w) = (f.symm ^ (n - m)) w := by
          intro w
          have heq : f.symm ^ n * f ^ m = f.symm ^ (n - m) := by
            conv_lhs => rw [← Nat.sub_add_cancel hmn, pow_add]
            change f.symm ^ (n - m) * (f⁻¹) ^ m * f ^ m = _
            rw [inv_pow, mul_assoc, inv_mul_cancel, mul_one]
          simpa only [Homeomorph.mul_apply] using congrArg (fun g : X ≃ₜ X ↦ g w) heq
        rw [hcancel, hcancel]
        exact ((hcontract b v z (n - m) (hCb v.property) (hCb z.property)).trans
          (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam0 hlam1))).trans hvz.le
    exact ⟨hsat z z.property hsmall, fun n ↦ (hsmall n).trans haγ⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun z : C ↦ interior (U z)) (fun _ ↦ isOpen_interior)
    (fun z _ ↦ mem_iUnion.mpr ⟨z, mem_interior_iff_mem_nhds.mpr (hU z)⟩)
  refine ⟨s, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp (hs (show (⟨z, hz⟩ : C) ∈ univ from mem_univ _))
  have hzv' : (⟨z, hz⟩ : C) ∈ U v := interior_subset hzv
  exact mem_iUnion₂.mpr ⟨v, hv, hzv'⟩

end HolomorphicAnosov.Bowen.RectangleSlicesPreparation

