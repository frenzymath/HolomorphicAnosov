import Mathlib.Topology.Baire.LocallyCompactRegular
import HolomorphicAnosov.Dynamics.ManeDenseOrbitOfSaturation
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.GroupTheory.Perm.Basic

/-! Dense full orbits on compact invariant transitive sets (Mañé, I§11, Prop. 11.4; Shub, Thm.
8.13). -/
namespace HolomorphicAnosov
open Set
universe u

/-- Positive-time open-set transitivity on a nonempty compact invariant set gives a point whose full
orbit has closure equal to that set (Mañé, I§11, Prop. 11.4; Shub, Thm. 8.13). -/
theorem smale_dense_full_orbit_of_transitivity
    {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    (f : X ≃ₜ X) (A : Set X) (hne : A.Nonempty) (hA : IsCompact A)
    (hinv : f '' A = A)
    (htrans : ∀ U V : Set X, IsOpen U → (U ∩ A).Nonempty →
      IsOpen V → (V ∩ A).Nonempty →
      ∃ k : ℕ, ((f : X → X)^[k] '' (U ∩ A) ∩ V).Nonempty) :
    ∃ x ∈ A, closure (Set.range (fun k : ℤ ↦ (f.toEquiv ^ k) x)) = A := by
  let : Nonempty A := hne.to_subtype
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hmap {x : X} (hx : x ∈ A) : f x ∈ A := hinv ▸ mem_image_of_mem f hx
  let g : A → A := fun x ↦ ⟨f x, hmap x.property⟩
  have hg : Continuous g := (f.continuous.comp continuous_subtype_val).subtype_mk _
  have hiter (k : ℕ) (x : A) : (g^[k] x).val = (f : X → X)^[k] x.val := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', g, ih]
  have hsat : ∀ U : Set A, IsOpen U → U.Nonempty →
      Dense (⋃ k : ℕ, g^[k] ⁻¹' U) := by
    intro U hU hUn
    apply dense_iff_inter_open.mpr
    intro V hV hVn
    obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.mp hU
    obtain ⟨V', hV', rfl⟩ := isOpen_induced_iff.mp hV
    obtain ⟨u, hu⟩ := hUn
    obtain ⟨v, hv⟩ := hVn
    obtain ⟨k, z, ⟨x, hx, rfl⟩, hz⟩ :=
      htrans V' U' hV' ⟨v.val, hv, v.property⟩ hU' ⟨u.val, hu, u.property⟩
    refine ⟨⟨x, hx.2⟩, hx.1, mem_iUnion.mpr ⟨k, ?_⟩⟩
    change (g^[k] ⟨x, hx.2⟩).val ∈ U'
    rw [hiter]
    exact hz
  obtain ⟨x, hx⟩ := mane_exists_dense_forward_orbit_of_dense_saturation g hg hsat
  refine ⟨x.val, x.property, ?_⟩
  have hforward : closure (range (fun k : ℕ ↦ (f : X → X)^[k] x.val)) = A := by
    have hc := (hA.isClosed.isClosedEmbedding_subtypeVal).closure_image_eq
      (range (fun k : ℕ ↦ g^[k] x))
    rw [hx.closure_eq] at hc
    have himage : Subtype.val '' range (fun k : ℕ ↦ g^[k] x) =
        range (fun k : ℕ ↦ (f : X → X)^[k] x.val) := by
      rw [← Set.range_comp]
      congr 1
      funext k
      exact hiter k x
    simpa only [himage, Set.image_univ, Subtype.range_coe] using hc
  apply Set.Subset.antisymm
  · apply closure_minimal _ hA.isClosed
    rintro y ⟨k, rfl⟩
    have hinv' {x : X} (hx : x ∈ A) : f.symm x ∈ A := by
      obtain ⟨y, hy, hxy⟩ := hinv.symm ▸ hx
      simpa only [← hxy, f.symm_apply_apply] using hy
    exact zpow_induction_left
      (P := fun e : Equiv.Perm X ↦ e x.val ∈ A) x.property
      (fun e he ↦ hmap he) (fun e he ↦ hinv' he) k
  · apply hforward.symm.subset.trans
    apply closure_mono
    rintro y ⟨k, rfl⟩
    refine ⟨(k : ℤ), ?_⟩
    simp only [zpow_natCast, Equiv.Perm.coe_pow]
    rfl

end HolomorphicAnosov
