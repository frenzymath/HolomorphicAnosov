import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Lipschitz

/-! This file defines forward and backward transport of continuous homogeneous sections and proves
their inverse and fixed-point laws. It also bounds the Lipschitz constant of the inverse of an
expanding bijection (Ghys, Lemma 3.3, pp. 592–593). -/

namespace HolomorphicAnosov.Ghys.SectionTransport

universe u v w

variable {J₁ : Type u} {J₂ : Type v} {W : Type w}
variable [TopologicalSpace J₁] [TopologicalSpace J₂]

/-- The set of continuous sections of `p` that intertwine the scaling maps `a₁` and `a₂` (Ghys,
Lemma 3.3, p. 592). -/
def sections (p : C(J₂, J₁)) (a₁ : W → J₁ → J₁) (a₂ : W → J₂ → J₂) :
    Set C(J₁, J₂) :=
  {s | (∀ x, p (s x) = x) ∧ ∀ w x, s (a₁ w x) = a₂ w (s x)}

/-- The subtype of continuous homogeneous sections of `p` (Ghys, Lemma 3.3, p. 592). -/
abbrev Section (p : C(J₂, J₁)) (a₁ : W → J₁ → J₁) (a₂ : W → J₂ → J₂) :=
  {s : C(J₁, J₂) // s ∈ sections p a₁ a₂}

/-- The continuous forward transport `e₂ ∘ s ∘ e₁⁻¹` (Ghys, Lemma 3.3, p. 592). -/
def forwardMap (e₁ : J₁ ≃ₜ J₁) (e₂ : J₂ ≃ₜ J₂) (s : C(J₁, J₂)) : C(J₁, J₂) where
  toFun x := e₂ (s (e₁.symm x))
  continuous_toFun := e₂.continuous_toFun.comp (s.continuous.comp e₁.continuous_invFun)

/-- The continuous backward transport `e₂⁻¹ ∘ s ∘ e₁` (Ghys, Lemma 3.3, p. 592). -/
def backwardMap (e₁ : J₁ ≃ₜ J₁) (e₂ : J₂ ≃ₜ J₂) (s : C(J₁, J₂)) : C(J₁, J₂) where
  toFun x := e₂.symm (s (e₁ x))
  continuous_toFun := e₂.continuous_invFun.comp (s.continuous.comp e₁.continuous_toFun)

/-- Forward and backward transport preserve homogeneous sections when the homeomorphisms intertwine
`p` and commute with scaling (Ghys, Lemma 3.3, pp. 592–593). -/
theorem transport_preserves_sections
    (p : C(J₂, J₁)) (a₁ : W → J₁ → J₁) (a₂ : W → J₂ → J₂)
    (e₁ : J₁ ≃ₜ J₁) (e₂ : J₂ ≃ₜ J₂)
    (hp : ∀ z, p (e₂ z) = e₁ (p z))
    (h₁ : ∀ w x, e₁ (a₁ w x) = a₁ w (e₁ x))
    (h₂ : ∀ w z, e₂ (a₂ w z) = a₂ w (e₂ z))
    (s : C(J₁, J₂)) (hs : s ∈ sections p a₁ a₂) :
    forwardMap e₁ e₂ s ∈ sections p a₁ a₂ ∧
      backwardMap e₁ e₂ s ∈ sections p a₁ a₂ := by
  rcases hs with ⟨hs, ha⟩
  constructor
  · constructor
    · intro x
      change p (e₂ (s (e₁.symm x))) = x
      rw [hp, hs, e₁.apply_symm_apply]
    · intro w x
      change e₂ (s (e₁.symm (a₁ w x))) = a₂ w (e₂ (s (e₁.symm x)))
      rw [show e₁.symm (a₁ w x) = a₁ w (e₁.symm x) from
        e₁.injective (by simp only [e₁.apply_symm_apply, h₁])]
      rw [ha, h₂]
  · constructor
    · intro x
      change p (e₂.symm (s (e₁ x))) = x
      apply e₁.injective
      rw [← hp, e₂.apply_symm_apply, hs]
    · intro w x
      change e₂.symm (s (e₁ (a₁ w x))) = a₂ w (e₂.symm (s (e₁ x)))
      apply e₂.injective
      rw [e₂.apply_symm_apply, h₁, ha, h₂, e₂.apply_symm_apply]

/-- The forward self-map of homogeneous sections given by `e₂ ∘ s ∘ e₁⁻¹` (Ghys, Lemma 3.3, p. 592). -/
def forward
    (p : C(J₂, J₁)) (a₁ : W → J₁ → J₁) (a₂ : W → J₂ → J₂)
    (e₁ : J₁ ≃ₜ J₁) (e₂ : J₂ ≃ₜ J₂)
    (hp : ∀ z, p (e₂ z) = e₁ (p z))
    (h₁ : ∀ w x, e₁ (a₁ w x) = a₁ w (e₁ x))
    (h₂ : ∀ w z, e₂ (a₂ w z) = a₂ w (e₂ z))
    (s : Section p a₁ a₂) : Section p a₁ a₂ :=
  ⟨forwardMap e₁ e₂ s.val,
    (transport_preserves_sections p a₁ a₂ e₁ e₂ hp h₁ h₂ s.val s.property).1⟩

/-- The backward self-map of homogeneous sections given by `e₂⁻¹ ∘ s ∘ e₁` (Ghys, Lemma 3.3, p.
592). -/
def backward
    (p : C(J₂, J₁)) (a₁ : W → J₁ → J₁) (a₂ : W → J₂ → J₂)
    (e₁ : J₁ ≃ₜ J₁) (e₂ : J₂ ≃ₜ J₂)
    (hp : ∀ z, p (e₂ z) = e₁ (p z))
    (h₁ : ∀ w x, e₁ (a₁ w x) = a₁ w (e₁ x))
    (h₂ : ∀ w z, e₂ (a₂ w z) = a₂ w (e₂ z))
    (s : Section p a₁ a₂) : Section p a₁ a₂ :=
  ⟨backwardMap e₁ e₂ s.val,
    (transport_preserves_sections p a₁ a₂ e₁ e₂ hp h₁ h₂ s.val s.property).2⟩

/-- Forward and backward transport are inverse, and forward fixed points are precisely the sections
intertwining the given homeomorphisms (Ghys, Lemma 3.3, pp. 592–593). -/
theorem transport_inverse_and_fixed_iff
    (p : C(J₂, J₁)) (a₁ : W → J₁ → J₁) (a₂ : W → J₂ → J₂)
    (e₁ : J₁ ≃ₜ J₁) (e₂ : J₂ ≃ₜ J₂)
    (hp : ∀ z, p (e₂ z) = e₁ (p z))
    (h₁ : ∀ w x, e₁ (a₁ w x) = a₁ w (e₁ x))
    (h₂ : ∀ w z, e₂ (a₂ w z) = a₂ w (e₂ z)) :
    let Q := forward p a₁ a₂ e₁ e₂ hp h₁ h₂
    let P := backward p a₁ a₂ e₁ e₂ hp h₁ h₂
    Function.LeftInverse P Q ∧ Function.RightInverse P Q ∧
      ∀ s : Section p a₁ a₂, Q s = s ↔ ∀ x, s.val (e₁ x) = e₂ (s.val x) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro s
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    change e₂.symm (e₂ (s.val (e₁.symm (e₁ x)))) = s.val x
    simp only [Homeomorph.symm_apply_apply]
  · intro s
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    change e₂ (e₂.symm (s.val (e₁ (e₁.symm x)))) = s.val x
    simp only [Homeomorph.apply_symm_apply]
  · intro s
    constructor
    · intro h x
      have hx := congrArg (fun t : Section p a₁ a₂ ↦ t.val (e₁ x)) h
      simpa only [forward, forwardMap, ContinuousMap.coe_mk,
        Homeomorph.symm_apply_apply] using hx.symm
    · intro h
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      change e₂ (s.val (e₁.symm x)) = s.val x
      simpa only [e₁.apply_symm_apply] using (h (e₁.symm x)).symm

/-- The inverse of a bijection expanding distances by a positive factor `c` is Lipschitz with
constant `c⁻¹` (Ghys, Lemma 3.3, p. 592). -/
theorem expansion_inverse_lipschitz
    {X : Type*} [MetricSpace X] (T : X ≃ X) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x y, c * dist x y ≤ dist (T x) (T y)) :
    LipschitzWith (Real.toNNReal c⁻¹) T.symm := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
  apply (le_inv_mul_iff₀ hc).mpr
  simpa only [T.apply_symm_apply] using hT (T.symm x) (T.symm y)

end HolomorphicAnosov.Ghys.SectionTransport
