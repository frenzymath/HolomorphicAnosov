import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.Topology.Covering.Deck

noncomputable section

namespace HolomorphicAnosov
open Ghys
open Set

/-- A locally projective developing map determines a unique deck holonomy homomorphism
into the effective Möbius group, making the map equivariant. (Thurston, §3.5, p. 35) -/
theorem transverse_mobius_deck_holonomy
    {M Y ι : Type*} [TopologicalSpace M] [TopologicalSpace Y]
    (q : ℕ) (b : ι → OpenPartialHomeomorph M ((Fin q → ℝ) × ℂ))
    (p : Y → M) (D : C(Y, ComplexProjectiveLine)) :
    let localForm : (Y → ComplexProjectiveLine) → Prop := fun D ↦
      ∀ y, ∃ i, ∃ g : ComplexMobiusTransformation, ∃ U : Set Y,
        IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (b i).source ∧
          EqOn D (fun w ↦ g.apply (complexProjectiveLineFinite ((b i (p w)).2))) U
    localForm D →
    (∀ D' : C(Y, ComplexProjectiveLine), localForm D' →
      ∃! a : ComplexMobiusTransformation, ∀ y, D' y = a.apply (D y)) →
    let G : Subgroup (Equiv.Perm ComplexProjectiveLine) :=
      (MulAction.toPermHom (GL (Fin 2) ℂ) ComplexProjectiveLine).range
    ∃! H : deck p →* G, ∀ γ : deck p, ∀ y,
      D ((γ : Y ≃ₜ Y) y) = (H γ).val (D y) := by
  classical
  intro localForm hD hglobal
  have hcompare : ∀ γ : deck p, ∃! a : ComplexMobiusTransformation,
      ∀ y, D ((γ : Y ≃ₜ Y) y) = a.apply (D y) := by
    intro γ
    let D' : C(Y, ComplexProjectiveLine) :=
      ⟨fun y ↦ D ((γ : Y ≃ₜ Y) y), D.continuous.comp (γ : Y ≃ₜ Y).continuous⟩
    apply hglobal D'
    intro y
    obtain ⟨i, g, U, hU, hy, hsub, heq⟩ := hD ((γ : Y ≃ₜ Y) y)
    refine ⟨i, g, (γ : Y ≃ₜ Y) ⁻¹' U, hU.preimage (γ : Y ≃ₜ Y).continuous,
      hy, ?_, ?_⟩
    · intro w hw
      have hm := hsub hw
      change p ((γ : Y ≃ₜ Y) w) ∈ (b i).source at hm
      change p w ∈ (b i).source
      simpa only [show p ((γ : Y ≃ₜ Y) w) = p w from congrFun γ.property w] using hm
    · intro w hw
      change D ((γ : Y ≃ₜ Y) w) = _
      simpa only [show p ((γ : Y ≃ₜ Y) w) = p w from congrFun γ.property w]
        using heq hw
  let G : Subgroup (Equiv.Perm ComplexProjectiveLine) :=
    (MulAction.toPermHom (GL (Fin 2) ℂ) ComplexProjectiveLine).range
  let toGroup : ComplexMobiusTransformation → G := fun a ↦
    ⟨a.val, by
      obtain ⟨A, hA⟩ := a.property
      exact ⟨A, Equiv.ext (fun z ↦ (hA z).symm)⟩⟩
  let ofGroup : G → ComplexMobiusTransformation := fun a ↦
    ⟨a.val, by
      obtain ⟨A, hA⟩ := a.property
      exact ⟨A, fun z ↦ congrArg (fun e : Equiv.Perm ComplexProjectiveLine ↦ e z) hA.symm⟩⟩
  have hc : ∀ γ : deck p, ∃! a : G,
      ∀ y, D ((γ : Y ≃ₜ Y) y) = a.val (D y) := by
    intro γ
    obtain ⟨a, ha, hu⟩ := hcompare γ
    refine ⟨toGroup a, ha, ?_⟩
    intro b hb
    have heq := hu (ofGroup b) hb
    exact Subtype.ext (congrArg (fun a : ComplexMobiusTransformation ↦ a.val) heq)
  choose h hh using fun γ ↦ (hc γ).exists
  have unique (γ : deck p) (a : G)
      (ha : ∀ y, D ((γ : Y ≃ₜ Y) y) = a.val (D y)) : a = h γ :=
    (hc γ).unique ha (hh γ)
  let H : deck p →* G :=
    { toFun := h
      map_one' := (unique 1 1 (fun _ ↦ rfl)).symm
      map_mul' := by
        intro γ δ
        apply (unique (γ * δ) (h γ * h δ) ?_).symm
        intro y
        change D ((γ : Y ≃ₜ Y) ((δ : Y ≃ₜ Y) y)) = (h γ).val ((h δ).val (D y))
        rw [hh γ, hh δ] }
  refine ⟨H, hh, ?_⟩
  intro K hK
  apply MonoidHom.ext
  intro γ
  exact unique γ (K γ) (hK γ)

end HolomorphicAnosov
