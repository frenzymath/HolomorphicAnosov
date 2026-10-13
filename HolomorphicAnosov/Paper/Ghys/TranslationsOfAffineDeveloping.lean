import HolomorphicAnosov.Paper.Ghys.ProjectiveDeveloping
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.FreeAffineActionTranslations
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.GlobalHolonomy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Deck
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.Paper.Ghys.DeckIdentityOfFixedPoint

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- Under the affine developing equation and the single-sheet fibre property, the deck action is faithful and its affine coordinate maps are translations with an additive translation homomorphism. (Ghys, Theorem B, p. 598; Hatcher, Prop. 1.34) -/
theorem translations_of_affine_developing
    {G E M : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace M]
    [PreconnectedSpace E] {p : E → M} (hp : IsCoveringMap p)
    (D : E → ℂ) (hD : Function.Surjective D) (δ : G ≃* deck p)
    (a b : G → ℂ)
    (hequiv : ∀ g e, D ((δ g : E ≃ₜ E) e) = a g * D e + b g)
    (hfibre : ∀ z : ℂ, Set.InjOn p {e | D e = z}) :
    ∃ tau : G →* Multiplicative ℂ,
      Function.Injective tau ∧
      (∀ g e, D ((δ g : E ≃ₜ E) e) = D e + (tau g).toAdd) ∧
      (∀ g h : G, g * h = h * g) ∧
      (∀ g : G, ∀ n : ℕ, 0 < n → g ^ n = 1 → g = 1) := by
  have hidentity : ∀ z : ℂ, a 1 * z + b 1 = z := by
    intro z
    obtain ⟨e, rfl⟩ := hD z
    simpa only [map_one, OneMemClass.coe_one, Homeomorph.one_apply] using (hequiv 1 e).symm
  have hcomposition : ∀ (g h : G) (z : ℂ),
      a (g * h) * z + b (g * h) = a g * (a h * z + b h) + b g := by
    intro g h z
    obtain ⟨e, rfl⟩ := hD z
    calc
      a (g * h) * D e + b (g * h) = D ((δ (g * h) : E ≃ₜ E) e) :=
        (hequiv (g * h) e).symm
      _ = D ((δ g : E ≃ₜ E) ((δ h : E ≃ₜ E) e)) := by rw [map_mul]; rfl
      _ = a g * (a h * D e + b h) + b g := by rw [hequiv, hequiv]
  have ha : ∀ g : G, a g ≠ 0 := by
    intro g hg
    have h0 := hcomposition g⁻¹ g 0
    have h1 := hcomposition g⁻¹ g 1
    rw [inv_mul_cancel, hidentity] at h0 h1
    simp only [hg, zero_mul, zero_add] at h0 h1
    exact zero_ne_one (h0.trans h1.symm)
  have hfree : ∀ g z, a g * z + b g = z → g = 1 := by
    intro g z hg
    obtain ⟨e, he⟩ := hD z
    have hfixed : (δ g : E ≃ₜ E) e = e := by
      apply hfibre z
      · show D ((δ g : E ≃ₜ E) e) = z
        rw [hequiv, he, hg]
      · exact he
      · exact deck.proj_smul (δ g) e
    apply δ.injective
    rw [map_one]
    exact deck_identity_of_fixed_point hp (δ g) e hfixed
  obtain ⟨hslopes, hb1, hbmul, hbinj, hcomm, htf⟩ :=
    freeAffineActionTranslations a b ha hidentity hcomposition hfree
  let tau : G →* Multiplicative ℂ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (b g)
      map_one' := hb1
      map_mul' := hbmul }
  refine ⟨tau, ?_, ?_, hcomm, ?_⟩
  · intro g h hgh
    exact hbinj (congrArg Multiplicative.toAdd hgh)
  · intro g e
    change D ((δ g : E ≃ₜ E) e) = D e + b g
    rw [hequiv, hslopes, one_mul]
  · let : IsMulTorsionFree G := htf
    intro g n hn hg
    exact (pow_eq_one_iff_left hn.ne').mp hg

end HolomorphicAnosov.Ghys

