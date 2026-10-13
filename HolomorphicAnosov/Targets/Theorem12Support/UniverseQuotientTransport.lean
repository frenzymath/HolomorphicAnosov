import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! A continuous real linear equivalence induces a homeomorphism between quotients by an integer
submodule and its image. This homeomorphism transports linear dynamical conjugacies. -/
noncomputable section
set_option autoImplicit false
universe u v x
namespace HolomorphicAnosov.UniverseQuotientTransport

variable {V : Type u} {W : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The integer submodule obtained as the image of `Γ` under `e`. -/
def transportedLattice (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) : Submodule ℤ W :=
  Γ.map (e.toLinearMap.restrictScalars ℤ)

/-- The additive subgroup underlying the transported lattice is the image of the additive subgroup
underlying `Γ`. -/
theorem transportedLattice_toAddSubgroup (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) :
    Γ.toAddSubgroup.map e.toAddEquiv.toAddMonoidHom =
      (transportedLattice e Γ).toAddSubgroup := rfl

/-- The additive equivalence between the quotients by `Γ` and its image under `e`. -/
def quotientEquiv (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) :
    (V ⧸ Γ.toAddSubgroup) ≃+ (W ⧸ (transportedLattice e Γ).toAddSubgroup) :=
  QuotientAddGroup.congr Γ.toAddSubgroup (transportedLattice e Γ).toAddSubgroup
    e.toAddEquiv (transportedLattice_toAddSubgroup e Γ)

@[simp] theorem quotientEquiv_mk (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) (v : V) :
    quotientEquiv e Γ (QuotientAddGroup.mk v) = QuotientAddGroup.mk (e v) := rfl

/-- The quotient equivalence induced by `e` is continuous. -/
theorem quotientEquiv_continuous (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) :
    Continuous (quotientEquiv e Γ) := by
  apply (QuotientAddGroup.isQuotientMap_mk Γ.toAddSubgroup).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp e.continuous

/-- The quotient equivalence induced by `e` is open. -/
theorem quotientEquiv_isOpenMap (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) :
    IsOpenMap (quotientEquiv e Γ) :=
  IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective
    (QuotientAddGroup.isOpenMap_coe.comp e.isOpenMap)

/-- The homeomorphism between the quotients by `Γ` and its image under `e`. -/
def quotientHomeomorph (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) :
    (V ⧸ Γ.toAddSubgroup) ≃ₜ (W ⧸ (transportedLattice e Γ).toAddSubgroup) :=
  (quotientEquiv e Γ).toEquiv.toHomeomorphOfContinuousOpen
    (quotientEquiv_continuous e Γ) (quotientEquiv_isOpenMap e Γ)

@[simp] theorem quotientHomeomorph_mk (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) (v : V) :
    quotientHomeomorph e Γ (QuotientAddGroup.mk v) = QuotientAddGroup.mk (e v) := rfl

@[simp] theorem quotientHomeomorph_symm_mk (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) (w : W) :
    (quotientHomeomorph e Γ).symm (QuotientAddGroup.mk w) =
      QuotientAddGroup.mk (e.symm w) := by
  apply (quotientHomeomorph e Γ).injective
  simp

/-- The continuous real linear automorphism `e ∘ A ∘ e⁻¹` on `W`. -/
def transportedDynamics (e : V ≃L[ℝ] W) (A : V ≃L[ℝ] V) : W ≃L[ℝ] W :=
  e.symm.trans (A.trans e)

/-- The quotient homeomorphism sends the class of `A v` to the class of the transported automorphism
applied to `e v`. -/
theorem quotientHomeomorph_dynamics_mk (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V)
    (A : V ≃L[ℝ] V) (v : V) :
    quotientHomeomorph e Γ (QuotientAddGroup.mk (A v)) =
      QuotientAddGroup.mk (transportedDynamics e A (e v)) := by
  simp [transportedDynamics]

/-- A conjugacy to linear dynamics on the quotient by `Γ` transports to a conjugacy on the quotient
by its image under `e`. -/
theorem transported_model_conjugacy {X : Type x} [TopologicalSpace X]
    (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) (A : V ≃L[ℝ] V)
    (h : X ≃ₜ (V ⧸ Γ.toAddSubgroup)) (f : X → X)
    (hdyn : ∀ (a : X) (v : V), QuotientAddGroup.mk v = h a →
      h (f a) = QuotientAddGroup.mk (A v)) :
    ∀ (a : X) (w : W), QuotientAddGroup.mk w =
      (h.trans (quotientHomeomorph e Γ)) a →
      (h.trans (quotientHomeomorph e Γ)) (f a) =
        QuotientAddGroup.mk (transportedDynamics e A w) := by
  intro a w hw
  have hv : QuotientAddGroup.mk (e.symm w) = h a := by
    apply (quotientHomeomorph e Γ).injective
    simpa using hw
  change quotientHomeomorph e Γ (h (f a)) = _
  rw [hdyn a (e.symm w) hv]
  simp [transportedDynamics]

end HolomorphicAnosov.UniverseQuotientTransport
