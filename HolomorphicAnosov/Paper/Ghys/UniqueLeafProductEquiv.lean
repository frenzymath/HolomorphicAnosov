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


noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- If every equivalence class meets each coordinate fibre exactly once, the space is equivalent to the product of one fibre with the coordinate space. -/
theorem product_equiv_of_unique_leaf_intersections
    {E Z : Type*} (R : Setoid E) (D : E → Z) (z₀ : Z)
    (hunique : ∀ e : E, ∀ z : Z, ∃! y : E, R.r e y ∧ D y = z) :
    ∃ B : ({e : E // D e = z₀} × Z) ≃ E,
      (∀ r z, D (B (r, z)) = z) ∧ (∀ r z, R.r r.val (B (r, z))) ∧
      ∀ r : {e : E // D e = z₀}, B (r, z₀) = r.val := by
  classical
  let P (e : E) (z : Z) : E := Classical.choose (hunique e z)
  have hP (e : E) (z : Z) : R.r e (P e z) ∧ D (P e z) = z :=
    (Classical.choose_spec (hunique e z)).1
  have hPu (e : E) (z : Z) (y : E) (hy : R.r e y ∧ D y = z) : y = P e z :=
    (Classical.choose_spec (hunique e z)).2 y hy
  let B : ({e : E // D e = z₀} × Z) ≃ E :=
    { toFun := fun q ↦ P q.1.val q.2
      invFun := fun e ↦ (⟨P e z₀, (hP e z₀).2⟩, D e)
      left_inv := by
        rintro ⟨r, z⟩
        apply Prod.ext
        · apply Subtype.ext
          exact (hPu (P r.val z) z₀ r.val ⟨R.symm (hP r.val z).1, r.property⟩).symm
        · exact (hP r.val z).2
      right_inv := by
        intro e
        exact (hPu (P e z₀) (D e) e ⟨R.symm (hP e z₀).1, rfl⟩).symm }
  refine ⟨B, fun r z ↦ (hP r.val z).2, fun r z ↦ (hP r.val z).1, ?_⟩
  intro r
  exact (hPu r.val z₀ r.val ⟨R.refl _, r.property⟩).symm

end HolomorphicAnosov.Ghys

