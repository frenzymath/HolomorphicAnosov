import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! This file transports continuous missing graphs and their complements through homeomorphisms
(Ghys, Lemma 5.2, pp. 599–600). -/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- The continuous missing graph transported by `e`, with value `e (u (e.symm q))` on the complement
of `e '' F` (Ghys, Lemma 5.2, pp. 599–600). -/
def transportMissing {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (e : P ≃ₜ Q) (F : Set P) (u : C({p : P // p ∉ F}, P)) :
    C({q : Q // q ∉ e '' F}, Q) :=
  let r : {q : Q // q ∉ e '' F} → {p : P // p ∉ F} :=
    fun q ↦ ⟨e.symm q.val, fun h ↦ q.property ⟨_, h, e.apply_symm_apply _⟩⟩
  ⟨fun q ↦ e (u (r q)), e.continuous.comp (u.continuous.comp
    ((e.symm.continuous.comp continuous_subtype_val).subtype_mk _))⟩

/-- The product homeomorphism `e.prodCongr e` maps the original graph complement onto the complement
of the transported graph (Ghys, Lemma 5.2, pp. 599–600). -/
theorem transportMissing_image {P Q : Type*}
    [TopologicalSpace P] [TopologicalSpace Q] (e : P ≃ₜ Q)
    (F : Set P) (u : C({p : P // p ∉ F}, P)) :
    (e.prodCongr e) '' {z : P × P | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} =
      {z : Q × Q | ∃ hp : z.1 ∉ e '' F,
        z.2 ≠ transportMissing e F u ⟨z.1, hp⟩} := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hneq⟩, rfl⟩
    have he : e y.1 ∉ e '' F := fun ⟨w, hw, hew⟩ ↦ hy (e.injective hew ▸ hw)
    refine ⟨he, ?_⟩
    change e y.2 ≠ e (u ⟨e.symm (e y.1), _⟩)
    simpa only [e.symm_apply_apply] using e.injective.ne hneq
  · rintro ⟨hz, hneq⟩
    have he : e.symm z.1 ∉ F := fun h ↦ hz ⟨_, h, e.apply_symm_apply _⟩
    refine ⟨(e.symm z.1, e.symm z.2), ⟨he, ?_⟩, ?_⟩
    · intro h
      apply hneq
      change z.2 = e (u ⟨e.symm z.1, _⟩)
      rw [← h, e.apply_symm_apply]
    · exact Prod.ext (e.apply_symm_apply _) (e.apply_symm_apply _)

end HolomorphicAnosov.Ghys
