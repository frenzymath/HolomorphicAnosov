import Mathlib

/-! Translation of sets and its existential membership characterization. -/

open Set

namespace HolomorphicAnosov.Theorem12LiftedFoliationAssembly

noncomputable section
universe w

theorem translated_image_eq {W : Type w} [AddCommGroup W]
    (a : W) (S : Set W) : (fun v ↦ a + v) '' S = {v | ∃ w : S, v = a + w.val} := by
  ext v
  constructor
  · rintro ⟨w,hw,hv⟩
    exact ⟨⟨w,hw⟩,hv.symm⟩
  · rintro ⟨w,hv⟩
    exact ⟨w.val,w.property,hv.symm⟩

end
end HolomorphicAnosov.Theorem12LiftedFoliationAssembly
