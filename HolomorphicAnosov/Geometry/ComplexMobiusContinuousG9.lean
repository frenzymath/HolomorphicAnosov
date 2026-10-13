import HolomorphicAnosov.Ghys.AffineProjectiveStructure

/-! This file proves continuity of the native effective action of complex Möbius transformations. (Demailly, V §15.A, p. 277; Thurston, §§3.5, 4.8).
-/

noncomputable section
open Topology _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Every effective complex Möbius transformation is continuous for the native homogeneous quotient topology. (Demailly, V §15.A, p. 277; Thurston, §§3.5, 4.8). -/
theorem ComplexMobiusTransformation.continuous_apply (g : ComplexMobiusTransformation) :
    Continuous g.apply := by
  obtain ⟨m, hm⟩ := g.property
  have hlin : Continuous (fun v : Fin 2 → ℂ ↦ m • v) :=
    (DistribMulAction.toModuleEnd ℂ (Fin 2 → ℂ) m).continuous_of_finiteDimensional
  have hsub : Continuous (fun v : {v : Fin 2 → ℂ // v ≠ 0} ↦
      (⟨m • v.val, (smul_ne_zero_iff_ne m).mpr v.property⟩ :
        {v : Fin 2 → ℂ // v ≠ 0})) :=
    (hlin.comp continuous_subtype_val).subtype_mk _
  apply (isQuotientMap_quotient_mk' : IsQuotientMap
    (Projectivization.mk' ℂ : {v : Fin 2 → ℂ // v ≠ 0} → ComplexProjectiveLine)).continuous_iff.mpr
  have hq : Continuous (Projectivization.mk' ℂ :
      {v : Fin 2 → ℂ // v ≠ 0} → ComplexProjectiveLine) := continuous_quotient_mk'
  exact (hq.comp hsub).congr (fun v ↦ (hm (Projectivization.mk' ℂ v)).symm)

end HolomorphicAnosov.Ghys
