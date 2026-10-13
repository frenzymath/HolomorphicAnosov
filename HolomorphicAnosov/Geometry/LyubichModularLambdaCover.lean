import HolomorphicAnosov.Geometry.LyubichReflectionGluingCover
import HolomorphicAnosov.Geometry.LyubichUnitDiskUniversalCover

/-! The file constructs the normalized modular-lambda covering from reflected ideal-triangle charts. (Lyubich, §2.4.13, Exercise 2.49) -/

namespace HolomorphicAnosov

open scoped ComplexConjugate

/-- The marked ideal-triangle Schwarz construction gives a universal holomorphic cover of the twice-punctured complex plane, with its original normalization. (Lyubich, §2.4.13, Exercise 2.49) -/
theorem lyubich_modular_lambda_cover (T : MarkedIdealDiskTriangle) :
    ∃ lam : ℂ → ℂ,
      DifferentiableOn ℂ lam {z : ℂ | ‖z‖ < 1} ∧
      IsCoveringMapOn (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val)
        {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∧
      Set.range (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val) =
        {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∧
      SimplyConnectedSpace {z : ℂ // ‖z‖ < 1} ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        ∃ e : OpenPartialHomeomorph ℂ ℂ,
          z ∈ e.source ∧ e.source ⊆ {z : ℂ | ‖z‖ < 1} ∧
          Set.EqOn e lam e.source ∧
          DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target) ∧
      (∃ F : OpenPartialHomeomorph ℂ ℂ,
        F.source = T.interiorSet ∧ F.target = {w : ℂ | 0 < w.im} ∧
        Set.EqOn F lam T.interiorSet ∧
        DifferentiableOn ℂ F F.source ∧ DifferentiableOn ℂ F.symm F.target) ∧
      (∃ b : ℂ → OnePoint ℂ,
        ContinuousOn b T.closedSet ∧
        Set.EqOn b (fun z ↦ (lam z : OnePoint ℂ)) T.interiorSet ∧
        b (T.vertex 0) = (0 : ℂ) ∧ b (T.vertex 1) = (1 : ℂ) ∧
        b (T.vertex 2) = OnePoint.infty) ∧
      ∀ (w : List (Fin 3)) (z : ℂ), z ∈ T.interiorSet →
        lam (T.itineraryMap w z) = ((fun u : ℂ ↦ conj u)^[w.length]) (lam z) := by
  obtain ⟨F, hsource, htarget, hhol, hinv, b, hbcont, hbeq, hb0, hb1, hb2⟩ :=
    markedIdealDiskTriangle_normalized_initial_map T
  obtain ⟨lam, hlam, hcover, hrange, hlocal, hFlam, hboundary, hitinerary⟩ :=
    lyubich_reflection_gluing_cover T F hsource htarget hhol hinv
      b hbcont hbeq hb0 hb1 hb2
  exact ⟨lam, hlam, hcover, hrange, lyubich_unit_disk_universal_cover_source,
    hlocal, ⟨F, hsource, htarget, hFlam, hhol, hinv⟩, hboundary, hitinerary⟩

end HolomorphicAnosov
