import HolomorphicAnosov.Geometry.LyubichInitialTriangleNormalization
import HolomorphicAnosov.Geometry.LyubichReflectionWordPairsG11

/-! The file glues Schwarz-reflected charts to construct the modular-lambda covering. (Lyubich, §2.4.13, Exercise 2.49(ii)) -/

namespace HolomorphicAnosov

open scoped ComplexConjugate

/-- Glue the normalized first-sheet map across the ideal-triangle reflection tiling to obtain the modular-lambda covering data. (Lyubich, §2.4.13, Exercise 2.49(ii)) -/
theorem lyubich_reflection_gluing_cover
    (T : MarkedIdealDiskTriangle)
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFsource : F.source = T.interiorSet)
    (hFtarget : F.target = {w : ℂ | 0 < w.im})
    (hFhol : DifferentiableOn ℂ F F.source)
    (hFsymm : DifferentiableOn ℂ F.symm F.target)
    (b : ℂ → OnePoint ℂ)
    (hbcont : ContinuousOn b T.closedSet)
    (hbeq : Set.EqOn b (fun z : ℂ ↦ (F z : OnePoint ℂ)) T.interiorSet)
    (hb0 : b (T.vertex 0) = (0 : ℂ))
    (hb1 : b (T.vertex 1) = (1 : ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty) :
    ∃ lam : ℂ → ℂ,
      DifferentiableOn ℂ lam {z : ℂ | ‖z‖ < 1} ∧
      IsCoveringMapOn (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val)
        {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∧
      Set.range (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val) =
        {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        ∃ e : OpenPartialHomeomorph ℂ ℂ,
          z ∈ e.source ∧ e.source ⊆ {z : ℂ | ‖z‖ < 1} ∧
          Set.EqOn e lam e.source ∧
          DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target) ∧
      Set.EqOn F lam T.interiorSet ∧
      (∃ b' : ℂ → OnePoint ℂ,
        ContinuousOn b' T.closedSet ∧
        Set.EqOn b' (fun z ↦ (lam z : OnePoint ℂ)) T.interiorSet ∧
        b' (T.vertex 0) = (0 : ℂ) ∧
        b' (T.vertex 1) = (1 : ℂ) ∧
        b' (T.vertex 2) = OnePoint.infty) ∧
      ∀ (w : List (Fin 3)) (z : ℂ), z ∈ T.interiorSet →
        lam (T.itineraryMap w z) = ((fun u : ℂ ↦ conj u)^[w.length]) (lam z) := by
  have hreflection {p q a c : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
      (ha : ‖a‖ = 1) (hc : ‖c‖ = 1) (hac : a ≠ c)
      (he : IdealDiskTriangle.openSide p q = IdealDiskTriangle.openSide a c) :
      idealDiskSideReflection p q = idealDiskSideReflection a c :=
    IdealDiskTriangle.reflection_eq_of_side_eq hp hq ha hc hpq hac he
  obtain ⟨hbinj,hbsurj⟩ := T.boundary_chart_model F hFsource hFtarget hFsymm b hbcont hbeq
  have hclosure := markedIdealDiskTriangle_closure_interior_eq_closedSet T
  obtain ⟨D,hDs,hDD,hDt,hDh,hDi,hD₁,hD₂,hDseam⟩ := T.exists_word_pair_charts F
    hFsource hFtarget hFhol hclosure b hbcont hbinj hbeq hb0 hb1 hb2
  obtain ⟨lam,hlam,hDeq,hword,hlocal⟩ := T.glue_actual_word_pairs F hFsource hreflection
    D hDs hDD hDh hDi hD₁ hD₂
  obtain ⟨hsep,hΩ⟩ := T.slitTarget_cover F hFsource hFtarget hclosure b hbcont hbinj hbeq
    hb0 hb1 hb2 hbsurj
  obtain ⟨hcover,hrange⟩ := T.covering_of_actual_word_pairs hreflection b lam D hDs hDD hDt
    hDeq hDseam hsep hΩ
  have hinit : Set.EqOn F lam T.interiorSet := by
    intro z hz
    exact hword [] (show z ∈ T.wordTile [] from ⟨z,hz,rfl⟩)
  refine ⟨lam,hlam,hcover,hrange,hlocal,hinit,⟨b,hbcont,?_,hb0,hb1,hb2⟩,?_⟩
  · intro z hz
    exact (hbeq hz).trans (congrArg (fun x : ℂ ↦ (x : OnePoint ℂ)) (hinit hz))
  · intro w z hz
    rw [← hword w (Set.mem_image_of_mem _ hz)]
    rw [T.itineraryChart_apply F (fun x hx ↦ (hFsource ▸ hx).1) w (hFsource.symm ▸ hz),
      hinit hz]

end HolomorphicAnosov
