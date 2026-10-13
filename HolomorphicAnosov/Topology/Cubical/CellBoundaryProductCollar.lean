import HolomorphicAnosov.Topology.Cubical.CompactOpenProductCollar
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import HolomorphicAnosov.Topology.CWComplex.EuclideanSupRadialHomeomorph
import HolomorphicAnosov.Topology.Cubical.CoordinateCellNormalization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Boundary product collar for a closed coordinate cell

Source: Hatcher, *Algebraic Topology*, Lemma 2.34, pp. 137–139, and Appendix
A.2–A.4, pp. 521–522. The explicit radial convex-body homeomorphism used in
the proof is Bredon, *Topology and Geometry*, I.16.2–I.16.4, pp. 56–57.

The radial normalization identifies the boundary with a unit sphere times
zero. Logarithmic radius and the inactive coordinates give a product chart;
the compact tube lemma restricts it inside the prescribed open neighborhood.
-/

open Set Metric

namespace HolomorphicAnosov.Cubical

/-- Every open neighborhood of the coordinate boundary of a nontrivial
(q+1)-cell contains a product collar homeomorphic to a unit q-sphere times an
open complementary ball, carrying the boundary to the central section.

Source: Hatcher Lemma 2.34, pp. 137–139; Appendix A.2–A.4, pp. 521–522;
Bredon I.16.2–I.16.4, pp. 56–57.

Natural-language proof: Affine coordinate normalization sends the active
coordinates of the cell to the unit cube and its inactive coordinates to zero.
The norm-preserving radial Euclidean/sup homeomorphism identifies its coordinate
boundary exactly with the Euclidean unit sphere times zero. There are q+1 active
coordinates, so one radial coordinate plus the inactive coordinates has dimension
N-q; choose a linear coordinate equivalence to that Euclidean space.

Positive radial scaling sends (u,t) to exp(t)u and is a homeomorphism from sphere
times the real line to the punctured active space. Together with the inactive
coordinates and the inverse normalization, it gives an open embedding of the
sphere times Euclidean (N-q)-space into the original ambient space. Its zero
section is exactly the original coordinate boundary, as follows from exp(0)=1
and injectivity of the normalization.

Pull O back to this product. Compactness of the sphere and the tube lemma give
one neighborhood of zero whose product with the entire sphere lies in that
preimage. Choose a positive-radius Euclidean ball in it. The open embedding maps
its product with the sphere to an open set V inside O. Rescaling the normal ball
to radius one gives the required homeomorphism and preserves the exact zero
section. No differentiation of the radial map or smoothness of the cubical
boundary is used. -/
theorem cubical_cell_boundary_product_collar {N q : ℕ}
    (_hq : 1 ≤ q) (hqN : q < N) (c : ClosedCoordinateCell N)
    (hd : c.dimension = q + 1) :
    let boundary := {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ i : Fin N,
      c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)}
    ∀ O : Set (Fin N → ℝ), IsOpen O → boundary ⊆ O →
      ∃ V : Set (Fin N → ℝ), IsOpen V ∧ V ⊆ O ∧ boundary ⊆ V ∧
        ∃ e : V ≃ₜ
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1 ×
            Metric.ball (0 : EuclideanSpace ℝ (Fin (N - q))) 1),
          e '' {x : V | x.val ∈ boundary} =
            Set.univ ×ˢ {⟨0, Metric.mem_ball_self zero_lt_one⟩} := by
  classical
  dsimp
  intro O hO hBO
  obtain ⟨e, hecell, hefaces⟩ := coordinate_cell_normalization c
  have heboundary (x : Fin N → ℝ) :
      (x ∈ c.carrier ∧ ∃ i : Fin N, c.lower i < c.upper i ∧
        (x i = c.lower i ∨ x i = c.upper i)) ↔
      ((∀ i, -1 ≤ (e x).1 i ∧ (e x).1 i ≤ 1) ∧ (e x).2 = 0) ∧
        ∃ i, (e x).1 i = -1 ∨ (e x).1 i = 1 := by
    rw [hecell x, hefaces x]
  have hcard : Fintype.card {i : Fin N // c.lower i < c.upper i} = q + 1 := by
    calc
      Fintype.card {i : Fin N // c.lower i < c.upper i} =
          Nat.card {i : Fin N // c.lower i < c.upper i} := Nat.card_eq_fintype_card.symm
      _ = c.dimension := Nat.card_coe_set_eq {i : Fin N | c.lower i < c.upper i}
      _ = q + 1 := hd
  let aeq := Fintype.equivFinOfCardEq hcard
  let relabel := Homeomorph.piCongrLeft (Y := fun _ : Fin (q + 1) ↦ ℝ) aeq
  obtain ⟨r, hr⟩ := euclidean_sup_radial_homeomorph (q + 1)
  let normalized := e.trans ((relabel.trans r.symm).prodCongr
    (Homeomorph.refl ({i : Fin N // ¬ c.lower i < c.upper i} → ℝ)))
  have hsupBoundary (f : Fin (q + 1) → ℝ) :
      ‖f‖ = 1 ↔ (∀ i, -1 ≤ f i ∧ f i ≤ 1) ∧ ∃ i, f i = -1 ∨ f i = 1 := by
    constructor
    · intro hf
      refine ⟨?_, ?_⟩
      · intro i
        have hi : ‖f i‖ ≤ 1 := (norm_le_pi_norm f i).trans_eq hf
        simpa only [Real.norm_eq_abs, abs_le] using hi
      · obtain ⟨i, hi⟩ := (IsGreatest.pi_norm f).1
        have hi' : |f i| = 1 := by simpa only [Real.norm_eq_abs, hf] using hi
        refine ⟨i, ?_⟩
        rcases le_total 0 (f i) with h | h
        · exact Or.inr (by simpa only [abs_of_nonneg h] using hi')
        · exact Or.inl (by rw [abs_of_nonpos h] at hi'; linarith)
    · rintro ⟨hb, i, hi⟩
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro j
        simpa only [Real.norm_eq_abs, abs_le] using hb j
      · have hh := norm_le_pi_norm f i
        rcases hi with hi | hi <;> simpa only [hi, norm_neg, norm_one] using hh
  have hboundaryEuclidean (x : Fin N → ℝ) :
      (x ∈ c.carrier ∧ ∃ i : Fin N, c.lower i < c.upper i ∧
        (x i = c.lower i ∨ x i = c.upper i)) ↔
      ‖(normalized x).1‖ = 1 ∧ (normalized x).2 = 0 := by
    have hnorm : ‖relabel (e x).1‖ = ‖r.symm (relabel (e x).1)‖ := by
      simpa only [r.apply_symm_apply] using hr (r.symm (relabel (e x).1))
    change _ ↔ ‖r.symm (relabel (e x).1)‖ = 1 ∧ (e x).2 = 0
    rw [heboundary x, ← hnorm, hsupBoundary]
    have hcoords (j : Fin (q + 1)) : relabel (e x).1 j = (e x).1 (aeq.symm j) := by
      simp [relabel, Homeomorph.piCongrLeft_apply]
    simp only [hcoords]
    constructor
    · rintro ⟨⟨hb, hz⟩, i, hi⟩
      refine ⟨⟨fun j ↦ hb (aeq.symm j), aeq i, ?_⟩, hz⟩
      simpa only [aeq.symm_apply_apply] using hi
    · rintro ⟨⟨hb, j, hj⟩, hz⟩
      refine ⟨⟨fun i ↦ ?_, hz⟩, aeq.symm j, hj⟩
      simpa only [aeq.symm_apply_apply] using hb (aeq i)
  let E := EuclideanSpace ℝ (Fin (q + 1))
  let F := {i : Fin N // ¬ c.lower i < c.upper i} → ℝ
  let G := EuclideanSpace ℝ (Fin (N - q))
  have hdim : Module.finrank ℝ (ℝ × F) = Module.finrank ℝ G := by
    dsimp [F, G]
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
      finrank_euclideanSpace_fin, Fintype.card_subtype_compl]
    rw [Fintype.card_fin, hcard]
    omega
  let L : (ℝ × F) ≃L[ℝ] G :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  let radial : (sphere (0 : E) 1 × ℝ) ≃ₜ ({0}ᶜ : Set E) :=
    ((Homeomorph.refl _).prodCongr Real.expOrderIso.toHomeomorph).trans
      (homeomorphUnitSphereProd E).symm
  let chart : (sphere (0 : E) 1 × G) ≃ₜ (({0}ᶜ : Set E) × F) :=
    ((Homeomorph.refl _).prodCongr L.symm.toHomeomorph).trans
      ((Homeomorph.prodAssoc _ _ _).symm.trans
        (radial.prodCongr (Homeomorph.refl F)))
  let embed : (sphere (0 : E) 1 × G) → (Fin N → ℝ) :=
    normalized.symm ∘ Prod.map Subtype.val id ∘ chart
  have hembed : Topology.IsOpenEmbedding embed :=
    normalized.symm.isOpenEmbedding.comp
      ((isOpen_compl_singleton.isOpenEmbedding_subtypeVal.prodMap
        Topology.IsOpenEmbedding.id).comp chart.isOpenEmbedding)
  have hzero (s : sphere (0 : E) 1) : normalized (embed (s, 0)) = (s.val, 0) := by
    simp only [embed, Function.comp_apply, normalized.apply_symm_apply]
    change (Real.exp (L.symm 0).1 • s.val, (L.symm 0).2) = (s.val, 0)
    simp
  have hboundaryEmbed (x : Fin N → ℝ) :
      (x ∈ c.carrier ∧ ∃ i : Fin N, c.lower i < c.upper i ∧
        (x i = c.lower i ∨ x i = c.upper i)) ↔
      ∃ s : sphere (0 : E) 1, embed (s, 0) = x := by
    rw [hboundaryEuclidean x]
    constructor
    · rintro ⟨hn, hz⟩
      refine ⟨⟨(normalized x).1, mem_sphere_zero_iff_norm.mpr hn⟩, ?_⟩
      apply normalized.injective
      rw [hzero]
      exact Prod.ext rfl hz.symm
    · rintro ⟨s, rfl⟩
      rw [hzero]
      exact ⟨mem_sphere_zero_iff_norm.mp s.property, rfl⟩
  let : CompactSpace (sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  obtain ⟨V, hV, hVO, hcenter, collar, hcollar⟩ :=
    compact_open_product_collar embed hembed O hO (fun s ↦
      hBO ((hboundaryEmbed _).mpr ⟨s, rfl⟩))
  refine ⟨V, hV, hVO, ?_, collar, ?_⟩
  · intro x hx
    obtain ⟨s, rfl⟩ := (hboundaryEmbed x).mp hx
    exact hcenter s
  · simpa only [hboundaryEmbed] using hcollar



end HolomorphicAnosov.Cubical
