import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.LinearAlgebra.Dimension.RankNullity
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Basic

/-! The rank of a holomorphic tangent subbundle with one-dimensional quotient fibres (Demailly, V
§1, pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- For a rank-`r` holomorphic tangent subbundle with one-dimensional quotient fibres, `r + 1 = d`
at every base point. -/
theorem quotient_line_rank
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (x : X) : r + 1 = d := by
  obtain ⟨V, s, hxV, hs, hspan⟩ := hP x
  have hr : Module.finrank ℂ (P x) = r := by
    rw [← hspan x hxV, finrank_span_eq_card (hs.2.2 x hxV)]
    simp
  have h := (P x).finrank_quotient_add_finrank
  rw [hline x, hr] at h
  have hd : Module.finrank ℂ (TangentSpace (complexModel d) x) = d :=
    (Module.finrank_pi ℂ).trans (Fintype.card_fin d)
  rw [hd] at h
  omega


end HolomorphicAnosov
