import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.LocalData
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.QuotientLineRank
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.HolomorphicTransverseLift
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.NormalizedQuotientCoordinate
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.NormalizedTotalCoefficientAt

/-! Existence of local coordinates for the tangent quotient by a holomorphic subbundle with one-
dimensional quotient fibres (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1,
pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- A holomorphic tangent subbundle with one-dimensional quotient fibres admits local quotient
coordinate data around every point (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
theorem exists_quotient_local_data
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (x : X) : ∃ D : QuotientLocalData P, x ∈ D.V := by
  classical
  have hr := quotient_line_rank P hP hline x
  have hd : 1 ≤ d := by omega
  have he : r = d - 1 := by omega
  have hP' : IsHolomorphicTangentSubbundle (d - 1) P := he ▸ hP
  obtain ⟨V, T, hxV, hT, hTP⟩ := exists_holomorphic_transverse_lift hd P hP' x
  obtain ⟨θ, hker, hθT, hL⟩ := normalized_quotient_coordinate P hline V T hTP
  choose L hLmk hLsymm using hL
  exact ⟨⟨V, T, θ, hT,
    fun p hp ↦ normalized_total_coefficient_at hd P hP' T hT θ hker hθT p hp,
    L, hLmk, hLsymm⟩, hxV⟩


end HolomorphicAnosov
