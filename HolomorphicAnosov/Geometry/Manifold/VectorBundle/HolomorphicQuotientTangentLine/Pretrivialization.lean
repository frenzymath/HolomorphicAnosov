import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.LocalData

/-! Local pretrivializations of the tangent quotient using transverse lifts (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The local quotient pretrivialization with forward fibre coordinate `L` and inverse given by the
class of a scalar multiple of the transverse lift. -/
def QuotientLocalData.pretrivialization
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLocalData P) : Pretrivialization ℂ (π ℂ (HolomorphicQuotientTangentLine P)) where
  toFun q := (q.proj, if h : q.proj ∈ D.V then D.L q.proj h q.snd else 0)
  invFun p := ⟨p.1, (P p.1).mkQ (p.2 • D.T p.1)⟩
  source := (π ℂ (HolomorphicQuotientTangentLine P)) ⁻¹' D.V
  target := (D.V : Set X) ×ˢ univ
  map_source' := fun q hq ↦ ⟨hq, mem_univ _⟩
  map_target' := fun p hp ↦ hp.1
  left_inv' := by
    intro q hq
    rcases q with ⟨x, v⟩
    change (⟨x, (P x).mkQ ((if h : x ∈ D.V then D.L x h v else 0) • D.T x)⟩ :
      TotalSpace ℂ (HolomorphicQuotientTangentLine P)) = ⟨x, v⟩
    apply congrArg (TotalSpace.mk x)
    have hx : x ∈ D.V := hq
    rw [dite_eq_left hx, ← D.symm_apply x hx, ContinuousLinearEquiv.symm_apply_apply]
  right_inv' := by
    intro p hp
    apply Prod.ext
    · rfl
    · change (if h : p.1 ∈ D.V then D.L p.1 h ((P p.1).mkQ (p.2 • D.T p.1)) else 0) = p.2
      have hx : p.1 ∈ D.V := hp.1
      rw [dite_eq_left hx, ← D.symm_apply p.1 hx, ContinuousLinearEquiv.apply_symm_apply]
  open_target := D.V.isOpen.prod isOpen_univ
  baseSet := D.V
  open_baseSet := D.V.isOpen
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun _ _ ↦ rfl


end HolomorphicAnosov
