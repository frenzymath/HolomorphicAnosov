import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Bundle Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff Classical

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus

/-- Evaluation of a quotient-frame coordinate is holomorphic on the tangent total space over the
frame domain. (Demailly, V §11, (11.1), p.267 and §14, (14.1), p.273) -/
theorem frame_total_coefficient_holomorphic
    {d r : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (p : TangentBundle (complexModel d) X) (hp : p.proj ∈ V) :
    ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ℂ) ∞
      (fun q : TangentBundle (complexModel d) X ↦
        if hq : q.proj ∈ V then
          e.coordinate q.proj hq (QuotientLineConnection.projection P q.proj q.snd)
        else 0) p := by
  obtain ⟨D, hpD⟩ := exists_quotient_local_data P hP hline p.proj
  obtain ⟨O, t, hO, hpO, hOV, ht, hte⟩ := e.holomorphic p.proj hp
  have ht' := (D.hscalar ⟨p.proj, t p.proj⟩ hpD).comp p.proj
    (ht.contMDiffAt (hO.mem_nhds hpO))
  have htne : D.θ p.proj (t p.proj) ≠ 0 := by
    rw [← D.apply_mk p.proj hpD, hte p.proj hpO]
    intro h
    have he0 : e.sectionValue p.proj = 0 :=
      (D.L p.proj hpD).injective (by simpa using h)
    have hn := e.normalized p.proj hp
    rw [he0, map_zero] at hn
    exact zero_ne_one hn
  have hden := ht'.comp p (contMDiffAt_proj (TangentSpace (complexModel d)))
  have hratio := (D.hscalar p hpD).div₀ hden htne
  apply hratio.congr_of_eventuallyEq
  have hproj : ContinuousAt
      (fun q : TangentBundle (complexModel d) X ↦ q.proj) p :=
    (FiberBundle.continuous_proj (ComplexModel d)
      (TangentSpace (complexModel d))).continuousAt
  filter_upwards [hproj.preimage_mem_nhds (hO.mem_nhds hpO),
    hproj.preimage_mem_nhds (D.V.isOpen.mem_nhds hpD)] with q hqO hqD
  have hqV : q.proj ∈ V := hOV hqO
  simp only [dite_eq_left hqV]
  have hclass : QuotientLineConnection.projection P q.proj q.snd =
      e.coordinate q.proj hqV (QuotientLineConnection.projection P q.proj q.snd) •
        e.sectionValue q.proj := by
    apply (e.coordinate q.proj hqV).injective
    simp only [map_smul, e.normalized, smul_eq_mul, mul_one]
  have hnonzero : D.θ q.proj (t q.proj) ≠ 0 := by
    rw [← D.apply_mk q.proj hqD, hte q.proj hqO]
    intro h
    have he0 : e.sectionValue q.proj = 0 :=
      (D.L q.proj hqD).injective (by simpa using h)
    have hn := e.normalized q.proj hqV
    rw [he0, map_zero] at hn
    exact zero_ne_one hn
  change _ = D.θ q.proj q.snd / D.θ q.proj (t q.proj)
  apply (eq_div_iff hnonzero).mpr
  rw [← D.apply_mk q.proj hqD, ← D.apply_mk q.proj hqD, hte q.proj hqO, hclass]
  simp [e.normalized]

end HolomorphicAnosov.ConnectionCalculus
