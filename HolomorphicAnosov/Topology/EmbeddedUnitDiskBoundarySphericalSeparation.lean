import HolomorphicAnosov.Analysis.Complex.EmbeddedUnitDiskBoundaryWinding
import HolomorphicAnosov.Topology.OnePointCompactComplement
import HolomorphicAnosov.Topology.CompactComplementComponentPath
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingOmittedPath
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingConstant

namespace HolomorphicAnosov


/-- An embedded unit-disk boundary separates the one-point compactification.
The boundary loop has nonzero winding about the center image and zero winding
about any point outside the full disk image. If its spherical complement were
preconnected, the compact plane-complement comparison would give an omitted-value
path between those two points. Winding constancy along that path contradicts
these different values. This is an agent-written winding proof of the planar
case of Hatcher Proposition 2B.1(b), pp.169–170. -/
theorem embedded_unit_disk_boundary_sphere_not_preconnected
    (f : Metric.closedBall (0 : ℂ) 1 → ℂ) (hf : Continuous f)
    (hi : Function.Injective f) :
    ¬ IsPreconnected (OnePoint.some '' (f '' {z | ‖z.val‖ = 1}))ᶜ := by
  let γ : ComplexLoop := ⟨fun z ↦ f ⟨z, by simp⟩, hf.comp (by fun_prop)⟩
  let c := f ⟨0, by simp⟩
  obtain ⟨hc, hwind⟩ := embedded_unit_disk_boundary_winding_ne_zero f hf hi
  change ∀ z, γ z ≠ c at hc
  change loopWinding γ c hc ≠ 0 at hwind
  have hrange : Set.range γ = f '' {z | ‖z.val‖ = 1} := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨z, by simp⟩, Circle.norm_coe z, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z.val, by change dist z.val 0 = 1; simpa only [dist_zero_right, Set.mem_ofPred_eq] using hz⟩, rfl⟩
  rw [← hrange]
  have hcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hfull : IsCompact (Set.range f) := isCompact_range hf
  obtain ⟨M, hM⟩ := hfull.isBounded.exists_norm_le
  let b : ℂ := (max M 0 + 1 : ℝ)
  have hbfull : b ∉ Set.range f := by
    intro hb
    have h := hM b hb
    have hnorm : ‖b‖ = max M 0 + 1 := by
      change ‖((max M 0 + 1 : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm] at h
    linarith [le_max_left M 0]
  have hb (z : Circle) : γ z ≠ b := fun he ↦ hbfull ⟨_, he⟩
  have hcb : c ≠ b := fun he ↦ hbfull ⟨_, he⟩
  have hwb : loopWinding γ b hb = 0 := by
    apply (loopWinding_homotopy γ (constantLoop c) b hb (fun _ ↦ hcb) ?_).trans
      (loopWinding_constant c b hcb)
    let d (t : unitInterval) (z : Circle) : Metric.closedBall (0 : ℂ) 1 :=
      ⟨(1 - (t : ℝ)) • (z : ℂ), by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr t.property.2), Circle.norm_coe, mul_one]
        linarith [t.property.1]⟩
    refine ⟨⟨fun p ↦ f (d p.1 p.2), hf.comp (by fun_prop)⟩, ?_, ?_, ?_⟩
    · intro z
      simp [d, γ]
    · intro z
      simp [d, constantLoop, c]
    · intro t z he
      exact hbfull ⟨d t z, he⟩
  intro hconn
  have hcK : c ∉ Set.range γ := by rintro ⟨z, hz⟩; exact hc z hz
  have hbK : b ∉ Set.range γ := by rintro ⟨z, hz⟩; exact hb z hz
  have hs : (b : OnePoint ℂ) ∈ connectedComponentIn
      (OnePoint.some '' Set.range γ)ᶜ (c : OnePoint ℂ) :=
    hconn.subset_connectedComponentIn (by simpa using hcK) Set.Subset.rfl (by simpa using hbK)
  have hp := Topology.onePoint_complex_complement_component hcompact hcK hbK hs
  obtain ⟨p, hp⟩ := Topology.joinedIn_compl_of_compact_component
    (Set.range γ) hcompact c b hcK hp
  have hw := loopWinding_omittedPath γ c b hc hb ⟨p, fun t z he ↦ hp t ⟨z, he.symm⟩⟩
  exact hwind (hw.trans hwb)

end HolomorphicAnosov
