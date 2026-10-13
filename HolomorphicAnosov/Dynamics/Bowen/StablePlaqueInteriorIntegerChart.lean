import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.homeomorph_pow_apply
import HolomorphicAnosov.Dynamics.Bowen.PlaqueLocalAgreement
import HolomorphicAnosov.Dynamics.Bowen.StablePlaqueIntegerChart

/-!
# Integer transport at an interior point of a fixed stable plaque

An agent-written combination of the public local carrier agreement and
integer plaque chart. The point must have strict initial distance less than
the plaque radius; the original full-plaque subspace topology is retained.
-/

namespace HolomorphicAnosov.Dynamics.Bowen
open Set

/-- An integer iterate is an open embedding from a neighborhood of any
strict interior point of a fixed stable plaque into the full stable plaque
at its image. Pair contraction makes the fixed plaque and the self-centered
plaque agree in a sufficiently small ball. Restrict the published integer
chart to that ball, identify its source with a relatively open subset of the
fixed plaque, and include its relatively open image in the image plaque.
No uniform neighborhood in the point or integer is asserted. -/
theorem stablePlaqueInteriorIntegerChart
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) (γ lam : ℝ)
    (hγ : 0 < γ) (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hc : ∀ a y z : X, y ∈ relativeClosedStablePlaque F γ a →
      z ∈ relativeClosedStablePlaque F γ a → ∀ n : ℕ,
      dist ((F : X → X)^[n] y) ((F : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (x : X) (z : relativeClosedStablePlaque F γ x) (hz : dist (z : X) x < γ)
    (n : ℤ) :
    ∃ O : Set (relativeClosedStablePlaque F γ x), IsOpen O ∧ z ∈ O ∧
      ∃ g : O → relativeClosedStablePlaque F γ ((F ^ n) z.val),
        _root_.Topology.IsOpenEmbedding g ∧ ∀ t, (g t : X) = (F ^ n) (t : X) := by
  let η := (γ - dist (z : X) x) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hself (a : X) : a ∈ relativeClosedStablePlaque F γ a :=
    fun _ ↦ by simpa using hγ.le
  have hp (r : ℝ) (a : X) :
      HolomorphicAnosov.Bowen.RectangleSlicesPreparation.stablePlaque F r a =
        relativeClosedStablePlaque F r a := by
    ext t
    simp only [HolomorphicAnosov.Bowen.RectangleSlicesPreparation.stablePlaque,
      relativeClosedStablePlaque, Set.mem_ofPred_eq,
      HolomorphicAnosov.Bowen.RectangleSlicesPreparation.homeomorph_pow_apply]
  have hlocal : ∀ t : X, dist t z.val < η →
      (t ∈ relativeClosedStablePlaque F γ z.val ↔ t ∈ relativeClosedStablePlaque F γ x) := by
    have hpc : ∀ a y v k,
        y ∈ HolomorphicAnosov.Bowen.RectangleSlicesPreparation.stablePlaque F γ a →
        v ∈ HolomorphicAnosov.Bowen.RectangleSlicesPreparation.stablePlaque F γ a →
        dist ((F ^ k) y) ((F ^ k) v) ≤ lam ^ k * dist y v := by
      intro a y v k hy hv
      rw [hp] at hy hv
      simpa only [HolomorphicAnosov.Bowen.RectangleSlicesPreparation.homeomorph_pow_apply] using
        hc a y v hy hv k
    have hqd : z.val ∈ HolomorphicAnosov.Bowen.RectangleSlicesPreparation.stablePlaque
        F (dist z.val x) x := by
      intro k
      have hh := hc x z.val x z.property (hself x) k
      simpa only [HolomorphicAnosov.Bowen.RectangleSlicesPreparation.homeomorph_pow_apply] using
        hh.trans (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (pow_le_one₀ hlam.1 hlam.2) dist_nonneg)
    have hh := plaqueLocalAgreement F hlam hpc hγ.le hz.le
      (show η + dist z.val x ≤ γ by dsimp [η]; linarith) hqd
    intro t ht
    simpa only [hp] using hh t ht
  obtain ⟨A, B, hA, hB, hzA, hzB, hAopen, hBopen, e, he⟩ :=
    stablePlaqueIntegerChart F γ hγ z.val n
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hAopen
  let O : Set (relativeClosedStablePlaque F γ x) :=
    Subtype.val ⁻¹' (W ∩ Metric.ball z.val η)
  have hO : IsOpen O := (hW.inter Metric.isOpen_ball).preimage continuous_subtype_val
  have hzW : z.val ∈ W := by
    change (⟨z.val, hself z.val⟩ : relativeClosedStablePlaque F γ z.val) ∈ Subtype.val ⁻¹' W
    rw [hWeq]
    exact hzA
  have hzO : z ∈ O := ⟨hzW, by simpa using hη⟩
  have hjA (t : O) : (t : X) ∈ A := by
    have ht : (t : X) ∈ relativeClosedStablePlaque F γ z.val :=
      (hlocal t (Metric.mem_ball.mp t.property.2)).mpr t.val.property
    have hw : (⟨(t : X), ht⟩ : relativeClosedStablePlaque F γ z.val) ∈ Subtype.val ⁻¹' W :=
      t.property.1
    rw [hWeq] at hw
    exact hw
  let j : O → A := fun t ↦ ⟨t, hjA t⟩
  have hj : _root_.Topology.IsOpenEmbedding j := by
    have hi : _root_.Topology.IsEmbedding ((Subtype.val : A → X) ∘ j) := by
      change _root_.Topology.IsEmbedding ((Subtype.val : relativeClosedStablePlaque F γ x → X) ∘
        (Subtype.val : O → relativeClosedStablePlaque F γ x))
      exact _root_.Topology.IsEmbedding.subtypeVal.comp _root_.Topology.IsEmbedding.subtypeVal
    refine ⟨(_root_.Topology.IsEmbedding.of_comp_iff
      _root_.Topology.IsEmbedding.subtypeVal).mp hi, ?_⟩
    have heq : Set.range j = (Subtype.val : A → X) ⁻¹' Metric.ball z.val η := by
      ext a
      constructor
      · rintro ⟨t, rfl⟩
        exact t.property.2
      · intro ha
        have hax : (a : X) ∈ relativeClosedStablePlaque F γ x :=
          (hlocal a (Metric.mem_ball.mp ha)).mp (hA a.property)
        have haW : (a : X) ∈ W := by
          change (⟨a.val, hA a.property⟩ : relativeClosedStablePlaque F γ z.val) ∈
            Subtype.val ⁻¹' W
          rw [hWeq]
          exact a.property
        exact ⟨⟨⟨a.val, hax⟩, haW, ha⟩, rfl⟩
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  let b : (Subtype.val ⁻¹' B : Set (relativeClosedStablePlaque F γ ((F ^ n) z.val))) ≃ₜ B :=
    _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hB)
  let g : O → relativeClosedStablePlaque F γ ((F ^ n) z.val) :=
    fun t ↦ (b.symm (e (j t))).val
  have hg : _root_.Topology.IsOpenEmbedding g :=
    hBopen.isOpenEmbedding_subtypeVal.comp
      (b.symm.isOpenEmbedding.comp (e.isOpenEmbedding.comp hj))
  refine ⟨O, hO, hzO, g, hg, ?_⟩
  intro t
  have hb : (b (b.symm (e (j t))) : X) = (e (j t) : X) :=
    congrArg Subtype.val (b.apply_symm_apply (e (j t)))
  exact hb.trans (he (j t))

end HolomorphicAnosov.Dynamics.Bowen

