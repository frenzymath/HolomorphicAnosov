import HolomorphicAnosov.Topology.HatcherPlanarEmbeddingOpenImage
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Separation.Hausdorff

open Set Metric

namespace HolomorphicAnosov

-- Coordinate conjugation between the two standard models of the real plane.
lemma complex_planar_open_range (U : Set ℂ) (hU : IsOpen U)
    (f : U → ℂ) (hf : Continuous f) (hinj : Function.Injective f) :
    IsOpen (range f) := by
  let e := Complex.orthonormalBasisOneI.repr.toHomeomorph
  let V : Set (EuclideanSpace ℝ (Fin 2)) := e.symm ⁻¹' U
  let g : V → EuclideanSpace ℝ (Fin 2) := fun x ↦ e (f ⟨e.symm x, x.property⟩)
  have hg : Continuous g := by fun_prop
  have hginj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact e.symm.injective (congrArg Subtype.val (hinj (e.injective h)))
  have hO := hatcher_planar_embedding_open_image V (hU.preimage e.symm.continuous) g hg hginj
  have heq : e ⁻¹' range g = range f := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨⟨e.symm x, x.property⟩, e.injective hx⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨e x, ?_⟩, ?_⟩
      · simp [V]
      · simp [g]
  rw [← heq]
  exact hO.preimage e.continuous

/-- A planar closed-disk chart makes its open-disk locus ambiently open and gives an
embedded-circle parametrization of its boundary locus.

Source: Hatcher, *Algebraic Topology*, Theorem 2B.3, p.172, applied to the inverse chart
on the open disk; Cairns (1951), §4(D), pp.865–866, the last step of relative cell gluing.
The inverse chart is a continuous injection. Its restriction to the open disk has open
image by planar invariance of domain. Its restriction to the unit circle is an embedding
because the circle is compact and the plane is Hausdorff. The stated image equalities
identify these two images with the prescribed loci R and C. -/
theorem disk_chart_open_interior_boundary (K R C : Set ℂ)
    (hRK : R ⊆ K) (hCK : C ⊆ K) (H : K ≃ₜ closedBall (0 : ℂ) 1)
    (hR : H '' {z : K | (z : ℂ) ∈ R} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1})
    (hC : H '' {z : K | (z : ℂ) ∈ C} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1}) :
    IsOpen R ∧ ∃ γ : sphere (0 : ℂ) 1 → ℂ,
      Topology.IsEmbedding γ ∧ range γ = C := by
  let f : ball (0 : ℂ) 1 → ℂ := fun z ↦
    H.symm ⟨z, ball_subset_closedBall z.property⟩
  have hf : Continuous f := by fun_prop
  have hi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun w : closedBall (0 : ℂ) 1 ↦ (w : ℂ))
      (H.symm.injective (Subtype.ext h)))
  have hrange : range f = R := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hw : (⟨w, ball_subset_closedBall w.property⟩ : closedBall (0 : ℂ) 1) ∈
          H '' {z : K | (z : ℂ) ∈ R} := by rw [hR]; exact w.property
      obtain ⟨x, hx, heq⟩ := hw
      change (H.symm _ : ℂ) ∈ R
      rw [← heq, H.symm_apply_apply]
      exact hx
    · intro hz
      have hw : (H ⟨z, hRK hz⟩ : ℂ) ∈ ball (0 : ℂ) 1 := by
        have : H ⟨z, hRK hz⟩ ∈ H '' {z : K | (z : ℂ) ∈ R} := ⟨_, hz, rfl⟩
        rw [hR] at this
        exact this
      refine ⟨⟨H ⟨z, hRK hz⟩, hw⟩, ?_⟩
      simp [f]
  refine ⟨hrange ▸ complex_planar_open_range _ isOpen_ball f hf hi, ?_⟩
  let γ : sphere (0 : ℂ) 1 → ℂ := fun z ↦
    H.symm ⟨z, sphere_subset_closedBall z.property⟩
  have hγ : Continuous γ := by fun_prop
  have hγi : Function.Injective γ := by
    intro x y h
    exact Subtype.ext (congrArg (fun w : closedBall (0 : ℂ) 1 ↦ (w : ℂ))
      (H.symm.injective (Subtype.ext h)))
  refine ⟨γ, (hγ.isClosedEmbedding hγi).isEmbedding, ?_⟩
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have hw : (⟨w, sphere_subset_closedBall w.property⟩ : closedBall (0 : ℂ) 1) ∈
        H '' {z : K | (z : ℂ) ∈ C} := by rw [hC]; exact w.property
    obtain ⟨x, hx, heq⟩ := hw
    change (H.symm _ : ℂ) ∈ C
    rw [← heq, H.symm_apply_apply]
    exact hx
  · intro hz
    have hw : (H ⟨z, hCK hz⟩ : ℂ) ∈ sphere (0 : ℂ) 1 := by
      have : H ⟨z, hCK hz⟩ ∈ H '' {z : K | (z : ℂ) ∈ C} := ⟨_, hz, rfl⟩
      rw [hC] at this
      exact this
    refine ⟨⟨H ⟨z, hCK hz⟩, hw⟩, ?_⟩
    simp [γ]

end HolomorphicAnosov
