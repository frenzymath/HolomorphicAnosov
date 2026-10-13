import HolomorphicAnosov.Paper.Ghys.ProjectiveCoverChartData
import HolomorphicAnosov.Paper.Ghys.ProjectiveNativeIdentification
import HolomorphicAnosov.Paper.Ghys.ProjectiveTransverseDevelopment
import HolomorphicAnosov.Paper.Ghys.ProjectiveCoverDevelopment
import HolomorphicAnosov.Geometry.ComplexMobiusPSLNormalization
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularity
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.TransverseMobiusGermDevelopment
import HolomorphicAnosov.Paper.Ghys.ProjectiveLocalGermsEffectiveCocycle
import HolomorphicAnosov.Paper.Ghys.Proposition31
import HolomorphicAnosov.Paper.Ghys.Proposition41
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveFiniteNeInfinity
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveInfinityOfNotFiniteSource
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveFiniteRange
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveAffineRange
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Basic

/-! The stable foliation has a projective developing map on the universal cover of each connected
component, with PSL holonomy and punctured projective-line images of unstable leaves. (Ghys, §5
p.597, Props.3.1,4.1; Thurston, §§3.5,4.8) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
universe u v
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- Native PSL transformations are determined by their action on the complex projective line. (Ghys,
p.597; Thurston, §§3.5,4.8) -/

theorem projectiveDeveloping_psl_action_ext
    (g h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
    (hact : ∀ p : ComplexProjectiveLine, g • p = h • p) : g = h := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective
  apply Equiv.ext
  intro p
  change g • p = h • p
  exact hact p

theorem projectiveDeveloping
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hu : ∀ x : M, Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2)
    (x₀ : M) :
    ∃ s : ℕ,
    ∃ A : NativeTransverseAsymptoticIdentification.{u, u}
        f.toHomeomorph a.splitting.stable.toDistribution
        a.splitting.unstable.toDistribution s 2,
    letI := A.realAmbientCharts
    ∃ C : IntrinsicComplexUnstableLeaves A.F,
    (∀ x : M,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      letI := A.F.unstableCharts (Quotient.mk A.F.unstablePartition x)
      letI := (A.nativeU x).topology
      letI := (A.nativeU x).charts
      letI := (A.complexU1 x).charts
      ContMDiff (complexModel 1) (complexModel 1) ∞ (A.unstableIdentification x) ∧
        ContMDiff (complexModel 1) (complexModel 1) ∞ (A.unstableIdentification x).symm) ∧
    (∀ x : M,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      ContMDiff (complexModel 1) (complexModel d) ∞
        (Subtype.val : A.F.ULeaf x → M)) ∧
    ∃ affine : AffineUnstableLeafStructures A.F C,
    (∀ q : Quotient A.F.unstablePartition,
      letI := A.F.unstableTopology q
      letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q)) ∧
    ∃ atlas : TransverseProjectiveAtlas A.F C,
    (∀ c ∈ atlas.charts, ∀ x : M, ∀ z : A.F.ULeaf x,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      z.val ∈ c.domain A.F C →
      ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint A.F C x),
        z ∈ b.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
          ∀ᶠ w in 𝓝 z,
            w ∈ b.source ∧ w.val ∈ c.domain A.F C ∧
              c.transverseCoordinate A.F C w.val = g • complexProjectiveLineFinite (b w)) ∧
    ∀ (E : Type v) [TopologicalSpace E] [SimplyConnectedSpace E]
      (p : E → M) (_hp : IsCoveringMap p) (y₀ : E),
      p y₀ = x₀ → Set.range p = connectedComponent x₀ →
      let stableLink : E → E → Prop := fun x y ↦
        ∃ i : A.F.boxIndex, ∃ w : FoliationCoordinateDisk 2, ∃ β : Path x y,
          ∀ t : unitInterval, ∃ z : FoliationCoordinateDisk s,
            p (β t) = ((A.F.box i).chart (z, w)).val
      let unstableLink : E → E → Prop := fun x y ↦
        ∃ i : A.F.boxIndex, ∃ z : FoliationCoordinateDisk s, ∃ β : Path x y,
          ∀ t : unitInterval, ∃ w : FoliationCoordinateDisk 2,
            p (β t) = ((A.F.box i).chart (z, w)).val
      ∃ charts : ChartedSpace (ComplexModel d) E,
      letI := charts
      ∃ smooth : IsManifold (complexModel d) ∞ E,
      letI := smooth
      IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p ∧
      ∃ D : C(E, ComplexProjectiveLine),
        (∀ y : E,
          let q := Quotient.mk A.F.stablePartition (p y)
          letI := A.F.stableTopology q
          ∃ (Vs : TopologicalSpace.Opens (IntrinsicFoliationLeaf A.F.stablePartition q))
            (W : TopologicalSpace.Opens ComplexProjectiveLine)
            (O : TopologicalSpace.Opens E),
            (⟨p y, rfl⟩ : IntrinsicFoliationLeaf A.F.stablePartition q) ∈ Vs ∧
            D y ∈ W ∧ y ∈ O ∧
            ∃ e : (Vs × W) ≃ₜ O,
              (∀ v w, D (e (v, w)) = w.val) ∧
              (∀ v w, w.val = D y → p (e (v, w)) = v.val.val) ∧
              (∀ v w, v.val.val = p y → w.val = D y → (e (v, w)).val = y)) ∧
        (∀ y : E, ∃ c ∈ atlas.charts,
          ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ, ∃ V : Set E,
            IsOpen V ∧ y ∈ V ∧ Set.MapsTo p V (c.domain A.F C) ∧
              ∀ z ∈ V, D z = g • c.transverseCoordinate A.F C (p z)) ∧
        ∃ action : FundamentalGroup M (p y₀) ≃* deck p,
          (∀ α : Path (p y₀) (p y₀),
            ∃ β : Path y₀ ((action (FundamentalGroup.fromPath
                (Path.Homotopic.Quotient.mk α)))⁻¹ • y₀),
              ∀ t, p (β t) = α t) ∧
          ∃ H : FundamentalGroup M (p y₀) →*
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
            (∀ γ y, D (action γ • y) = H γ • D y) ∧
            (∀ y : E,
              let q := Quotient.mk A.F.stablePartition (p y)
              letI := A.F.stableTopology q
              ∃ lift : IntrinsicFoliationLeaf A.F.stablePartition q → E,
                Continuous lift ∧ Function.Injective lift ∧
                lift ⟨p y, rfl⟩ = y ∧ (∀ z, p (lift z) = z.val) ∧
                Set.range lift = {z : E | Relation.EqvGen stableLink y z} ∧
                Set.range lift = connectedComponentIn (D ⁻¹' {D y}) y) ∧
            (∀ y : E,
              letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition (p y))
              letI := C.charts (Quotient.mk A.F.unstablePartition (p y))
              ∃ lift : A.F.ULeaf (p y) → E,
                ContMDiff (complexModel 1) (complexModel d) ∞ lift ∧
                Function.Injective lift ∧ lift (A.F.uPoint (p y)) = y ∧
                (∀ z, p (lift z) = z.val) ∧
                Set.range lift = {z : E | Relation.EqvGen unstableLink y z} ∧
                ∃ (pole : ComplexProjectiveLine)
                  (e : OpenPartialHomeomorph (A.F.ULeaf (p y)) ComplexProjectiveLine),
                  e.source = Set.univ ∧ e.target = {pole}ᶜ ∧
                  (∀ z, e z = D (lift z)) ∧
                  ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
                  ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target) := by
  obtain ⟨s, A, _hA⟩ := projective_native_identification f a x₀ hu
  refine ⟨s, A, ?_⟩
  let := A.realAmbientCharts
  obtain ⟨C, hCident, hCinc, affine, hAffine, atlas, hAtlas⟩ :=
    projective_transverse_development f a hu s A
  refine ⟨C, hCident, hCinc, affine, hAffine, atlas, hAtlas, ?_⟩
  obtain ⟨pslIdentification, hpslIdentification⟩ := effective_complex_mobius_psl_equiv
  have hpslActionUnique (g : (MulAction.toPermHom (GL (Fin 2) ℂ)
      ComplexProjectiveLine).range)
      (q : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
      (hq : ∀ z : ComplexProjectiveLine, q • z = g.val z) :
      q = pslIdentification g := by
    apply projectiveDeveloping_psl_action_ext
    intro z
    exact (hq z).trans (hpslIdentification g z).symm

  have _coverChartProvider (E : Type v) [TopologicalSpace E] [T2Space E]
      [SecondCountableTopology E] (p : E → M) (hp : IsCoveringMap p)
      (hsurj : Function.Surjective p) :=
    projective_cover_chart_data (d := d) (M := M) (E := E) p hp hsurj
  
  
  
  exact projective_cover_development f a s A C atlas affine hAffine hAtlas hCinc x₀

end HolomorphicAnosov.Ghys
