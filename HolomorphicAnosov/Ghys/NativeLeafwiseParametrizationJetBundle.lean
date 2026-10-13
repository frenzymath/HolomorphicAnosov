import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Ghys.CurveJetReparametrization
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination

/-! Parametrization jets of the original intrinsic leaves (Ghys, §3) -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped Manifold ContDiff
universe u

variable {ι : Type u} (L : ι → Type u)
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
variable [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]

/-- The original dependent sum of intrinsic one-contact quotients. (Ghys, §3) -/
abbrev NativeLeafwiseJet1 := Σ i, CurveJet1 (L i)

/-- The original dependent sum of intrinsic two-contact quotients. (Ghys, §3) -/
abbrev NativeLeafwiseJet2 := Σ i, CurveJet2 (L i)

/-- Intrinsic one-jets embed into the dependent sum. (Ghys, §3) -/
def nativeLeafwiseJet1Inclusion (i : ι) : CurveJet1 (L i) → NativeLeafwiseJet1 L :=
  fun j ↦ ⟨i, j⟩

/-- Intrinsic two-jets embed into the dependent sum with the original leaf label. (Ghys, §3) -/
def nativeLeafwiseJet2Inclusion (i : ι) : CurveJet2 (L i) → NativeLeafwiseJet2 L :=
  fun j ↦ ⟨i, j⟩

/-- Truncation preserves the original intrinsic leaf and the representative germ. (Ghys, §3) -/
def nativeLeafwiseJetTruncation (j : NativeLeafwiseJet2 L) : NativeLeafwiseJet1 L :=
  ⟨j.1, curveJetTruncation (L j.1) j.2⟩

/-- Scaling acts by germ precomposition on the dependent sum. (Ghys, §3) -/
def nativeLeafwiseJet1Scale (omega : ℂˣ) (j : NativeLeafwiseJet1 L) :
    NativeLeafwiseJet1 L := ⟨j.1, curveJet1Scale (L j.1) omega j.2⟩

/-- Rational source precomposition on the original total two-jets. (Ghys, §3) -/
def nativeLeafwiseJet2Reparametrize (p : CurveJetReparametrization)
    (j : NativeLeafwiseJet2 L) : NativeLeafwiseJet2 L :=
  ⟨j.1, curveJet2Reparametrize (L j.1) p j.2⟩

variable {d : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real
variable [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
variable {D : RealTangentDistribution (realModel d) M}
variable (U : HPS.LeafPartition D ι L (fun _ ↦ 2))

/-- The original ambient base of an intrinsic one-jet. (Ghys, §3) -/
def nativeLeafwiseJet1Base (j : NativeLeafwiseJet1 L) : M :=
  (U.leaf j.1).inclusion (curveJet1Base (L j.1) j.2)

/-- The original ambient base of an intrinsic two-jet. (Ghys, §3) -/
def nativeLeafwiseJet2Base (j : NativeLeafwiseJet2 L) : M :=
  (U.leaf j.1).inclusion (curveJet2Base (L j.1) j.2)

/-- Actual scalar flowbox coordinate on an original intrinsic leaf. (Ghys, §3) -/
def nativeLeafFlowboxScalar {s : ℕ} (c : OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (i : ι) (z : L i) : ℂ := (c ((U.leaf i).inclusion z)).1

/-- Full one-jet flowbox coordinates, retaining the transverse base label. (Ghys, §3) -/
def nativeLeafwiseJet1Coeff {s : ℕ}
    (c : OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (j : NativeLeafwiseJet1 L) : (ℂ × (Fin s → ℝ)) × ℂ :=
  (c (nativeLeafwiseJet1Base L U j),
    germFirst (j.2.out.1.map (nativeLeafFlowboxScalar L U c j.1)))

/-- Full two-jet flowbox coordinates, with the quadratic derivative divided by two. (Ghys, §3) -/
def nativeLeafwiseJet2Coeff {s : ℕ}
    (c : OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (j : NativeLeafwiseJet2 L) : ((ℂ × (Fin s → ℝ)) × ℂ) × ℂ :=
  ((c (nativeLeafwiseJet2Base L U j),
    germFirst (j.2.out.1.map (nativeLeafFlowboxScalar L U c j.1))),
    germSecond (j.2.out.1.map (nativeLeafFlowboxScalar L U c j.1)))

/-- The flowbox-generated topology on the dependent sum of one-jets. (Ghys, §3) -/
@[instance_reducible]
def nativeLeafwiseJet1Topology {n s : ℕ}
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ))) :
    TopologicalSpace (NativeLeafwiseJet1 L) :=
  TopologicalSpace.generateFrom {S | ∃ i : Fin n, ∃ O : Set ((ℂ × (Fin s → ℝ)) × ℂ),
    IsOpen O ∧ S = {j | nativeLeafwiseJet1Base L U j ∈ (c i).source ∧
      nativeLeafwiseJet1Coeff L U (c i) j ∈ O}}

/-- The flowbox-generated topology on the dependent sum of two-jets. (Ghys, §3) -/
@[instance_reducible]
def nativeLeafwiseJet2Topology {n s : ℕ}
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ))) :
    TopologicalSpace (NativeLeafwiseJet2 L) :=
  TopologicalSpace.generateFrom {S | ∃ i : Fin n,
    ∃ O : Set (((ℂ × (Fin s → ℝ)) × ℂ) × ℂ),
    IsOpen O ∧ S = {j | nativeLeafwiseJet2Base L U j ∈ (c i).source ∧
      nativeLeafwiseJet2Coeff L U (c i) j ∈ O}}

section IntrinsicAtlases
variable [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]

/-- The first-jet coefficient atlas supplied by the fixed-leaf theorem on its coefficient-generated topology. (Ghys, §3) -/
@[instance_reducible]
def nativeLeafJet1Charts (i : ι) : ChartedSpace (ℂ × ℂ) (CurveJet1 (L i)) :=
  (leaf_jet_complex_manifold (L i)).2.2.2.2.choose

/-- The paired second-jet coefficient atlas supplied by the fixed-leaf theorem. (Ghys, §3) -/
@[instance_reducible]
def nativeLeafJet2Charts (i : ι) : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 (L i)) :=
  (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose

omit [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)] in
/-- The original first-jet coefficient atlas is complex smooth. (Ghys, §3) -/
theorem nativeLeafJet1Manifold (i : ι) :
    letI := nativeLeafJet1Charts L i
    IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 (L i)) :=
  (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec.2.2.2.2.1

omit [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)] in
/-- The paired original two-jet coefficient atlas is complex smooth. (Ghys, §3) -/
theorem nativeLeafJet2Manifold (i : ι) :
    letI := nativeLeafJet2Charts L i
    IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 (L i)) :=
  (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec.2.2.2.2.2.1

omit [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)] in
/-- Truncation is holomorphic for the paired intrinsic coefficient atlases. (Ghys, §3) -/
theorem nativeLeafJetTruncationHolomorphic (i : ι) :
    letI := nativeLeafJet1Charts L i
    letI := nativeLeafJet2Charts L i
    ContMDiff 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, ℂ × ℂ) ∞ (curveJetTruncation (L i)) :=
  (leaf_jet_complex_manifold (L i)).2.2.2.2.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.1

end IntrinsicAtlases

end HolomorphicAnosov.Ghys
