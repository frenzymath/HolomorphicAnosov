import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData

namespace HolomorphicAnosov

open Set Topology _root_.Topology
open scoped ContDiff Manifold ENNReal

universe u v w z t

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {V : Type z} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An original connected intrinsic smooth leaf with its actual tangent inclusion.

Source: HPS §6B, pp.111–114, and (7.5)–(7.6), pp.127–129. Its topology is
part of the leaf data, independently of the ambient subspace topology. The
finite rank may depend on the leaf. No global Euclidean parametrization,
ambient embedding of the whole leaf, or asymptotic-set identification is imposed.
-/
structure NativeSmoothLeaf
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (center : M) where
  rank : ℕ
  Carrier : Type w
  [topology : TopologicalSpace Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  [connected : ConnectedSpace Carrier]
  [charted : ChartedSpace (Fin rank → ℝ) Carrier]
  [smoothManifold : IsManifold 𝓘(ℝ, Fin rank → ℝ) ∞ Carrier]
  point : Carrier
  inclusion : Carrier → M
  inclusion_point : inclusion point = center
  inclusion_smooth : ContMDiff 𝓘(ℝ, Fin rank → ℝ) I ∞ inclusion
  inclusion_injective : Function.Injective inclusion
  inclusion_immersed : ∀ y,
    Function.Injective (mfderiv 𝓘(ℝ, Fin rank → ℝ) I inclusion y)
  inclusion_tangent : ∀ y,
    (mfderiv 𝓘(ℝ, Fin rank → ℝ) I inclusion y).range = D (inclusion y)

attribute [instance] NativeSmoothLeaf.topology NativeSmoothLeaf.hausdorff
  NativeSmoothLeaf.secondCountable NativeSmoothLeaf.connected NativeSmoothLeaf.charted
  NativeSmoothLeaf.smoothManifold

/-- A coherent native leaf system and the lift of the original diffeomorphism.

Source: HPS §6B, pp.111–114, and §7, pp.127–129. Rebasing uses the same
ambient inclusion; advancing uses the original map, not a positive iterate.
These are explicit intrinsic diffeomorphisms with actual commuting equations.
-/
structure NativeInvariantLeafSystem
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x))
    (g : Diffeomorph I I M M ∞) where
  leaf : ∀ x, NativeSmoothLeaf I D x
  advance : ∀ x, Diffeomorph 𝓘(ℝ, Fin (leaf x).rank → ℝ)
    𝓘(ℝ, Fin (leaf (g x)).rank → ℝ) (leaf x).Carrier (leaf (g x)).Carrier ∞
  inclusion_advance : ∀ x y,
    (leaf (g x)).inclusion (advance x y) = g ((leaf x).inclusion y)
  rebase : ∀ x (y : (leaf x).Carrier),
    Diffeomorph 𝓘(ℝ, Fin (leaf x).rank → ℝ)
      𝓘(ℝ, Fin (leaf ((leaf x).inclusion y)).rank → ℝ)
      (leaf x).Carrier (leaf ((leaf x).inclusion y)).Carrier ∞
  inclusion_rebase : ∀ x (y z : (leaf x).Carrier),
    (leaf ((leaf x).inclusion y)).inclusion (rebase x y z) = (leaf x).inclusion z


/-- The literal strict forward or backward ambient orbit plaque of AP.
Source: HPS (5.5), pp.61–63, and Shub (1987), pp.72–78. -/
def adaptedOpenOrbitPlaque (g : Diffeomorph I I M M ∞)
    (d : MetricSpace M) (β : ℝ) (x : M) : Set M :=
  {y | ∀ n : ℕ, d.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) < β}

/-- The literal closed orbit core, including all natural times and time zero.
Source: Shub (1987), Theorem 6.2(3), pp.71–72, and p.78. -/
def adaptedClosedOrbitCore (g : Diffeomorph I I M M ∞)
    (d : MetricSpace M) (γ : ℝ) (x : M) : Set M :=
  {y | ∀ n : ℕ, d.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤ γ}

/-- The original strict close-pair domain. The bracket is defined on this
actual product subtype, not on untested pairs. Source: Shub 10.10, pp.126–127. -/
def adaptedClosePairDomain (d : MetricSpace M) (ε : ℝ) : Set (M × M) :=
  {p | d.dist p.1 p.2 < ε}

/-- Original ambient open ball for an explicitly selected metric. -/
def adaptedMetricBall (d : MetricSpace M) (x : M) (r : ℝ) : Set M :=
  {y | d.dist y x < r}

/-- Original ambient closed ball for that same metric. -/
def adaptedMetricClosedBall (d : MetricSpace M) (x : M) (r : ℝ) : Set M :=
  {y | d.dist y x ≤ r}

/-- The source-native topological and local-C¹ content of an AP orbit-plaque
family. Source: HPS (5.5), §6B, (7.5)–(7.6), and Shub pp.72–78.

Every set in this structure is the literal orbit set. Its intrinsic topology
comes from the supplied native smooth leaf; the restriction of the original
leaf inclusion is an ambient embedding. Enlarged local family parametrizations
contain the entire orbit plaque and commute with the same intrinsic inclusion.
No arbitrary plaque predicate or separate substituted set is supplied.
-/
structure AdaptedNativeOrbitPlaques
    (g : Diffeomorph I I M M ∞)
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x))
    (d : MetricSpace M) (β γ : ℝ) (S : NativeInvariantLeafSystem I D g) where
  plaque_in_leaf : ∀ x, adaptedOpenOrbitPlaque I g d β x ⊆ Set.range (S.leaf x).inclusion
  plaque_intrinsic_open : ∀ x,
    IsOpen ((S.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque I g d β x)
  plaque_contains_center : ∀ x, x ∈ adaptedOpenOrbitPlaque I g d β x
  plaque_embedded : ∀ x, IsEmbedding
    (fun y : (S.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque I g d β x ↦
      (S.leaf x).inclusion y.1)
  plaque_native_chart : ∀ x, ∃ r : ℕ,
    ∃ P : NativeEmbeddedPlaque I (V := Fin r → ℝ) D x,
      P.image = adaptedOpenOrbitPlaque I g d β x ∧
      ∃ T : NativePlaqueIntrinsicChart I (W := Fin (S.leaf x).rank → ℝ)
        (L := (S.leaf x).Carrier) D x P,
        T.inclusion = (S.leaf x).inclusion
  closed_core : ∀ x, adaptedClosedOrbitCore I g d γ x =
    adaptedOpenOrbitPlaque I g d β x ∩ adaptedMetricClosedBall d x γ
  strict_core : ∀ x, adaptedOpenOrbitPlaque I g d γ x =
    adaptedOpenOrbitPlaque I g d β x ∩ adaptedMetricBall d x γ
  strict_core_intrinsic_open : ∀ x,
    IsOpen ((S.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque I g d γ x)
  strict_core_contains_center : ∀ x, x ∈ adaptedOpenOrbitPlaque I g d γ x
  local_C1_family : ∀ x, ∃ r : ℕ,
    ∃ F : NativePlaqueFamily I (V := Fin r → ℝ) D x,
      ∀ p : F.centerDomain,
        adaptedOpenOrbitPlaque I g d β p.1 ⊆ (F.plaque p).image ∧
        ∃ T : NativePlaqueIntrinsicChart I (W := Fin (S.leaf p.1).rank → ℝ)
          (L := (S.leaf p.1).Carrier) D p.1 (F.plaque p),
          T.inclusion = (S.leaf p.1).inclusion

/-- Both actual factor domains and the ambient-open image of the AP product map.
Source: Shub (1987), Proposition 10.10, pp.126–127.

The factor sets are intrinsically open subsets of the specified central leaves,
contained in the literal closed orbit cores. Every pair satisfies the original
bracket caller bound. The homeomorphism has both continuous inverse components,
and its value is precisely the bracket with unstable-first inputs.
-/
structure AdaptedNativeProduct
    (f : Diffeomorph I I M M ∞)
    (Ds Du : ∀ x : M, Submodule ℝ (TangentSpace I x))
    (d : MetricSpace M) (γ ε : ℝ)
    (S : NativeInvariantLeafSystem I Ds f)
    (U : NativeInvariantLeafSystem I Du f.symm)
    (bracket : adaptedClosePairDomain (M := M) d ε → M) (x : M) where
  stableDomain : Set (S.leaf x).Carrier
  unstableDomain : Set (U.leaf x).Carrier
  stable_open : IsOpen stableDomain
  unstable_open : IsOpen unstableDomain
  stable_center : (S.leaf x).point ∈ stableDomain
  unstable_center : (U.leaf x).point ∈ unstableDomain
  stable_core : ∀ s ∈ stableDomain,
    (S.leaf x).inclusion s ∈ adaptedClosedOrbitCore I f d γ x
  unstable_core : ∀ u ∈ unstableDomain,
    (U.leaf x).inclusion u ∈ adaptedClosedOrbitCore I f.symm d γ x
  caller : ∀ (s : stableDomain) (u : unstableDomain),
    d.dist ((U.leaf x).inclusion u.1) ((S.leaf x).inclusion s.1) < ε
  neighborhood : Set M
  neighborhood_open : IsOpen neighborhood
  neighborhood_center : x ∈ neighborhood
  product : (stableDomain × unstableDomain) ≃ₜ neighborhood
  product_eq : ∀ (s : stableDomain) (u : unstableDomain),
    (product (s, u) : M) =
      bracket ⟨((U.leaf x).inclusion u.1, (S.leaf x).inclusion s.1), caller s u⟩


/-- Length of an actual native piecewise-smooth path, measured after its original
inclusion by the same ambient tensor. Source: Lee (2003), p.275, and HPS
(6B.4), pp.111–114. This is the pullback length written without choosing an
unrelated leaf metric or postulating an equality of distance conventions. -/
noncomputable def nativeLeafPathLength
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {x : M}
    (L : NativeSmoothLeaf I D x) {y z : L.Carrier}
    (p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, Fin L.rank → ℝ) y z) : ℝ :=
  ∑ i : Fin (p.n + 1), ∫ t in p.time i.castSucc..p.time i.succ,
    let v := mfderivWithin 𝓘(ℝ) I (L.inclusion ∘ p.piece i)
      (p.pieceInterval i) t (show TangentSpace 𝓘(ℝ) t from (1 : ℝ))
    Real.sqrt (h.inner (L.inclusion (p.piece i t)) v v)

/-- The actual intrinsic piecewise-smooth pullback length infimum, on the
original connected native leaf. Source: Lee (2003), pp.275,277–279. The AP
conclusion supplies finiteness and contraction separately. -/
noncomputable def nativeLeafPathEDist
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {x : M}
    (L : NativeSmoothLeaf I D x) (y z : L.Carrier) : ℝ≥0∞ :=
  ⨅ p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, Fin L.rank → ℝ) y z,
    ENNReal.ofReal (nativeLeafPathLength I h L p)

end HolomorphicAnosov
