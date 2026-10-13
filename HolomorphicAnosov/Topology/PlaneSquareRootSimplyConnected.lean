import HolomorphicAnosov.Analysis.Complex.ConwaySquareRootCriterionDiskBiholomorphism
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace HolomorphicAnosov.Topology

/-- A nonempty connected open plane set on which every nowhere-zero holomorphic
function has a holomorphic square root is simply connected.

Source: Conway, Functions of One Complex Variable I, VIII Theorem 2.2,
pp.202–204, implications (h) to (i) to (a), using VII Lemma 4.3.
For the whole plane, convexity gives a contraction. Otherwise the square-root
criterion gives mutually inverse holomorphic maps between the domain and the
unit disk. Their restrictions are a homeomorphism. The disk is contractible by
its straight-line contraction, hence simply connected; transport this property
through the homeomorphism. This contracts arbitrary continuous loops. -/
theorem conway_square_root_criterion_simply_connected
    {U : Set ℂ} (hUopen : IsOpen U) (hUconnected : IsConnected U)
    (hsqrt : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z) :
    IsSimplyConnected U := by
  by_cases hproper : U = Set.univ
  · subst U
    have : ContractibleSpace (Set.univ : Set ℂ) :=
      (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
    exact SimplyConnectedSpace.ofContractible _
  · obtain ⟨a, ha⟩ := hUconnected.nonempty
    obtain ⟨F, G, hF, hG, hbij, hmap, hGF, hFG, _⟩ :=
      conway_square_root_criterion_disk_biholomorphism hUopen hUconnected hproper hsqrt a ha
    let e : U ≃ₜ Metric.ball (0 : ℂ) 1 := {
      toFun := fun z ↦ ⟨F z, hbij.mapsTo z.property⟩
      invFun := fun w ↦ ⟨G w, hmap w.property⟩
      left_inv := fun z ↦ Subtype.ext (hGF z z.property)
      right_inv := fun w ↦ Subtype.ext (hFG w w.property)
      continuous_toFun := hF.continuousOn.domRestrict.subtype_mk _
      continuous_invFun := hG.continuousOn.domRestrict.subtype_mk _ }
    have : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, Metric.mem_ball_self (by norm_num)⟩
    have : SimplyConnectedSpace (Metric.ball (0 : ℂ) 1) :=
      SimplyConnectedSpace.ofContractible _
    exact e.toHomotopyEquiv.simplyConnectedSpace

end HolomorphicAnosov.Topology

