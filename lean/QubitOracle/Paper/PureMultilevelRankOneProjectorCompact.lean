import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import QubitOracle.Paper.PureMultilevelCompactNearestProjection
import QubitOracle.Paper.PureStateFoundations
/-!
# Compactness of finite-dimensional pure projectors

Normalized complex vectors form a compact set in every fixed finite
dimension.  The rank-one projector map is continuous, hence its Frobenius
image is compact.  This supplies the compactness premise required by the
kernel-defined nearest-pure projection estimator.
-/

namespace QubitOracle.Paper
namespace PureMultilevelRankOneProjectorCompact

open Set Metric
open scoped Matrix.Norms.Frobenius

noncomputable section

/-- Normalized state vectors in Hilbert dimension `D`. -/
def normalizedPureVectorSet (D : Nat) : Set (Fin D -> Complex) :=
  {psi | pureStateNormSq psi = 1}

abbrev NormalizedPureVector (D : Nat) := normalizedPureVectorSet D

/-- Frobenius-ambient rank-one projector represented by a normalized vector. -/
def normalizedRankOneProjectorEmbed (D : Nat) :
    NormalizedPureVector D -> Matrix (Fin D) (Fin D) Complex :=
  fun psi => rankOneDensity psi.1

theorem continuous_pureStateNormSq (D : Nat) :
    Continuous (fun psi : Fin D -> Complex => pureStateNormSq psi) := by
  unfold pureStateNormSq
  fun_prop

theorem isClosed_normalizedPureVectorSet (D : Nat) :
    IsClosed (normalizedPureVectorSet D) := by
  exact isClosed_singleton.preimage (continuous_pureStateNormSq D)

theorem normalizedPureVector_norm_le_one
    {D : Nat} {psi : Fin D -> Complex}
    (hpsi : psi ∈ normalizedPureVectorSet D) :
    ‖psi‖ <= 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hterm : Complex.normSq (psi i) <= pureStateNormSq psi := by
    unfold pureStateNormSq
    exact Finset.single_le_sum
      (fun j _ => Complex.normSq_nonneg (psi j)) (Finset.mem_univ i)
  have hsum : pureStateNormSq psi = 1 := hpsi
  rw [hsum] at hterm
  nlinarith [norm_nonneg (psi i), Complex.sq_norm (psi i)]

theorem isBounded_normalizedPureVectorSet (D : Nat) :
    Bornology.IsBounded (normalizedPureVectorSet D) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : Fin D -> Complex)]
  refine ⟨1, fun psi hpsi => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact normalizedPureVector_norm_le_one hpsi

theorem isCompact_normalizedPureVectorSet (D : Nat) :
    IsCompact (normalizedPureVectorSet D) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_normalizedPureVectorSet D)
    (isBounded_normalizedPureVectorSet D)

theorem continuous_rankOneDensity (D : Nat) :
    Continuous
      (fun psi : Fin D -> Complex =>
        (rankOneDensity psi : Matrix (Fin D) (Fin D) Complex)) := by
  unfold rankOneDensity
  fun_prop

/-- The physical set of normalized rank-one projectors is compact in the
Frobenius matrix topology. -/
theorem isCompact_range_normalizedRankOneProjectorEmbed (D : Nat) :
    IsCompact (Set.range (normalizedRankOneProjectorEmbed D)) := by
  have himage := (isCompact_normalizedPureVectorSet D).image
    (continuous_rankOneDensity D)
  have hrange :
      Set.range (normalizedRankOneProjectorEmbed D) =
        (fun psi : Fin D -> Complex =>
          (rankOneDensity psi : Matrix (Fin D) (Fin D) Complex)) ''
            normalizedPureVectorSet D := by
    ext M
    constructor
    · rintro ⟨psi, rfl⟩
      exact ⟨psi.1, psi.2, rfl⟩
    · rintro ⟨psi, hpsi, rfl⟩
      exact ⟨⟨psi, hpsi⟩, rfl⟩
  rw [hrange]
  exact himage

/-- Exact nearest rank-one projector selected in Frobenius norm. -/
def nearestNormalizedRankOneProjector
    (D : Nat) (truth : NormalizedPureVector D)
    (raw : Matrix (Fin D) (Fin D) Complex) : NormalizedPureVector D :=
  PureMultilevelCompactNearestProjection.compactNearestPureProjection
    (normalizedRankOneProjectorEmbed D) truth
    (isCompact_range_normalizedRankOneProjectorEmbed D) raw

theorem nearestNormalizedRankOneProjector_is_nearest
    (D : Nat) (truth : NormalizedPureVector D)
    (raw : Matrix (Fin D) (Fin D) Complex)
    (candidate : NormalizedPureVector D) :
    ‖normalizedRankOneProjectorEmbed D
        (nearestNormalizedRankOneProjector D truth raw) - raw‖ <=
      ‖normalizedRankOneProjectorEmbed D candidate - raw‖ :=
  PureMultilevelCompactNearestProjection.compactNearestPureProjection_is_nearest
    (normalizedRankOneProjectorEmbed D) truth
    (isCompact_range_normalizedRankOneProjectorEmbed D) raw candidate

end

end PureMultilevelRankOneProjectorCompact
end QubitOracle.Paper
