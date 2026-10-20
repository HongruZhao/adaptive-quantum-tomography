import Mathlib.Analysis.Normed.Group.Basic
/-!
# Consistency of nearest pure-state projection

This file isolates the deterministic argument needed after consistency of an
ambient estimator.  If the true point belongs to the constraint set and every
projected estimate is a nearest point in that set, then projection increases
the estimation error by at most a factor of two.  Consequently, convergence
of the raw estimates implies convergence of the projected estimates.

No existence or uniqueness of nearest points is assumed or proved here.
-/

namespace QubitOracle.Paper.PureMultilevelNearestPureProjection

open Filter Set Topology

section AbstractNormedSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- A nearest constrained point is at most twice as far from any true
constrained point as the raw estimate is. -/
theorem nearestPoint_error_le_two
    (pureSet : Set E) (truth raw projected : E)
    (htruth : truth ∈ pureSet)
    (hnearest : ∀ candidate ∈ pureSet,
      ‖projected - raw‖ ≤ ‖candidate - raw‖) :
    ‖projected - truth‖ ≤ 2 * ‖raw - truth‖ := by
  calc
    ‖projected - truth‖ = ‖(projected - raw) + (raw - truth)‖ := by
      congr 1
      abel
    _ ≤ ‖projected - raw‖ + ‖raw - truth‖ := norm_add_le _ _
    _ ≤ ‖truth - raw‖ + ‖raw - truth‖ :=
      add_le_add (hnearest truth htruth) (le_refl _)
    _ = 2 * ‖raw - truth‖ := by
      rw [norm_sub_rev]
      ring

/-- Source-clean consistency theorem for nearest-point constrained
projection in an arbitrary normed additive space. -/
theorem nearestPoint_tendsto
    (pureSet : Set E) (truth : E) (raw projected : ℕ → E)
    (htruth : truth ∈ pureSet)
    (hnearest : ∀ n candidate, candidate ∈ pureSet →
      ‖projected n - raw n‖ ≤ ‖candidate - raw n‖)
    (hraw : Tendsto raw atTop (𝓝 truth)) :
    Tendsto projected atTop (𝓝 truth) := by
  rw [Metric.tendsto_atTop] at hraw ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hraw (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  calc
    ‖projected n - truth‖ ≤ 2 * ‖raw n - truth‖ :=
      nearestPoint_error_le_two pureSet truth (raw n) (projected n)
        htruth (hnearest n)
    _ < 2 * (ε / 2) := by
      exact mul_lt_mul_of_pos_left
        (by simpa [dist_eq_norm] using hN n hn) (by norm_num)
    _ = ε := by ring

end AbstractNormedSpace

section EmbeddedPureStates

variable {E Pure : Type*} [NormedAddCommGroup E]

/-- The ambient error bound when admissible pure states are represented by an
embedding into a normed space (for example, rank-one Hermitian matrices with
the Frobenius norm). -/
theorem nearestPureProjection_error_le_two
    (embed : Pure → E) (truth : Pure) (raw : E) (projected : Pure)
    (hnearest : ∀ candidate : Pure,
      ‖embed projected - raw‖ ≤ ‖embed candidate - raw‖) :
    ‖embed projected - embed truth‖ ≤ 2 * ‖raw - embed truth‖ := by
  apply nearestPoint_error_le_two (Set.range embed) (embed truth) raw
    (embed projected)
  · exact ⟨truth, rfl⟩
  · intro candidate hcandidate
    obtain ⟨pureCandidate, rfl⟩ := hcandidate
    exact hnearest pureCandidate

/-- Consistency of nearest pure-state projection in the ambient norm.  For
Hermitian raw estimates and the Frobenius norm, a leading rank-one Frobenius
projection is an instance whenever it satisfies the displayed nearest-point
property. -/
theorem nearestPureProjection_tendsto
    (embed : Pure → E) (truth : Pure)
    (raw : ℕ → E) (projected : ℕ → Pure)
    (hnearest : ∀ n candidate,
      ‖embed (projected n) - raw n‖ ≤ ‖embed candidate - raw n‖)
    (hraw : Tendsto raw atTop (𝓝 (embed truth))) :
    Tendsto (fun n => embed (projected n)) atTop (𝓝 (embed truth)) := by
  apply nearestPoint_tendsto (Set.range embed) (embed truth) raw
    (fun n => embed (projected n))
  · exact ⟨truth, rfl⟩
  · intro n candidate hcandidate
    obtain ⟨pureCandidate, rfl⟩ := hcandidate
    exact hnearest n pureCandidate
  · exact hraw

end EmbeddedPureStates

end QubitOracle.Paper.PureMultilevelNearestPureProjection
