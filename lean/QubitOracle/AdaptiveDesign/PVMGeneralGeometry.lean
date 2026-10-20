-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeometry

/-! An arbitrary finite identifying exploration library.  The hypotheses are
static properties of the supplied projective bases; no statistical limit or
Fisher optimality is assumed of exploration. -/
namespace QubitOracle.AdaptiveDesign.PVMGeneralGeometry
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PVMGeometry FiniteFrameCoercivity CoerciveLeastSquares
open scoped BigOperators InnerProductSpace
noncomputable section

/-- The library size is arbitrary.  Identification is a property of the
combined projectors, not of each individual basis. -/
class ExplorationLibrary (d : ℕ) where
  count : ℕ
  count_pos : 0 < count
  basis : Fin count → Action d
  identifies : ∀ A : HermitianSpace (d+1),
    (∀ l k, ⟪basisEffect (basis l) k, A⟫_ℝ = 0) → A = 0
  /-- Any admissible exploitation frame may be supplied independently of
  the identifying library. The default preserves previous instances. -/
  exploitationFrame : OracleFrame d := canonicalOracleFrame d

def exploitationFrame (d : ℕ) [L : ExplorationLibrary d] : OracleFrame d :=
  L.exploitationFrame

def withExploitationFrame {d : ℕ} (L : ExplorationLibrary d) (F : OracleFrame d) :
    ExplorationLibrary d := { L with exploitationFrame := F }

@[simp] theorem withExploitationFrame_frame {d : ℕ}
    (L : ExplorationLibrary d) (F : OracleFrame d) :
    (withExploitationFrame L F).exploitationFrame = F := rfl

def exploitationChiAction {d : ℕ} [ExplorationLibrary d] (U : Action d) : Action d :=
  ⟨transportedChiBasis U.matrix (exploitationFrame d),
    transportedChiBasis_mem_unitary U.matrix U.unitary _⟩

def exploitationTauAction {d : ℕ} [ExplorationLibrary d] (U : Action d) : Action d :=
  ⟨transportedTauBasis U.matrix (exploitationFrame d),
    transportedTauBasis_mem_unitary U.matrix U.unitary _⟩

abbrev ExplorationIndex (d : ℕ) [L : ExplorationLibrary d] := Fin L.count

instance (d : ℕ) [L : ExplorationLibrary d] : Nonempty (ExplorationIndex d) :=
  ⟨⟨0, L.count_pos⟩⟩

def explorationBasis {d : ℕ} [L : ExplorationLibrary d]
    (l : ExplorationIndex d) : Action d := L.basis l

theorem exploration_card_pos (d : ℕ) [L : ExplorationLibrary d] :
    (0 : ℝ) < Fintype.card (ExplorationIndex d) := by
  simpa [ExplorationIndex] using (Nat.cast_pos.mpr L.count_pos : (0 : ℝ) < L.count)

theorem exploration_separates {d : ℕ} [L : ExplorationLibrary d]
    (A : HermitianSpace (d+1))
    (h : ∀ l k, ⟪basisEffect (explorationBasis l) k, A⟫_ℝ = 0) : A = 0 :=
  L.identifies A h

def explorationFrame (d : ℕ) [ExplorationLibrary d] :
    HermitianSpace (d+1) →ₗ[ℝ] HermitianSpace (d+1) :=
  (Fintype.card (ExplorationIndex d) : ℝ)⁻¹ •
    frameOperator (fun o : ExplorationIndex d × Fin (d+1) =>
      basisEffect (explorationBasis o.1) o.2)

/-- A positive frame constant is derived from identification and finite
dimensionality, rather than supplied as an additional library assumption. -/
theorem explorationFrame_coercive (d : ℕ) [ExplorationLibrary d] :
    ∃ κ : ℝ, 0 < κ ∧ Coercive (explorationFrame d) κ := by
  obtain ⟨κ, hκ, h⟩ := exists_positive_coercivity_of_separating
    (fun o : ExplorationIndex d × Fin (d+1) => basisEffect (explorationBasis o.1) o.2)
    (fun A hA => exploration_separates A (fun l k => hA (l,k)))
  have hc := exploration_card_pos d
  refine ⟨(Fintype.card (ExplorationIndex d) : ℝ)⁻¹ * κ, by positivity, ?_⟩
  intro A
  have hh := mul_le_mul_of_nonneg_left (h A) (inv_nonneg.mpr hc.le)
  simpa [explorationFrame, inner_smul_right, mul_assoc] using hh

/-- Spectral measurements of any spanning Hermitian generator family
identify every state.  This is the certificate used by Pauli-type examples. -/
theorem identifies_of_spanning_generators {d K J : ℕ}
    (bases : Fin K → Action d) (generator : Fin J → HermitianSpace (d+1))
    (spanning : ∀ A : HermitianSpace (d+1),
      (∀ j, ⟪generator j, A⟫_ℝ = 0) → A = 0)
    (coeff : Fin J → Fin K → Fin (d+1) → ℝ)
    (spectral : ∀ j, generator j =
      ∑ l, ∑ k, coeff j l k • basisEffect (bases l) k) :
    ∀ A : HermitianSpace (d+1),
      (∀ l k, ⟪basisEffect (bases l) k, A⟫_ℝ = 0) → A = 0 := by
  intro A hA
  apply spanning A
  intro j
  rw [spectral]
  simp only [sum_inner, real_inner_smul_left, hA, mul_zero, Finset.sum_const_zero]

end
end QubitOracle.AdaptiveDesign.PVMGeneralGeometry

-/
