import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.PVMGeometry
import QubitOracle.FiniteGillMassar
/-! A recorded random PVM setting is exactly a POVM, in Born probability.
This proves the probabilistic implementation assertion in Section 4.2
and Appendix S4.1, including zero probabilities and arbitrary input states.
The elementary family itself is constructed in a separate module.
-/
namespace QubitOracle.AdaptiveDesign.RandomizedPVM
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn PVMGeometry
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000
variable {d : ℕ} {L : Type} [Fintype L]

def measurement (weight : L → ℝ) (basis : L → Action d)
    (hw : ∀ l, 0 ≤ weight l) (hsum : ∑ l, weight l = 1) :
    FinitePOVM (Fin (d+1)) (L × Fin (d+1)) where
  effect y := weight y.1 • toMatrix (basisEffect (basis y.1) y.2)
  positive y := (basisEffect_positive (basis y.1) y.2).smul (hw y.1)
  complete := by
    simp only [Fintype.sum_prod_type, ← Finset.smul_sum, basisEffect_sum,
      ← Finset.sum_smul, hsum, one_smul]

theorem complete_born_law (weight : L → ℝ) (basis : L → Action d)
    (hw : ∀ l, 0 ≤ weight l) (hsum : ∑ l, weight l = 1)
    (rho : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (l : L) (k : Fin (d+1)) :
    (Matrix.trace (rho * (measurement weight basis hw hsum).effect (l,k))).re =
      weight l * (Matrix.trace (rho * toMatrix (basisEffect (basis l) k))).re := by
  simp [measurement, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul]

theorem complete_law_as_basis_probability (weight : L → ℝ) (basis : L → Action d)
    (hw : ∀ l, 0 ≤ weight l) (hsum : ∑ l, weight l = 1)
    (rho : PhysicalParameter (d+1)) (l : L) (k : Fin (d+1)) :
    (Matrix.trace (toMatrix rho.val * (measurement weight basis hw hsum).effect (l,k))).re =
      weight l * basisProbability rho (basis l) k := by
  rw [complete_born_law, basisProbability, inner_eq_trace]

theorem discarded_basis_law (weight : L → ℝ) (basis : L → Action d)
    (hw : ∀ l, 0 ≤ weight l) (hsum : ∑ l, weight l = 1)
    (rho : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (k : Fin (d+1)) :
    ∑ l, (Matrix.trace (rho * (measurement weight basis hw hsum).effect (l,k))).re =
      (Matrix.trace (rho * ∑ l, weight l • toMatrix (basisEffect (basis l) k))).re := by
  simp only [measurement, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

def uniformWeight (L : Type) [Fintype L] : L → ℝ := fun _ => (Fintype.card L : ℝ)⁻¹

theorem uniformWeight_nonnegative (l : L) : 0 ≤ uniformWeight L l := by
  unfold uniformWeight
  positivity

theorem uniformWeight_sum [Nonempty L] : ∑ l, uniformWeight L l = 1 := by
  have hn : (Fintype.card L : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α := L))
  simp [uniformWeight, hn]

theorem hardware_state_gate_born_law {ι : Type*} [Fintype ι]
    (rho F G : Matrix ι ι ℂ) :
    Matrix.trace ((G * rho * G.conjTranspose) * F) =
      Matrix.trace (rho * (G.conjTranspose * F * G)) := by
  calc
    _ = Matrix.trace (G * (rho * (G.conjTranspose * F))) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (rho * (G.conjTranspose * F) * G) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end
end QubitOracle.AdaptiveDesign.RandomizedPVM
