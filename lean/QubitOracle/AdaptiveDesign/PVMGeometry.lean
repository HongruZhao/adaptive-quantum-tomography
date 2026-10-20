import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.Paper.RankOneStageContinuity

/-! Projective bases, a concrete globally identifying exploration family,
and the two locally Fisher-optimal projective bases. -/
namespace QubitOracle.AdaptiveDesign.PVMGeometry
open QubitOracle QubitOracle.Paper
open GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController
open FiniteFrameCoercivity CoerciveLeastSquares
open scoped BigOperators Topology InnerProductSpace ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

/-- An orthogonal real matrix with a uniform first row exists in every dimension. -/
theorem exists_oracleFrame (d : ℕ) : Nonempty (OracleFrame d) := by
  let a : ℝ := 1 / Real.sqrt (d+1:ℝ)
  let u : EuclideanSpace ℝ (Fin (d+1)) := WithLp.toLp 2 (fun _ => a)
  have hu : ‖u‖ = 1 := by
    have ha : (d+1:ℝ) * a^2 = 1 := by
      dsimp [a]
      rw [div_pow, Real.sq_sqrt (by positivity)]
      field_simp
    have hs : ‖u‖^2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa [u, Nat.cast_add, Nat.cast_one] using ha
    nlinarith [norm_nonneg u]
  let v : Fin (d+1) → EuclideanSpace ℝ (Fin (d+1)) :=
    fun i => if i = 0 then u else EuclideanSpace.basisFun (Fin (d+1)) ℝ i
  have hv : Orthonormal ℝ (({0} : Set (Fin (d+1))).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Fin (d+1)) = 0 := i.property
    have hj : (j : Fin (d+1)) = 0 := j.property
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    subst j
    simp only [Set.domRestrict, v, hi, if_pos]
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (ι := Fin (d+1)) (𝕜 := ℝ)) hv
  have hB0 : B 0 = u := by rw [hB 0 (by simp)]; simp [v]
  let E0 := EuclideanSpace.basisFun (Fin (d+1)) ℝ
  let W := (E0.toBasis.toMatrix B).transpose
  have hW : W ∈ Matrix.orthogonalGroup (Fin (d+1)) ℝ := by
    have h := OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary E0 B
    simpa [W] using Matrix.transpose_mem_unitaryGroup_iff.mpr h
  refine ⟨⟨W, hW, ?_⟩⟩
  intro k
  simp [W, E0, Module.Basis.toMatrix_apply, hB0, u, a]

def canonicalOracleFrame (d : ℕ) : OracleFrame d := Classical.choice (exists_oracleFrame d)

def coordinateEffect {d : ℕ} (k : Fin (d+1)) : HermitianSpace (d+1) :=
  ofMatrix (projector (coordinate k)) (projector_posSemidef _).isHermitian

/-- The effects here are full projectors, without the probability of choosing a basis. -/
def basisEffect {d : ℕ} (U : Action d) (k : Fin (d+1)) : HermitianSpace (d+1) :=
  conjugationIsometry U.matrix U.unitary (coordinateEffect k)

theorem basisEffect_matrix {d : ℕ} (U : Action d) (k : Fin (d+1)) :
    toMatrix (basisEffect U k) = projector (fun i => U.matrix i k) := by
  change U.matrix * projector (coordinate k) * U.matrix.conjTranspose = _
  rw [← projector_mulVec]
  congr 1
  funext i
  simp [coordinate, Matrix.mulVec_single_one]

theorem basisEffect_sum {d : ℕ} (U : Action d) :
    ∑ k, toMatrix (basisEffect U k) = 1 := by
  change (∑ k, U.matrix * projector (coordinate k) * U.matrix.conjTranspose) = 1
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, coordinate_projector_sum, Matrix.mul_one]
  exact Matrix.mem_unitaryGroup_iff.mp U.unitary

theorem basisEffect_positive {d : ℕ} (U : Action d) (k : Fin (d+1)) :
    (toMatrix (basisEffect U k)).PosSemidef := by
  rw [basisEffect_matrix]
  exact projector_posSemidef _

theorem basisEffect_orthogonal {d : ℕ} (U : Action d) (j k : Fin (d+1)) :
    toMatrix (basisEffect U j) * toMatrix (basisEffect U k) =
      if j = k then toMatrix (basisEffect U j) else 0 := by
  have hu : U.matrix.conjTranspose * U.matrix = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.unitary
  have hc : projector (coordinate j) * projector (coordinate k) =
      if j = k then projector (coordinate j) else 0 := by
    ext a b
    by_cases hjk : j = k
    · subst k; simp [projector, coordinate, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.single_apply]
    · simp [projector, coordinate, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.single_apply, hjk, Ne.symm hjk]
  change (U.matrix * projector (coordinate j) * U.matrix.conjTranspose) *
    (U.matrix * projector (coordinate k) * U.matrix.conjTranspose) = _
  calc
    _ = (U.matrix * projector (coordinate j)) *
        (U.matrix.conjTranspose * U.matrix) *
        (projector (coordinate k) * U.matrix.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = U.matrix * (projector (coordinate j) * projector (coordinate k)) *
        U.matrix.conjTranspose := by rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hc]
      split_ifs
      · rfl
      · simp

def basisFrame {d : ℕ} (U : Action d) : HermitianSpace (d+1) →ₗ[ℝ] HermitianSpace (d+1) :=
  frameOperator (basisEffect U)

theorem basisFrame_nonnegative {d : ℕ} (U : Action d) : Coercive (basisFrame U) 0 := by
  intro x
  rw [zero_mul, basisFrame, frameOperator_quadratic]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

def basisProbability {d : ℕ} (theta : PhysicalParameter (d+1)) (U : Action d)
    (k : Fin (d+1)) : ℝ := ⟪basisEffect U k, theta.1⟫_ℝ

theorem basisProbability_nonnegative {d : ℕ} (theta : PhysicalParameter (d+1))
    (U : Action d) (k : Fin (d+1)) : 0 ≤ basisProbability theta U k := by
  rw [basisProbability, inner_eq_trace, basisEffect_matrix, trace_mul_projector]
  have h := theta.2.1.dotProduct_mulVec_nonneg (fun i => U.matrix i k)
  have hr := (Complex.nonneg_iff.mp h).1
  simpa [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hr

theorem basisProbability_sum {d : ℕ} (theta : PhysicalParameter (d+1)) (U : Action d) :
    ∑ k, basisProbability theta U k = 1 := by
  simp_rw [basisProbability, inner_eq_trace]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, basisEffect_sum,
    Matrix.mul_one, theta.2.2]
  rfl

def basisBound (d : ℕ) : ℝ := ∑ k : Fin (d+1), ‖coordinateEffect k‖

theorem basisBound_nonnegative (d : ℕ) : 0 ≤ basisBound d :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem basisEffect_bound {d : ℕ} (U : Action d) (k : Fin (d+1)) :
    ‖basisEffect U k‖ ≤ basisBound d := by
  rw [basisEffect, (conjugationIsometry U.matrix U.unitary).norm_map]
  exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ k)

/-- Offline exploration uses the previous elementary library in the FULL space C^D. -/
abbrev ExplorationIndex (d : ℕ) := LibraryIndex (d+1)

def explorationVector {d : ℕ} (l : ExplorationIndex d) : PureVector d :=
  ⟨libraryVector l, libraryVector_normSq l⟩

def explorationBasis {d : ℕ} (l : ExplorationIndex d) : Action d :=
  ⟨Classical.choose (exists_unitary_firstColumn (explorationVector l)),
    (Classical.choose_spec (exists_unitary_firstColumn (explorationVector l))).1⟩

theorem explorationBasis_first {d : ℕ} (l : ExplorationIndex d) :
    toMatrix (basisEffect (explorationBasis l) 0) = projector (libraryVector l) := by
  rw [basisEffect_matrix]
  congr 1
  exact (Classical.choose_spec (exists_unitary_firstColumn (explorationVector l))).2

theorem exploration_separates {d : ℕ} (x : HermitianSpace (d+1))
    (h : ∀ l k, ⟪basisEffect (explorationBasis l) k, x⟫_ℝ = 0) : x = 0 := by
  apply toMatrix_injective
  change toMatrix x = 0
  apply (library_quadratic_eq_zero_iff (toMatrix x)).mp
  intro l
  have hh := congrArg Complex.ofReal (h l 0)
  rw [complex_inner_eq_trace, explorationBasis_first, trace_mul_projector] at hh
  simpa using hh

def explorationFrame (d : ℕ) : HermitianSpace (d+1) →ₗ[ℝ] HermitianSpace (d+1) :=
  (Fintype.card (ExplorationIndex d):ℝ)⁻¹ •
    frameOperator (fun o : ExplorationIndex d × Fin (d+1) =>
      basisEffect (explorationBasis o.1) o.2)

theorem explorationFrame_coercive (d : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ Coercive (explorationFrame d) κ := by
  obtain ⟨κ,hκ,h⟩ := exists_positive_coercivity_of_separating
    (fun o : ExplorationIndex d × Fin (d+1) => basisEffect (explorationBasis o.1) o.2)
    (fun x hx => exploration_separates x (fun l k => hx (l,k)))
  have hc : (0:ℝ) < Fintype.card (ExplorationIndex d) := by
    rw [show Fintype.card (ExplorationIndex d) = (d+1)*(4*(d+1)+1) from library_card (d+1)]
    positivity
  refine ⟨(Fintype.card (ExplorationIndex d):ℝ)⁻¹ * κ, by positivity, ?_⟩
  intro x
  have hh := mul_le_mul_of_nonneg_left (h x) (inv_nonneg.mpr hc.le)
  simpa [explorationFrame, inner_smul_right, mul_assoc] using hh

def chiAction {d : ℕ} (U : Action d) : Action d :=
  ⟨transportedChiBasis U.matrix (canonicalOracleFrame d),
    transportedChiBasis_mem_unitary U.matrix U.unitary _⟩
def tauAction {d : ℕ} (U : Action d) : Action d :=
  ⟨transportedTauBasis U.matrix (canonicalOracleFrame d),
    transportedTauBasis_mem_unitary U.matrix U.unitary _⟩

end
end QubitOracle.AdaptiveDesign.PVMGeometry
