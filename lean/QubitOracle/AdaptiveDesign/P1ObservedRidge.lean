import QubitOracle.AdaptiveDesign.P1WeightedMoments

/-! Coercivity and consistency of the observed-axis ridge normal equation.
The Gram matrix here is the realized matrix, not its predictable average. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def quadratic (A : Mat) (x : Fin 3 → ℝ) : ℝ := x ⬝ᵥ (A.mulVec x)
def entrySize (A : Mat) : ℝ := ∑ i, ∑ j, |A i j|
def Lower (A : Mat) (c : ℝ) : Prop := ∀ x, c * blochNormSq x ≤ quadratic A x

theorem quadratic_add (A B : Mat) (x : Fin 3 → ℝ) :
    quadratic (A+B) x = quadratic A x + quadratic B x := by
  simp [quadratic,Matrix.add_mulVec,dotProduct_add]

theorem quadratic_smul (c : ℝ) (A : Mat) (x : Fin 3 → ℝ) :
    quadratic (c • A) x = c * quadratic A x := by
  simp [quadratic,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

theorem quadratic_one (x : Fin 3 → ℝ) : quadratic 1 x = blochNormSq x := by
  simp [quadratic,Matrix.one_mulVec,dotProduct,blochNormSq,pow_two]

theorem quadratic_outer (u x : Fin 3 → ℝ) : quadratic (blochOuter u) x = (blochDot u x)^2 := by
  simp [quadratic,blochOuter,Matrix.mulVec,dotProduct,blochDot,Fin.sum_univ_succ]
  ring

theorem quadratic_sum {ι : Type*} (s : Finset ι) (A : ι → Mat) (x : Fin 3 → ℝ) :
    quadratic (∑ k ∈ s, A k) x = ∑ k ∈ s, quadratic (A k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadratic]
  | @insert k s hk ih => simp [Finset.sum_insert hk,quadratic_add,ih]

theorem coordinate_sq_le (x : Fin 3 → ℝ) (i : Fin 3) : (x i)^2 ≤ blochNormSq x :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

theorem quadratic_abs_le (A : Mat) (x : Fin 3 → ℝ) :
    |quadratic A x| ≤ entrySize A * blochNormSq x := by
  unfold quadratic Matrix.mulVec dotProduct
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i, |∑ j, x i * (A i j * x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j| * blochNormSq x := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      have hprod : |x i| * |x j| ≤ blochNormSq x := by
        nlinarith [coordinate_sq_le x i,coordinate_sq_le x j,
          sq_nonneg (|x i|-|x j|),sq_abs (x i),sq_abs (x j)]
      simp only [abs_mul]
      calc
        _ = |A i j| * (|x i| * |x j|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = _ := by simp only [entrySize,Finset.sum_mul]

theorem lower_perturb (A B : Mat) (c : ℝ) (hA : Lower A c) :
    Lower (A+B) (c-entrySize B) := by
  intro x
  rw [quadratic_add]
  have h := neg_le_of_abs_le (quadratic_abs_le B x)
  have h' := hA x
  nlinarith

theorem gram_lower (a : Action) (c : ℝ) (hc : ∀ k, c ≤ a.weight k) : Lower (gram a) c := by
  intro x
  have hresolution : ∑ k, blochOuter (axis a k) = (1:Mat) := by
    ext i j
    simpa only [Matrix.sum_apply,blochOuter,Matrix.one_apply,axis] using a.frame.resolution i j
  rw [gram,quadratic_sum]
  simp_rw [quadratic_smul,quadratic_outer]
  have he : ∑ k, (blochDot (axis a k) x)^2 = blochNormSq x := by
    rw [← quadratic_one,← hresolution,quadratic_sum]
    simp_rw [quadratic_outer]
  calc
    _ = ∑ k, c * (blochDot (axis a k) x)^2 := by rw [← Finset.mul_sum,he]
    _ ≤ _ := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hc k) (sq_nonneg _))

theorem ridge_posDef (ridge : ℝ) (hr : 0 < ridge) (a : ℕ → Fin 3 → ℝ) (n : ℕ) :
    (ridge • (1:Mat) + ∑ k ∈ Finset.range n, blochOuter (a k)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [Matrix.conjTranspose_apply,Matrix.add_apply,Matrix.smul_apply,
      Matrix.one_apply,Matrix.sum_apply,blochOuter,mul_comm,eq_comm]
  · intro x hx
    change 0 < quadratic (ridge • 1 + ∑ k ∈ Finset.range n, blochOuter (a k)) x
    rw [quadratic_add,quadratic_smul,quadratic_one,quadratic_sum]
    simp_rw [quadratic_outer]
    have hxpos : 0 < blochNormSq x := by
      have hn := normSq_nonneg x
      by_contra h
      have he : blochNormSq x = 0 := le_antisymm (le_of_not_gt h) hn
      apply hx
      funext i
      have hi := coordinate_sq_le x i
      rw [he] at hi
      change x i = 0
      nlinarith [sq_nonneg (x i)]
    exact add_pos_of_pos_of_nonneg (mul_pos hr hxpos) (Finset.sum_nonneg fun k _ => sq_nonneg _)

theorem lower_to_coercive (A : Mat) (c : ℝ) (h : Lower A c) :
    CoerciveLeastSquares.Coercive A.toEuclideanLin c := by
  intro x
  have hh := h (WithLp.ofLp x)
  simpa only [quadratic,Matrix.toEuclideanLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial,WithLp.ofLp_toLp,← EuclideanSpace.real_norm_sq_eq,blochNormSq,dotProduct_comm] using hh

theorem estimate_normalEquation (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    (pathState loss ridge refresh n path).gram.mulVec (estimate loss ridge refresh n path) =
      (pathState loss ridge refresh n path).rhs := by
  have hp : (pathState loss ridge refresh n path).gram.PosDef := by
    rw [pathState_gram]
    exact ridge_posDef ridge hr _ n
  rw [estimate,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne'),
    Matrix.one_mulVec]

end
end QubitOracle.AdaptiveDesign.P1Weighted
