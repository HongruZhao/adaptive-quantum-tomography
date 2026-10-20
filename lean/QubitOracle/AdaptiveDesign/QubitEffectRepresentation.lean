import QubitOracle.FiniteGillMassar
import QubitOracle.AdaptiveDesign.PhysicalModelCharacterization

/-! Bloch effect coordinates derived from arbitrary positive qubit effects,
including zero effects. Completeness is proved from the actual matrix sum. -/
namespace QubitOracle.AdaptiveDesign.QubitEffectRepresentation
open QubitOracle.Paper
open scoped BigOperators ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def weight (E : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((E 0 0).re+(E 1 1).re)/2
def vector (E : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![(E 0 1).re,-(E 0 1).im,((E 0 0).re-(E 1 1).re)/2]

theorem reconstruction (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.IsHermitian) :
    E=weight E • (1:Matrix (Fin 2) (Fin 2) ℂ)+pauliLinear (vector E) := by
  have h00 := congrArg Complex.im (hE.apply 0 0)
  have h11 := congrArg Complex.im (hE.apply 1 1)
  have h10r := congrArg Complex.re (hE.apply 1 0)
  have h10i := congrArg Complex.im (hE.apply 1 0)
  simp at h00 h11 h10r h10i
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [weight,vector,pauliLinear,Matrix.one_apply,Matrix.add_apply] <;> linarith

theorem weight_nonneg (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef) :
    0≤weight E := by
  have h0 := (Complex.nonneg_iff.mp (hE.diag_nonneg (i:=0))).1
  have h1 := (Complex.nonneg_iff.mp (hE.diag_nonneg (i:=1))).1
  dsimp [weight]
  positivity

theorem vector_bound (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef) :
    blochNormSq (vector E)≤weight E^2 := by
  have h := psd_entry_normSq_le_diag_mul_diag E hE 0 1
  simp only [Complex.normSq_apply] at h
  simp [vector,weight,blochNormSq,Fin.sum_univ_succ]
  nlinarith

theorem weight_positive (E : Matrix (Fin 2) (Fin 2) ℂ) (hE : E.PosSemidef)
    (hne : E≠0) : 0<weight E := by
  have hn := weight_nonneg E hE
  apply lt_of_le_of_ne hn
  intro hz
  have htr : Matrix.trace E=0 := by
    have hdiag := (Complex.nonneg_iff.mp hE.trace_nonneg).2
    apply Complex.ext
    · simpa [weight,Matrix.trace,Fin.sum_univ_two] using congrArg (fun x : ℝ => 2*x) hz.symm
    · simpa using hdiag.symm
  exact hne ((hE.trace_eq_zero_iff).mp htr)

variable {O : Type} [Fintype O]

def ofPOVM (P : FinitePOVM (Fin 2) O) : QubitBlochPOVM O where
  weight y := weight (P.effect y)
  vector y := vector (P.effect y)
  weight_nonneg y := weight_nonneg _ (P.positive y)
  vector_normSq_le y := vector_bound _ (P.positive y)
  sum_weight := by
    have h0 := congrArg (fun E : Matrix (Fin 2) (Fin 2) ℂ => (E 0 0).re) P.complete
    have h1 := congrArg (fun E : Matrix (Fin 2) (Fin 2) ℂ => (E 1 1).re) P.complete
    simp only [Matrix.sum_apply,Complex.re_sum,Matrix.one_apply,ite_true,Complex.one_re] at h0 h1
    simp only [weight]
    rw [← Finset.sum_div,Finset.sum_add_distrib,h0,h1]
    norm_num
  sum_vector i := by
    have h0 := congrArg (fun E : Matrix (Fin 2) (Fin 2) ℂ => (E 0 0).re) P.complete
    have h1 := congrArg (fun E : Matrix (Fin 2) (Fin 2) ℂ => (E 1 1).re) P.complete
    have h01r := congrArg (fun E : Matrix (Fin 2) (Fin 2) ℂ => (E 0 1).re) P.complete
    have h01i := congrArg (fun E : Matrix (Fin 2) (Fin 2) ℂ => (E 0 1).im) P.complete
    simp only [Matrix.sum_apply,Complex.re_sum,Complex.im_sum,Matrix.one_apply,
      ite_true,Complex.one_re] at h0 h1 h01r h01i
    fin_cases i <;> simp [vector,← Finset.sum_div,Finset.sum_sub_distrib,h0,h1,h01r,h01i]

theorem effect_reconstruction (P : FinitePOVM (Fin 2) O) (y : O) :
    P.effect y=(ofPOVM P).weight y • (1:Matrix (Fin 2) (Fin 2) ℂ)+
      pauliLinear ((ofPOVM P).vector y) := reconstruction _ (P.positive y).isHermitian

theorem probability_is_born (P : FinitePOVM (Fin 2) O) (r : Fin 3 → ℝ) (y : O) :
    qubitProbability r (ofPOVM P) y=(Matrix.trace (P.effect y*qubitDensityMatrix r)).re := by
  conv_rhs => rw [effect_reconstruction P y]
  simp [qubitProbability,blochDot,qubitDensityMatrix,pauliLinear,Matrix.trace,
    Matrix.mul_apply,Fin.sum_univ_two,Fin.sum_univ_succ,Matrix.one_apply,
    Complex.mul_re,Complex.mul_im]
  ring

theorem all_qubit_gillMassar (P : FinitePOVM (Fin 2) O) (r : Fin 3 → ℝ)
    (hr : blochNormSq r<1) :
    Matrix.trace (qubitSLDFisherInv r*qubitClassicalFisher r (ofPOVM P))≤1 := by
  exact qubit_interior_gillMassar r (ofPOVM P) hr

def normalizedVector (E : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  (weight E)⁻¹ • vector E

theorem scaled_normalized (E : Matrix (Fin 2) (Fin 2) ℂ) (hw : weight E≠0) :
    weight E • normalizedVector E=vector E := by
  rw [normalizedVector,smul_smul,mul_inv_cancel₀ hw,one_smul]

theorem normalized_vector_bound (E : Matrix (Fin 2) (Fin 2) ℂ)
    (hE : E.PosSemidef) (hne : E≠0) : blochNormSq (normalizedVector E)≤1 := by
  have hw := weight_positive E hE hne
  simp only [normalizedVector,blochNormSq,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  calc
    _ ≤ (weight E)⁻¹^2*(weight E)^2 :=
      mul_le_mul_of_nonneg_left (vector_bound E hE) (sq_nonneg _)
    _ = 1 := by field_simp

theorem pauliLinear_real_smul (c : ℝ) (v : Fin 3 → ℝ) :
    pauliLinear (c • v)=c • pauliLinear v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliLinear,Pi.smul_apply,smul_eq_mul] <;> ring

theorem normalized_reconstruction (E : Matrix (Fin 2) (Fin 2) ℂ)
    (hE : E.PosSemidef) (hne : E≠0) :
    E=weight E • (1+pauliLinear (normalizedVector E)) := by
  rw [smul_add,← pauliLinear_real_smul,scaled_normalized E (weight_positive E hE hne).ne']
  exact reconstruction E hE.isHermitian

/-- All constraints in the supplement's normalized effect representation
follow from positivity and completeness, not additional POVM hypotheses. -/
theorem normalizedPOVM_constraints (P : FinitePOVM (Fin 2) O)
    (hne : ∀ y, P.effect y≠0) :
    (∀ y, 0<weight (P.effect y)) ∧
    (∀ y, blochNormSq (normalizedVector (P.effect y))≤1) ∧
    (∑ y, weight (P.effect y))=1 ∧
    (∀ i, ∑ y, weight (P.effect y)*normalizedVector (P.effect y) i=0) ∧
    (∀ y, P.effect y=weight (P.effect y) • (1+pauliLinear (normalizedVector (P.effect y)))) := by
  refine ⟨fun y => weight_positive _ (P.positive y) (hne y),
    fun y => normalized_vector_bound _ (P.positive y) (hne y),
    (ofPOVM P).sum_weight,?_,fun y => normalized_reconstruction _ (P.positive y) (hne y)⟩
  intro i
  calc
    _ = ∑ y, vector (P.effect y) i := by
      apply Finset.sum_congr rfl
      intro y hy
      exact congrFun (scaled_normalized _ (weight_positive _ (P.positive y) (hne y)).ne') i
    _ = 0 := (ofPOVM P).sum_vector i

end
end QubitOracle.AdaptiveDesign.QubitEffectRepresentation
