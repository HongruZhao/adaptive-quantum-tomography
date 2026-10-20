import QubitOracle.AdaptiveDesign.PureChartDomain
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.OneQubitBlochPhysicalState
import QubitOracle.Paper.PureMultilevelDeterministicGeometryClosed
import QubitOracle.Paper.PureMultilevelMatrixTraceDistance
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.Paper.QuantumDistances
import QubitOracle.Paper.QubitFoundations
/-! Exact bridges from positive-matrix-square-root fidelity to the scalar
qubit and pure-state formulas used by the statistical endpoints. -/
namespace QubitOracle.AdaptiveDesign.QuantumFidelityBridges
open QubitOracle QubitOracle.Paper Matrix
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem trace_sq_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A.trace^2=(A*A).trace+2*A.det := by
  simp [Matrix.trace,Matrix.mul_apply,Matrix.det_fin_two,Fin.sum_univ_two]
  ring

theorem sqrt_trace_sq_two (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    (Matrix.trace (CFC.sqrt A)).re^2=A.trace.re+2*Real.sqrt A.det.re := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hS2 : S*S=A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have htr : S.trace.im=0 := (Complex.nonneg_iff.mp hS.trace_nonneg).2.symm
  have hd : S.det.im=0 := (Complex.nonneg_iff.mp hS.det_nonneg).2.symm
  have hdp : 0 ≤ S.det.re := (Complex.nonneg_iff.mp hS.det_nonneg).1
  have hdet : S.det.re^2=A.det.re := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det.re) hS2
    simpa [Matrix.det_mul,Complex.mul_re,hd,pow_two] using hh
  have hsqrt : Real.sqrt A.det.re=S.det.re := by
    rw [← hdet,Real.sqrt_sq hdp]
  have hh := congrArg Complex.re (trace_sq_two S)
  rw [hS2] at hh
  simpa [pow_two,htr,hsqrt,Complex.mul_re,S] using hh

theorem qubit_fidelity_trace_det (rho sigma : FiniteDensityMatrix (Fin 2)) :
    quantumFidelity rho sigma = (rho.val*sigma.val).trace.re+
      2*Real.sqrt (rho.val.det.re*sigma.val.det.re) := by
  let S := CFC.sqrt rho.val
  have hS : S.PosSemidef := (CFC.sqrt_nonneg rho.val).posSemidef
  have hS2 : S*S=rho.val := CFC.sqrt_mul_sqrt_self rho.val rho.pos.nonneg
  have hM : (S*sigma.val*S).PosSemidef := by
    simpa only [hS.isHermitian.eq] using sigma.pos.mul_mul_conjTranspose_same S
  have ht : (S*sigma.val*S).trace=(rho.val*sigma.val).trace := by
    rw [Matrix.trace_mul_cycle,hS2]
  have hd : (S*sigma.val*S).det=rho.val.det*sigma.val.det := by
    have hh := congrArg Matrix.det hS2
    simp only [Matrix.det_mul] at hh ⊢
    rw [← hh]
    ring
  have hr : rho.val.det.im=0 := (Complex.nonneg_iff.mp rho.pos.det_nonneg).2.symm
  have hs : sigma.val.det.im=0 := (Complex.nonneg_iff.mp sigma.pos.det_nonneg).2.symm
  change (Matrix.trace (CFC.sqrt (S*sigma.val*S))).re^2 = _
  rw [sqrt_trace_sq_two _ hM,ht,hd,Complex.mul_re,hr,hs]
  ring_nf

theorem qubit_det (theta : Fin 3 → ℝ) :
    (qubitDensityMatrix theta).det=((1-blochNormSq theta)/4:ℝ) := by
  simp [qubitDensityMatrix,pauliLinear,Matrix.det_fin_two,blochNormSq,Fin.sum_univ_succ]
  apply Complex.ext <;> simp [pow_two,Complex.mul_re,Complex.mul_im] <;> ring

theorem qubit_product_trace (theta eta : Fin 3 → ℝ) :
    (qubitDensityMatrix theta*qubitDensityMatrix eta).trace=((1+blochDot theta eta)/2:ℝ) := by
  simp [qubitDensityMatrix,pauliLinear,Matrix.trace,Matrix.mul_apply,blochDot,Fin.sum_univ_succ]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

theorem qubit_fidelity_bloch (theta eta : Fin 3 → ℝ)
    (htheta : blochNormSq theta ≤ 1) (heta : blochNormSq eta ≤ 1) :
    quantumFidelity (blochFiniteDensityMatrix theta htheta) (blochFiniteDensityMatrix eta heta) =
      (1+blochDot theta eta+Real.sqrt (1-blochNormSq theta)*Real.sqrt (1-blochNormSq eta))/2 := by
  rw [qubit_fidelity_trace_det]
  change (qubitDensityMatrix theta*qubitDensityMatrix eta).trace.re+
    2*Real.sqrt ((qubitDensityMatrix theta).det.re*(qubitDensityMatrix eta).det.re)=_
  rw [qubit_product_trace,qubit_det,qubit_det]
  simp only [Complex.ofReal_re]
  have he : ((1-blochNormSq theta)/4)*((1-blochNormSq eta)/4) =
      ((1-blochNormSq theta)*(1-blochNormSq eta))/16 := by ring
  rw [he,Real.sqrt_div (mul_nonneg (by linarith) (by linarith)),
    Real.sqrt_mul (by linarith : 0 ≤ 1-blochNormSq theta)]
  norm_num
  ring

open PureMultilevelDeterministicGeometry PureMultilevelMatrixTraceDistance

theorem rankOne_mul_self {n : ℕ} (h : Fin (n+1) → ℂ) (hh : pureStateNormSq h=1) :
    rankOneDensity h*rankOneDensity h=rankOneDensity h := by
  ext i j
  have hn : (∑ k, star (h k)*h k)=(1:ℂ) := by
    rw [← show (pureStateNormSq h:ℂ)=∑ k, star (h k)*h k by
      simp [pureStateNormSq,Complex.normSq_eq_conj_mul_self]]
    simp [hh]
  change (∑ k, (h i*star (h k))*(h k*star (h j)))=h i*star (h j)
  calc
    _ = h i*(∑ k, star (h k)*h k)*star (h j) := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hn,mul_one]

theorem rankOne_sqrt {n : ℕ} (h : Fin (n+1) → ℂ) (hh : pureStateNormSq h=1) :
    CFC.sqrt (rankOneDensity h)=rankOneDensity h :=
  CFC.sqrt_unique (rankOne_mul_self h hh) (normalizedPureDensityMatrix h hh).pos.nonneg

theorem pure_fidelity {n : ℕ} (h g : Fin (n+1) → ℂ)
    (hh : pureStateNormSq h=1) (hg : pureStateNormSq g=1) :
    quantumFidelity (normalizedPureDensityMatrix h hh) (normalizedPureDensityMatrix g hg)=
      pureMultilevelFidelity h g := by
  let f := pureMultilevelFidelity h g
  have hf : 0 ≤ f := Complex.normSq_nonneg _
  have hs : CFC.sqrt (f • rankOneDensity h)=Real.sqrt f • rankOneDensity h := by
    apply CFC.sqrt_unique
    · rw [smul_mul_smul,rankOne_mul_self h hh]
      rw [Real.mul_self_sqrt hf]
    · exact smul_nonneg (Real.sqrt_nonneg _) (normalizedPureDensityMatrix h hh).pos.nonneg
  change (Matrix.trace (CFC.sqrt
    (CFC.sqrt (rankOneDensity h)*rankOneDensity g*CFC.sqrt (rankOneDensity h)))).re^2=f
  rw [rankOne_sqrt h hh,rankOneDensity_sandwich_fidelity]
  have hc : (pureMultilevelFidelity h g:ℂ) • rankOneDensity h=f • rankOneDensity h := by
    ext i j
    simp [f,Matrix.smul_apply]
  rw [hc,hs,Matrix.trace_smul,rankOneDensity_trace_eq_one h hh]
  simp [Real.sq_sqrt hf]

theorem pure_bures {n : ℕ} (h g : Fin (n+1) → ℂ)
    (hh : pureStateNormSq h=1) (hg : pureStateNormSq g=1) :
    quantumBuresDistanceSq (normalizedPureDensityMatrix h hh) (normalizedPureDensityMatrix g hg)=
      pureMultilevelBuresSq h g := by
  simp [quantumBuresDistanceSq,pure_fidelity,pureMultilevelBuresSq,pureMultilevelRootFidelity]

end
end QubitOracle.AdaptiveDesign.QuantumFidelityBridges
