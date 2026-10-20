import QubitOracle.AdaptiveDesign.InformationCoordinateInvariance
import QubitOracle.AdaptiveDesign.PureChartDifferential
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.PureStateFoundations
/-! Intrinsic information, its actual Born derivative, and independence
of the arbitrary kernel part of a pure-state SLD. -/
namespace QubitOracle.AdaptiveDesign.IntrinsicInformationGeometry
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open scoped BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def sldPairing {d : ℕ} (h : PureVector d) (L M : HermitianSpace (d+1)) : ℝ :=
  (Matrix.trace (rankOneDensity h.val * (toMatrix L*toMatrix M+toMatrix M*toMatrix L))).re/2

theorem sldPairing_independent {d : ℕ} (h : PureVector d) (A B : tangentSpace h)
    (L M : HermitianSpace (d+1))
    (hL : rankOneDensity h.val*toMatrix L+toMatrix L*rankOneDensity h.val=(2:ℝ) • toMatrix A.val)
    (hM : rankOneDensity h.val*toMatrix M+toMatrix M*rankOneDensity h.val=(2:ℝ) • toMatrix B.val) :
    sldPairing h L M = 2*⟪A.val,B.val⟫_ℝ := by
  let P := rankOneDensity h.val
  let a := toMatrix A.val
  let b := toMatrix B.val
  let l := toMatrix L
  let m := toMatrix M
  have ha : P*a+a*P=a := (tangentSpace_mem h A.val).mp A.property
  have ht : Matrix.trace (P*(l*m+m*l)) = (4:ℝ) • Matrix.trace (a*b) := by
    calc
      _ = Matrix.trace ((P*l+l*P)*m) := by
        simp only [Matrix.mul_add,Matrix.add_mul,← Matrix.mul_assoc,Matrix.trace_add]
        rw [Matrix.trace_mul_cycle l P m,Matrix.trace_mul_cycle m l P]
      _ = (2:ℝ) • Matrix.trace (a*m) := by
        rw [hL,Matrix.smul_mul,Matrix.trace_smul]
      _ = (2:ℝ) • Matrix.trace ((P*a+a*P)*m) := by rw [ha]
      _ = (2:ℝ) • Matrix.trace (a*(P*m+m*P)) := by
        simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_assoc,Matrix.trace_add]
        rw [Matrix.trace_mul_cycle P a m,Matrix.trace_mul_cycle m P a]
        congr 1
        ring
      _ = _ := by rw [hM,Matrix.mul_smul,Matrix.trace_smul,smul_smul]; norm_num; rfl
  rw [sldPairing]
  change (Matrix.trace (P*(l*m+m*l))).re/2 = _
  rw [ht,inner_eq_trace,Matrix.trace_mul_comm (toMatrix B.val)]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  dsimp only [a,b]
  ring

def fisherForm {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d)
    (A B : HermitianSpace (d+1)) : ℝ :=
  ∑ y, (⟪GeneralPOVM.responseVector P U y,A⟫_ℝ * ⟪GeneralPOVM.responseVector P U y,B⟫_ℝ)/
    GeneralPOVM.bornProbability P truth U y

theorem fisherForm_symmetric {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d)
    (A B : HermitianSpace (d+1)) : fisherForm P truth U A B=fisherForm P truth U B A := by
  simp only [fisherForm,mul_comm]

theorem fisherForm_nonnegative {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d)
    (A : HermitianSpace (d+1)) : 0 ≤ fisherForm P truth U A A := by
  unfold fisherForm
  apply Finset.sum_nonneg
  intro y _
  exact div_nonneg (mul_self_nonneg _) (GeneralPOVM.bornProbability_nonnegative P truth U y)

theorem born_hasFDerivAt {d : ℕ} {O : Type} [Fintype O] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : FinitePOVM (Fin (d+1)) O) (U : GlobalPFSICBorn.Action d) (y : O)
    (chart : V → HermitianSpace (d+1)) (x : V) (D : V →L[ℝ] HermitianSpace (d+1))
    (hD : HasFDerivAt chart D x) :
    HasFDerivAt (fun z => ⟪GeneralPOVM.responseVector P U y,chart z⟫_ℝ)
      ((innerSL ℝ (GeneralPOVM.responseVector P U y)).comp D) x := by
  exact (innerSL ℝ (GeneralPOVM.responseVector P U y)).hasFDerivAt.comp x hD

/-- Pulling back the intrinsic form along a chart derivative gives
exactly the usual probability-derivative formula. Division by zero is
zero, as in the manuscript's positive-support convention. -/
theorem fisherForm_chart {d : ℕ} {O : Type} [Fintype O] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d)
    (chart : V → HermitianSpace (d+1)) (x : V) (D : V →L[ℝ] HermitianSpace (d+1))
    (hD : HasFDerivAt chart D x) (u v : V) :
    fisherForm P truth U (D u) (D v) = ∑ y,
      (fderiv ℝ (fun z => ⟪GeneralPOVM.responseVector P U y,chart z⟫_ℝ) x u *
       fderiv ℝ (fun z => ⟪GeneralPOVM.responseVector P U y,chart z⟫_ℝ) x v)/
      GeneralPOVM.bornProbability P truth U y := by
  simp only [fisherForm,(born_hasFDerivAt P U _ chart x D hD).fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

def fisherBilin {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d) :
    LinearMap.BilinForm ℝ (HermitianSpace (d+1)) where
  toFun A :=
    { toFun := fisherForm P truth U A
      map_add' B C := by simp [fisherForm,inner_add_right,mul_add,add_div,Finset.sum_add_distrib]
      map_smul' c B := by
        simp only [fisherForm,inner_smul_right,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro y _
        ring }
  map_add' A B := by
    ext C
    simp [fisherForm,inner_add_right,add_mul,add_div,Finset.sum_add_distrib]
  map_smul' c A := by
    ext B
    change fisherForm P truth U (c • A) B = c * fisherForm P truth U A B
    simp only [fisherForm,inner_smul_right,smul_eq_mul,Finset.mul_sum,
      LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro y _
    ring

theorem bilinear_coordinate_congruence {V : Type*} [AddCommGroup V] [Module ℝ V]
    {I J : Type*} [Fintype I] [Fintype J]
    (B : LinearMap.BilinForm ℝ V) (v : I → V) (A : Matrix I J ℝ) :
    LinearMap.BilinForm.toMatrixAux (fun j => ∑ i, A i j • v i) B =
      A.transpose * LinearMap.BilinForm.toMatrixAux v B * A := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrixAux_apply,map_sum,map_smul,LinearMap.sum_apply,
    LinearMap.smul_apply,smul_eq_mul,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem fisher_coordinate_congruence {d : ℕ} {O : Type} [Fintype O]
    {I J : Type*} [Fintype I] [Fintype J]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d)
    (v : I → HermitianSpace (d+1)) (A : Matrix I J ℝ) :
    (fun i j => fisherForm P truth U (∑ k, A k i • v k) (∑ k, A k j • v k)) =
      A.transpose * (show Matrix I I ℝ from fun i j => fisherForm P truth U (v i) (v j)) * A :=
  bilinear_coordinate_congruence (fisherBilin P truth U) v A

/-- The chain rule supplies the tangent vectors used in the congruence;
the transition map is an actual differentiable function. -/
theorem chart_transition_derivative {d : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (chart : V → HermitianSpace (d+1)) (transition : W → V) (x : W)
    (D : V →L[ℝ] HermitianSpace (d+1)) (J : W →L[ℝ] V)
    (hD : HasFDerivAt chart D (transition x)) (hJ : HasFDerivAt transition J x) :
    HasFDerivAt (chart ∘ transition) (D.comp J) x := hD.comp x hJ

end
end QubitOracle.AdaptiveDesign.IntrinsicInformationGeometry
