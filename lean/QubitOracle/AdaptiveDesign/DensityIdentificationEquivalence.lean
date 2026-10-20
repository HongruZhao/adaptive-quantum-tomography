import QubitOracle.AdaptiveDesign.ReferenceIdentificationSpanning
import QubitOracle.AdaptiveDesign.PhysicalModelCharacterization

/-! The printed equivalence between C1 and identification of every
density matrix. The reverse implication constructs two physical density
matrices from a nonzero invisible Hermitian direction. -/
namespace QubitOracle.AdaptiveDesign.DensityIdentificationEquivalence
open QubitOracle QubitOracle.Paper GeneralPOVM GlobalPFSICHermitian
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

theorem hermitian_positive_shift {d : ℕ} (A : HermitianSpace (d+1)) :
    ∃ c : ℝ, 0 < c ∧ (toMatrix A + (c:ℂ) • 1).PosSemidef := by
  classical
  let hM := toMatrix_isHermitian A
  let c : ℝ := 1 + ∑ i, |hM.eigenvalues i|
  have hc : 0 < c := by dsimp [c]; positivity
  have he (i : Fin (d+1)) : 0 ≤ hM.eigenvalues i + c := by
    have hi := Finset.single_le_sum (fun j _ => abs_nonneg (hM.eigenvalues j))
      (Finset.mem_univ i)
    dsimp [c]
    linarith [neg_abs_le (hM.eigenvalues i)]
  have hd : (Matrix.diagonal (fun i => ((hM.eigenvalues i + c : ℝ):ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr ⟨he i,by simp⟩)
  have hdiag : Matrix.diagonal (fun i => ((hM.eigenvalues i+c:ℝ):ℂ)) =
      Matrix.diagonal (fun i => (hM.eigenvalues i:ℂ)) + (c:ℂ) • 1 := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  have hs : hM.eigenvectorUnitary.val * Matrix.diagonal (fun i => (hM.eigenvalues i:ℂ)) *
      hM.eigenvectorUnitary.val.conjTranspose = toMatrix A := hM.spectral_theorem.symm
  have hu := Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.property
  change hM.eigenvectorUnitary.val * hM.eigenvectorUnitary.val.conjTranspose = 1 at hu
  have hp := hd.mul_mul_conjTranspose_same hM.eigenvectorUnitary.val
  rw [hdiag,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hs,hu] at hp
  exact ⟨c,hc,hp⟩

def densityBorn {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) (ρ : FiniteDensityMatrix (Fin (d+1))) : O → ℂ :=
  fun y => Matrix.trace (ρ.val * F.effect y)

def IdentifiesDensityMatrices {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) : Prop :=
  ∀ ρ σ : FiniteDensityMatrix (Fin (d+1)), densityBorn F ρ = densityBorn F σ → ρ.val = σ.val

theorem identifying_iff_density_injective {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) : Identifying F ↔ IdentifiesDensityMatrices F := by
  constructor
  · intro hF ρ σ h
    let A : HermitianSpace (d+1) := ofMatrix (ρ.val-σ.val) (ρ.pos.isHermitian.sub σ.pos.isHermitian)
    have hz : A=0 := hF A (fun y => by
      have hh := congrArg (fun f : O → ℂ => (f y).re) h
      simpa [inner_eq_trace,A,GeneralPOVM.effectVector,densityBorn,Matrix.sub_mul,Matrix.trace_sub] using
        sub_eq_zero.mpr hh)
    have hm := congrArg toMatrix hz
    exact sub_eq_zero.mp hm
  · intro hF A hA
    have hz (y : O) : Matrix.trace (toMatrix A * F.effect y) = 0 := by
      have hh := congrArg Complex.ofReal (hA y)
      simpa only [complex_inner_eq_trace,GeneralPOVM.effectVector,toMatrix_ofMatrix,Complex.ofReal_zero] using hh
    have ht : Matrix.trace (toMatrix A) = 0 := by
      rw [← Matrix.mul_one (toMatrix A),← F.complete,Matrix.mul_sum,Matrix.trace_sum]
      simp [hz]
    obtain ⟨c,hc,hpos⟩ := hermitian_positive_shift A
    let q : ℝ := (c*(d+1:ℝ))⁻¹
    have hq : 0 < q := by dsimp [q]; positivity
    have hqeq : (q:ℂ)*(c:ℂ)*(d+1:ℂ)=1 := by
      dsimp [q]
      push_cast
      field_simp
    let ρ : FiniteDensityMatrix (Fin (d+1)) :=
      ⟨(q:ℂ) • (toMatrix A + (c:ℂ) • 1),
       hpos.smul (Complex.nonneg_iff.mpr ⟨hq.le,by simp⟩),by
        simp only [Matrix.trace_smul,Matrix.trace_add,ht,zero_add,Matrix.trace_one,
          Fintype.card_fin,smul_eq_mul,Nat.cast_add,Nat.cast_one]
        simpa only [mul_assoc] using hqeq⟩
    let σ : FiniteDensityMatrix (Fin (d+1)) :=
      ⟨((q*c:ℝ):ℂ) • 1,
        Matrix.PosSemidef.one.smul (Complex.nonneg_iff.mpr ⟨mul_nonneg hq.le hc.le,by simp⟩),by
          simpa [Matrix.trace_smul,Matrix.trace_one,smul_eq_mul,mul_assoc] using hqeq⟩
    have he : densityBorn F ρ = densityBorn F σ := by
      funext y
      simp [densityBorn,ρ,σ,Matrix.smul_mul,Matrix.add_mul,Matrix.trace_smul,
        Matrix.trace_add,hz,mul_add,mul_assoc]
    have hm := hF ρ σ he
    have ha : (q:ℂ) • toMatrix A = 0 := by
      change (q:ℂ) • (toMatrix A+(c:ℂ) • 1)=((q*c:ℝ):ℂ) • 1 at hm
      rw [smul_add,smul_smul,Complex.ofReal_mul] at hm
      exact add_right_cancel (hm.trans (zero_add _).symm)
    apply toMatrix_injective
    exact (smul_eq_zero.mp ha).resolve_left (Complex.ofReal_ne_zero.mpr hq.ne')

theorem spanning_iff_density_injective {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) :
    Submodule.span ℝ (Set.range (effectVector F)) = ⊤ ↔ IdentifiesDensityMatrices F :=
  (ReferenceIdentificationSpanning.identifying_iff_span F).symm.trans
    (identifying_iff_density_injective F)

end
end QubitOracle.AdaptiveDesign.DensityIdentificationEquivalence
