import Mathlib
import QubitOracle.Paper.ReferenceReflection

/-! Finite coordinate elimination for real orthogonal operations.
The operations act on at most two coordinate levels; determinant-one
operations are real plane rotations, and coordinate reflections are signs.
-/
namespace QubitOracle.Paper.RealTwoLevelElimination
open Submodule
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev E (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι
abbrev G (ι : Type*) [Fintype ι] := E ι ≃ₗᵢ[ℝ] E ι
def axis (i : ι) : E ι := EuclideanSpace.single i 1
def reflect (v : E ι) : G ι := (ℝ ∙ v)ᗮ.reflection

def TwoLevelReflection (g : G ι) : Prop :=
  ∃ i j : ι, ∃ v : E ι, (∀ k, k ≠ i → k ≠ j → v k = 0) ∧ g = reflect v

theorem reflect_fixed {v x : E ι} (h : inner ℝ v x = 0) : reflect v x = x := by
  apply reflection_mem_subspace_eq_self
  exact (mem_orthogonal_singleton_iff_inner_left).mpr (by simpa only [real_inner_comm] using h)

theorem reflect_fix_axis {v : E ι} {k : ι} (h : v k = 0) : reflect v (axis k) = axis k := by
  apply reflect_fixed
  simpa [axis, EuclideanSpace.inner_single_right] using h

theorem eliminate_pair (x : E ι) (i j : ι) (hij : i ≠ j) :
    ∃ g : G ι, TwoLevelReflection g ∧ (g x) j = 0 ∧
      ∀ k, k ≠ i → k ≠ j → (g x) k = x k := by
  let p : E ι := x i • axis i + x j • axis j
  let q : E ι := ‖p‖ • axis i
  let v := p-q
  let g := reflect v
  have ha : ‖axis i‖ = 1 := by simp [axis]
  have he : ‖p‖ = ‖q‖ := by simp [q, norm_smul, ha, abs_of_nonneg (norm_nonneg p)]
  have hg : g p = q := reflection_sub he
  have hv (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : v k = 0 := by
    simp [v,p,q,axis,PiLp.single_apply,hki,hkj]
  have hx : inner ℝ v (x-p) = 0 := by
    simp only [v,p,q,inner_sub_left,inner_add_left,inner_smul_left,
      EuclideanSpace.inner_single_left, axis, inner_sub_right]
    simp [p,axis,PiLp.single_apply,hij,Ne.symm hij]
  have hrest : g (x-p) = x-p := reflect_fixed hx
  have hwhole : g x = q+(x-p) := by
    calc g x = g (p+(x-p)) := by congr 1; abel
         _ = q+(x-p) := by rw [map_add,hg,hrest]
  refine ⟨g,⟨i,j,v,hv,rfl⟩,?_,?_⟩
  · rw [hwhole]
    simp [p,q,axis,PiLp.single_apply,hij,Ne.symm hij]
  · intro k hki hkj
    rw [hwhole]
    simp [p,q,axis,PiLp.single_apply,hki,hkj]

theorem align_supported (i : ι) (s : Finset ι) (hi : i ∉ s)
    (x : E ι) (hx : ∀ k, k ≠ i → k ∉ s → x k = 0) :
    ∃ l : List (G ι), (∀ g ∈ l, TwoLevelReflection g) ∧
      ∃ a : ℝ, l.prod x = a • axis i := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    refine ⟨[],by simp, x i, ?_⟩
    ext k
    by_cases hk : k=i
    · subst k; simp [axis,PiLp.single_apply]
    · simp [axis,PiLp.single_apply,hk,hx k hk (by simp)]
  | @insert j s hjs ih =>
    have hji : j ≠ i := by intro h; subst j; exact hi (Finset.mem_insert_self _ _)
    obtain ⟨g,hg,hzero,hother⟩ := eliminate_pair x i j (Ne.symm hji)
    have hsupport : ∀ k, k ≠ i → k ∉ s → (g x) k = 0 := by
      intro k hki hks
      by_cases hkj : k=j
      · subst k; exact hzero
      · rw [hother k hki hkj]
        exact hx k hki (by simp [hkj,hks])
    obtain ⟨l,hl,a,ha⟩ := ih (by aesop) (g x) hsupport
    refine ⟨l++[g],?_,a,?_⟩
    · intro f hf
      rcases List.mem_append.mp hf with hf|hf
      · exact hl f hf
      · have he : f = g := by simpa using hf
        simpa only [he] using hg
    · simpa [List.prod_append] using ha

theorem coordinate_alignment (i : ι) (x : E ι) :
    ∃ l : List (G ι), (∀ g ∈ l, TwoLevelReflection g) ∧
      ∃ a : ℝ, l.prod x = a • axis i := by
  apply align_supported i (Finset.univ.erase i) (by simp) x
  intro k hki hk
  exact False.elim (hk (by simp [hki]))

def orientation (g : G ι) : ℝˣ := LinearEquiv.det g.toLinearEquiv
theorem orientation_mul (g h : G ι) : orientation (g*h) = orientation g * orientation h :=
  map_mul LinearEquiv.det _ _
theorem orientation_inv (g : G ι) : orientation g⁻¹ = (orientation g)⁻¹ :=
  map_inv LinearEquiv.det _

def PlaneRotation (g : G ι) : Prop :=
  ∃ i j : ι, (∀ k, k ≠ i → k ≠ j → g (axis k) = axis k) ∧ orientation g = 1
def SignChange (g : G ι) : Prop := ∃ i : ι, g = reflect (axis i)
def ElementaryGate (g : G ι) : Prop := PlaneRotation g ∨ SignChange g

theorem reflect_orientation {v : E ι} (hv : v ≠ 0) : orientation (reflect v) = -1 := by
  change (ℝ ∙ v)ᗮ.reflection.det = -1
  rw [Submodule.linearEquiv_det_reflection,Submodule.orthogonal_orthogonal,
    finrank_span_singleton hv,pow_one]

theorem axis_ne_zero (i : ι) : axis i ≠ 0 := by
  intro he
  have h := congrArg (fun v : E ι => v i) he
  norm_num [axis] at h

theorem twoLevel_gate_word {g : G ι} (hg : TwoLevelReflection g) :
    ∃ l : List (G ι), (∀ f ∈ l, ElementaryGate f) ∧ g = l.prod := by
  obtain ⟨i,j,v,hv,rfl⟩ := hg
  by_cases hzero : v=0
  · refine ⟨[],by simp,?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    apply reflection_mem_subspace_eq_self
    simp [hzero]
  · let s := reflect (axis i)
    let r := reflect v * s
    have hs : orientation s = -1 := reflect_orientation (axis_ne_zero i)
    have hr : PlaneRotation r := by
      refine ⟨i,j,?_,?_⟩
      · intro k hki hkj
        change reflect v (s (axis k)) = axis k
        have hsign : s (axis k) = axis k := by
          apply reflect_fix_axis
          simp [axis,Ne.symm hki]
        rw [hsign]
        exact reflect_fix_axis (hv k hki hkj)
      · dsimp only [r]
        rw [orientation_mul,reflect_orientation hzero,hs]
        simp
    refine ⟨[r,s],?_,?_⟩
    · intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl
      · exact Or.inl hr
      · exact Or.inr ⟨i,rfl⟩
    · simp [r,s,reflect, mul_assoc]

theorem elementary_inverse {g : G ι} (hg : ElementaryGate g) : ElementaryGate g⁻¹ := by
  rcases hg with ⟨i,j,hfix,hdet⟩ | ⟨i,rfl⟩
  · left
    refine ⟨i,j,?_,?_⟩
    · intro k hki hkj
      apply g.injective
      change g (g.symm (axis k)) = g (axis k)
      simpa only [g.apply_symm_apply] using (hfix k hki hkj).symm
    · rw [orientation_inv,hdet,inv_one]
  · right
    exact ⟨i,by simp [reflect]⟩

def gateWords : Subgroup (G ι) where
  carrier := {g | ∃ l : List (G ι), (∀ f ∈ l, ElementaryGate f) ∧ g = l.prod}
  one_mem' := ⟨[],by simp,by simp⟩
  mul_mem' := by
    rintro g h ⟨l,hl,rfl⟩ ⟨m,hm,rfl⟩
    refine ⟨l++m,?_,by simp⟩
    intro f hf
    rcases List.mem_append.mp hf with hf|hf
    · exact hl f hf
    · exact hm f hf
  inv_mem' := by
    rintro g ⟨l,hl,rfl⟩
    refine ⟨(l.map Inv.inv).reverse,?_,?_⟩
    · intro f hf
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
      exact elementary_inverse (hl h hh)
    · exact List.prod_inv_reverse l

theorem twoLevel_in_gateWords {g : G ι} (hg : TwoLevelReflection g) : g ∈ gateWords :=
  twoLevel_gate_word hg

theorem reflection_in_gateWords (i : ι) (v : E ι) : reflect v ∈ gateWords := by
  by_cases hv : v=0
  · have he : reflect v = 1 := by
      apply LinearIsometryEquiv.ext
      intro x
      apply reflection_mem_subspace_eq_self
      simp [hv]
    rw [he]; exact gateWords.one_mem
  obtain ⟨l,hl,a,ha⟩ := coordinate_alignment i v
  let g := l.prod
  have hg : g ∈ gateWords := gateWords.list_prod_mem (fun f hf => twoLevel_in_gateWords (hl f hf))
  have hnonzero : a ≠ 0 := by
    intro he
    have hgv : g v=0 := by simpa [g,he] using ha
    exact hv (g.injective (by simpa using hgv))
  have hmap : ((ℝ ∙ v)ᗮ).map (g.toLinearEquiv : E ι →ₗ[ℝ] E ι) = (ℝ ∙ axis i)ᗮ := by
    rw [Submodule.map_orthogonal_equiv,Submodule.map_span,Set.image_singleton]
    change (ℝ ∙ g v)ᗮ = _
    rw [show g v=a • axis i from ha,span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hnonzero)]
  have hconj : reflect v = g⁻¹ * reflect (axis i) * g := by
    have he := Submodule.reflection_map g ((ℝ ∙ v)ᗮ)
    have he' : reflect (axis i) = g.symm.trans ((reflect v).trans g) := by
      simpa only [hmap,reflect] using he
    apply LinearIsometryEquiv.ext
    intro x
    change reflect v x = g.symm (reflect (axis i) (g x))
    rw [he']
    simp
  rw [hconj]
  apply gateWords.mul_mem (gateWords.mul_mem (gateWords.inv_mem hg) ?_) hg
  exact twoLevel_in_gateWords ⟨i,i,axis i,(by intro k hki _; simp [axis,hki]),rfl⟩

theorem orthogonal_finite_gate_decomposition [Nonempty ι] (g : G ι) :
    ∃ l : List (G ι), (∀ f ∈ l, ElementaryGate f) ∧ g = l.prod := by
  obtain ⟨l,_,rfl⟩ := g.reflections_generate_dim
  exact gateWords.list_prod_mem (by
    intro f hf
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hf
    exact reflection_in_gateWords (Classical.arbitrary ι) v)

def realNormal (u : ι → ℂ) : E ι := WithLp.toLp 2 (fun k => (u k).re)

theorem realNormal_norm_sq (u : ι → ℂ) (hu : ∀ k, (u k).im=0) :
    ‖realNormal u‖^2 = QubitOracle.Paper.pureStateNormSq u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold QubitOracle.Paper.pureStateNormSq
  apply Finset.sum_congr rfl
  intro k _
  simp [realNormal,Complex.normSq_apply,hu k,pow_two]

theorem real_reflection_matrix_apply (u : ι → ℂ) (hu : ∀ k, (u k).im=0) (x : E ι) :
    (QubitOracle.Paper.ElementaryReferenceAlgebra.reflection u).mulVec (fun k => (x k : ℂ)) =
      fun k => ((reflect (realNormal u) x) k : ℂ) := by
  have hreal (k : ι) : u k = ((u k).re : ℂ) := by
    apply Complex.ext <;> simp [hu k]
  have hf (k : ι) : (reflect (realNormal u) x) k =
      x k - 2/(‖realNormal u‖^2) * (∑ j, (u j).re*x j) * (u k).re := by
    rw [reflect,Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
    simp only [PiLp.neg_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
      PiLp.inner_apply,RCLike.inner_apply,realNormal,star_trivial]
    simp only [starRingEnd_apply,star_trivial,mul_comm]
    simp only [two_smul,RCLike.ofReal_real_eq_id,id_eq]
    ring
  have ham : QubitOracle.Paper.basisBornAmplitude u (fun k => (x k : ℂ)) =
      ((∑ j, (u j).re*x j) : ℂ) := by
    apply Complex.ext <;>
      simp [QubitOracle.Paper.basisBornAmplitude,Complex.mul_re,Complex.mul_im,
        Complex.star_def,hu]
  rw [QubitOracle.Paper.ElementaryReferenceAlgebra.reflection,
    Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
    QubitOracle.Paper.ProjectiveStateGeometry.density_mulVec]
  funext k
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hf]
  rw [ham,← realNormal_norm_sq u hu,hreal k]
  push_cast
  simp only [Complex.ofReal_re]
  ring

theorem referenceRotation_finite_gate_decomposition (d : ℕ) :
    ∃ l : List (G (Fin (d+1))), (∀ f ∈ l, ElementaryGate f) ∧
      ∀ i j, QubitOracle.Paper.ReferenceReflection.referenceRotation d i j =
        ((l.prod (axis j)) i : ℂ) := by
  let u := QubitOracle.Paper.ReferenceReflection.referenceVector d -
    QubitOracle.AdaptiveDesign.GlobalPFSIC.coordinate 0
  have hu (k : Fin (d+1)) : (u k).im=0 := by
    by_cases hk : k=0 <;>
      simp [u,QubitOracle.Paper.ReferenceReflection.referenceVector_real,
        QubitOracle.AdaptiveDesign.GlobalPFSIC.coordinate,Pi.single_apply,hk]
  obtain ⟨l,hl,he⟩ := orthogonal_finite_gate_decomposition (reflect (realNormal u))
  refine ⟨l,hl,?_⟩
  intro i j
  have h := congrFun (real_reflection_matrix_apply u hu (axis j)) i
  simpa [QubitOracle.Paper.ReferenceReflection.referenceRotation,u,axis,
    Matrix.mulVec,dotProduct,PiLp.single_apply,he,apply_ite] using h

end
end QubitOracle.Paper.RealTwoLevelElimination
