import QubitOracle.Paper.OneQubitMixedExactCycleCommonSpaceEmbedding
import Mathlib.Probability.Independence.Integration

/-!
# Closing the common-space conditional-expectation pullback

For a fixed row `n`, the augmented sigma algebra has a finite observation:
all complete coordinates before `n`, together with the current row's prefix
history.  Its fibers are therefore a finite measurable partition.  On each
fiber, `Indep.setIntegral_eq_mul` factors the earlier-row contribution from the
current-coordinate integral.  The remaining current-coordinate equality is
exactly the finite-row conditional-expectation identity.

This closes `CommonSpaceCondExpPullbackAPI.condExp_lift` without an axiom or a
limit theorem.  No Gaussian convergence statement is made here.
-/

open scoped BigOperators ENNReal
open Filter MeasureTheory ProbabilityTheory

namespace QubitOracle.Paper
namespace MixedExactCycleScalarTriangularArrayData

section PullbackClosure

variable (A : ℕ → MixedExactCycleScalarTriangularArrayData)
variable (rowSize : ℕ → ℕ)

attribute [local instance] rowMeasurableSpace rowMeasurableSingletonClass
  historyKeyMeasurableSpace

local instance pullbackHistoryKeyMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass ((A n).HistoryKey (rowSize n)) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-! ## A finite observation generating the augmented sigma algebra -/

/-- Tuple of all complete row coordinates strictly before `n`. -/
abbrev EarlierRowsValue (n : ℕ) :=
  ∀ i : ↥(Finset.range n), CommonRow A rowSize i.1

/-- Projection onto all complete coordinates strictly before `n`. -/
def earlierRowsProjection (n : ℕ) :
    CommonOmega A rowSize → EarlierRowsValue A rowSize n :=
  fun omega i => omega i.1

/-- The earlier-row sigma algebra is exactly the comap of the finite earlier
coordinate tuple. -/
theorem completeEarlierRowsSigma_eq_comap_earlierRowsProjection (n : ℕ) :
    completeEarlierRowsSigma A rowSize n =
      MeasurableSpace.comap (earlierRowsProjection A rowSize n)
        (inferInstance : MeasurableSpace (EarlierRowsValue A rowSize n)) := by
  have hPi :
      MeasurableSpace.comap (earlierRowsProjection A rowSize n)
          (inferInstance : MeasurableSpace (EarlierRowsValue A rowSize n)) =
        ⨆ i : ↥(Finset.range n),
          MeasurableSpace.comap
            (fun omega : CommonOmega A rowSize => omega i.1)
            (⊤ : MeasurableSpace (CommonRow A rowSize i.1)) := by
    simp [rowMeasurableSpace, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, earlierRowsProjection, Function.comp_def]
  rw [completeEarlierRowsSigma, hPi]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    refine le_iSup_of_le
      (⟨j.1, Finset.mem_range.mpr j.2⟩ : ↥(Finset.range n)) ?_
    rfl
  · refine iSup_le fun i => ?_
    refine le_iSup_of_le
      (⟨i.1, Finset.mem_range.mp i.2⟩ : Fin n) ?_
    rfl

/-- Current row history, viewed from the common sample space. -/
def currentHistoryProjection (n k : ℕ) :
    CommonOmega A rowSize → (A n).HistoryKey (rowSize n) :=
  fun omega => (A n).historyProjection (rowSize n) k (omega n)

theorem currentRowPrefixSigma_eq_comap_currentHistory
    (n k : ℕ) :
    currentRowPrefixSigma A rowSize n k =
      MeasurableSpace.comap (currentHistoryProjection A rowSize n k)
        (inferInstance : MeasurableSpace
          ((A n).HistoryKey (rowSize n))) := by
  have hCurrent :
      currentHistoryProjection A rowSize n k =
        (A n).historyProjection (rowSize n) k ∘
          rowCoordinate A rowSize n := by
    rfl
  rw [hCurrent]
  simp [currentRowPrefixSigma, rowFiltrationSigma,
    MeasurableSpace.comap_comp]
  rfl

/-- Finite observation key for the augmented row filtration. -/
abbrev AugmentedHistoryValue (n : ℕ) :=
  EarlierRowsValue A rowSize n × (A n).HistoryKey (rowSize n)

/-- The complete finite observation available at row `n`, time `k`. -/
def augmentedHistoryProjection (n k : ℕ) :
    CommonOmega A rowSize → AugmentedHistoryValue A rowSize n :=
  fun omega =>
    (earlierRowsProjection A rowSize n omega,
      currentHistoryProjection A rowSize n k omega)

/-- The joined augmented sigma algebra is exactly the comap of its finite
observation key. -/
theorem augmentedRowFiltrationSigma_eq_comap_augmentedHistory
    (n k : ℕ) :
    augmentedRowFiltrationSigma A rowSize n k =
      MeasurableSpace.comap (augmentedHistoryProjection A rowSize n k)
        (inferInstance : MeasurableSpace
          (AugmentedHistoryValue A rowSize n)) := by
  have hEarlierSmall :
      Measurable[completeEarlierRowsSigma A rowSize n]
        (earlierRowsProjection A rowSize n) := by
    rw [measurable_iff_comap_le,
      completeEarlierRowsSigma_eq_comap_earlierRowsProjection A]
  have hCurrentSmall :
      Measurable[currentRowPrefixSigma A rowSize n k]
        (currentHistoryProjection A rowSize n k) := by
    rw [measurable_iff_comap_le,
      currentRowPrefixSigma_eq_comap_currentHistory A]
  have hEarlierAugmented :
      Measurable[augmentedRowFiltrationSigma A rowSize n k]
        (earlierRowsProjection A rowSize n) := by
    intro s hs
    exact (show completeEarlierRowsSigma A rowSize n ≤
      augmentedRowFiltrationSigma A rowSize n k from le_sup_left)
      _ (hEarlierSmall hs)
  have hCurrentAugmented :
      Measurable[augmentedRowFiltrationSigma A rowSize n k]
        (currentHistoryProjection A rowSize n k) := by
    intro s hs
    exact (show currentRowPrefixSigma A rowSize n k ≤
      augmentedRowFiltrationSigma A rowSize n k from le_sup_right)
      _ (hCurrentSmall hs)
  have hCombinedAugmented :
      Measurable[augmentedRowFiltrationSigma A rowSize n k]
        (augmentedHistoryProjection A rowSize n k) := by
    exact hEarlierAugmented.prodMk hCurrentAugmented
  have hCombinedComap :
      Measurable[
        MeasurableSpace.comap (augmentedHistoryProjection A rowSize n k)
          (inferInstance : MeasurableSpace
            (AugmentedHistoryValue A rowSize n))]
        (augmentedHistoryProjection A rowSize n k) := by
    rw [measurable_iff_comap_le]
  apply le_antisymm
  · apply sup_le
    · rw [completeEarlierRowsSigma_eq_comap_earlierRowsProjection A]
      exact ((measurable_fst.comp hCombinedComap).comap_le)
    · rw [currentRowPrefixSigma_eq_comap_currentHistory A]
      exact ((measurable_snd.comp hCombinedComap).comap_le)
  · exact hCombinedAugmented.comap_le

/-! ## Independence of the earlier tuple and the current row -/

/-- The finite tuple of earlier coordinates is independent of row coordinate
`n`. -/
theorem earlierRowsProjection_indepFun_rowCoordinate (n : ℕ) :
    IndepFun (earlierRowsProjection A rowSize n)
      (rowCoordinate A rowSize n) (commonMeasure A rowSize) := by
  let rightEval :
      (∀ i : ↥({n} : Finset ℕ), CommonRow A rowSize i.1) →
        CommonRow A rowSize n :=
    fun x => x ⟨n, Finset.mem_singleton_self n⟩
  have hDisjoint :
      Disjoint (Finset.range n) ({n} : Finset ℕ) := by
    simp
  have hFinite :=
    (rowCoordinates_iIndepFun A rowSize).indepFun_finset
      (Finset.range n) ({n} : Finset ℕ) hDisjoint
      (fun i => rowCoordinate_measurable A rowSize i)
  have hRight : Measurable rightEval := by
    exact measurable_pi_apply
      (⟨n, Finset.mem_singleton_self n⟩ : ↥({n} : Finset ℕ))
  have hComposed := hFinite.comp measurable_id hRight
  change IndepFun
    (fun omega : CommonOmega A rowSize =>
      fun i : ↥(Finset.range n) => omega i.1)
    (fun omega : CommonOmega A rowSize => omega n)
    (commonMeasure A rowSize)
  simpa [rightEval, rowCoordinate, Function.comp_def] using hComposed

/-- Sigma-algebra form of the preceding finite-block independence. -/
theorem completeEarlierRowsSigma_indep_currentRow (n : ℕ) :
    Indep (completeEarlierRowsSigma A rowSize n)
      (MeasurableSpace.comap (rowCoordinate A rowSize n)
        (⊤ : MeasurableSpace (CommonRow A rowSize n)))
      (commonMeasure A rowSize) := by
  have h := earlierRowsProjection_indepFun_rowCoordinate A rowSize n
  change Indep
    (MeasurableSpace.comap (earlierRowsProjection A rowSize n)
      (inferInstance : MeasurableSpace (EarlierRowsValue A rowSize n)))
    (MeasurableSpace.comap (rowCoordinate A rowSize n)
      (⊤ : MeasurableSpace (CommonRow A rowSize n)))
    (commonMeasure A rowSize) at h
  simpa [completeEarlierRowsSigma_eq_comap_earlierRowsProjection A
    rowSize n] using h

/-! ## Measurable atoms of the finite observation -/

def earlierRowsAtom (n : ℕ) (value : EarlierRowsValue A rowSize n) :
    Set (CommonOmega A rowSize) :=
  {omega | earlierRowsProjection A rowSize n omega = value}

def currentHistoryFiber (n k : ℕ)
    (key : (A n).HistoryKey (rowSize n)) :
    Set (CommonRow A rowSize n) :=
  {row | (A n).historyProjection (rowSize n) k row = key}

def augmentedHistoryAtom (n k : ℕ)
    (key : AugmentedHistoryValue A rowSize n) :
    Set (CommonOmega A rowSize) :=
  {omega | augmentedHistoryProjection A rowSize n k omega = key}

theorem earlierRowsAtom_measurable (n : ℕ)
    (value : EarlierRowsValue A rowSize n) :
    MeasurableSet[completeEarlierRowsSigma A rowSize n]
      (earlierRowsAtom A rowSize n value) := by
  have hProjection :
      Measurable[completeEarlierRowsSigma A rowSize n]
        (earlierRowsProjection A rowSize n) := by
    rw [measurable_iff_comap_le,
      completeEarlierRowsSigma_eq_comap_earlierRowsProjection A]
  exact hProjection (measurableSet_singleton value)

theorem currentHistoryFiber_measurable (n k : ℕ)
    (key : (A n).HistoryKey (rowSize n)) :
    MeasurableSet[(A n).rowFiltrationSigma (rowSize n) k]
      (currentHistoryFiber A rowSize n k key) := by
  have hProjection :
      Measurable[(A n).rowFiltrationSigma (rowSize n) k]
        ((A n).historyProjection (rowSize n) k) := by
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap
      ((A n).historyProjection (rowSize n) k) ⊤ ≤
        (A n).rowFiltrationSigma (rowSize n) k
    rfl
  exact hProjection (measurableSet_singleton key)

theorem augmentedHistoryAtom_measurable (n k : ℕ)
    (key : AugmentedHistoryValue A rowSize n) :
    MeasurableSet[augmentedRowFiltrationSigma A rowSize n k]
      (augmentedHistoryAtom A rowSize n k key) := by
  have hProjection :
      Measurable[augmentedRowFiltrationSigma A rowSize n k]
        (augmentedHistoryProjection A rowSize n k) := by
    rw [measurable_iff_comap_le,
      augmentedRowFiltrationSigma_eq_comap_augmentedHistory A]
  exact hProjection (measurableSet_singleton key)

/-- An augmented atom is the intersection of an earlier-row atom and a
current-row prefix fiber. -/
theorem augmentedHistoryAtom_eq_inter (n k : ℕ)
    (key : AugmentedHistoryValue A rowSize n) :
    augmentedHistoryAtom A rowSize n k key =
      earlierRowsAtom A rowSize n key.1 ∩
        (rowCoordinate A rowSize n) ⁻¹'
          currentHistoryFiber A rowSize n k key.2 := by
  rcases key with ⟨earlier, history⟩
  ext omega
  simp [augmentedHistoryAtom, augmentedHistoryProjection,
    earlierRowsAtom, currentHistoryFiber, currentHistoryProjection,
    rowCoordinate]

/-! ## Integral factorization on one augmented atom -/

/-- Integrability is preserved when a finite row variable is lifted through a
measure-preserving coordinate projection. -/
theorem liftRowVariable_integrable (n : ℕ)
    (f : CommonRow A rowSize n → ℝ)
    (hf : Integrable f (commonRowMeasure A rowSize n)) :
    Integrable (liftRowVariable A rowSize n f)
      (commonMeasure A rowSize) := by
  have hComp :=
    ((rowCoordinate_measurePreserving A rowSize n).integrable_comp hf.1).2 hf
  change Integrable (fun omega : CommonOmega A rowSize => f (omega n))
    (commonMeasure A rowSize)
  exact hComp

/-- Almost-everywhere row identities remain almost-everywhere identities after
coordinate lifting. -/
theorem liftRowVariable_ae_eq (n : ℕ)
    {f g : CommonRow A rowSize n → ℝ}
    (hfg : f =ᵐ[commonRowMeasure A rowSize n] g) :
    liftRowVariable A rowSize n f =ᵐ[commonMeasure A rowSize]
      liftRowVariable A rowSize n g := by
  have hTendsto :
      Tendsto (rowCoordinate A rowSize n)
        (ae (commonMeasure A rowSize))
        (ae (commonRowMeasure A rowSize n)) :=
    (rowCoordinate_measurePreserving A rowSize n).quasiMeasurePreserving.tendsto_ae
  change (fun omega : CommonOmega A rowSize => f (omega n)) =ᵐ[
      commonMeasure A rowSize]
    (fun omega : CommonOmega A rowSize => g (omega n))
  exact hTendsto hfg

/-- Product independence factors a lifted row integral on one augmented atom
into an earlier-atom probability and the corresponding row prefix integral. -/
theorem setIntegral_liftRowVariable_augmentedAtom
    (n k : ℕ) (key : AugmentedHistoryValue A rowSize n)
    (f : CommonRow A rowSize n → ℝ) :
    (∫ omega in augmentedHistoryAtom A rowSize n k key,
        liftRowVariable A rowSize n f omega
        ∂commonMeasure A rowSize) =
      (commonMeasure A rowSize).real
          (earlierRowsAtom A rowSize n key.1) *
        ∫ row in currentHistoryFiber A rowSize n k key.2,
          f row ∂commonRowMeasure A rowSize n := by
  classical
  let currentFiber := currentHistoryFiber A rowSize n k key.2
  let earlierAtom := earlierRowsAtom A rowSize n key.1
  have hfMeasurable : Measurable f := by
    intro s hs
    exact MeasurableSet.of_discrete
  have hCurrentPrefix :
      MeasurableSet[(A n).rowFiltrationSigma (rowSize n) k]
        currentFiber :=
    currentHistoryFiber_measurable A rowSize n k key.2
  have hCurrentFull : MeasurableSet currentFiber :=
    (show (A n).rowFiltrationSigma (rowSize n) k ≤
      (⊤ : MeasurableSpace (CommonRow A rowSize n)) from le_top)
      _ hCurrentPrefix
  have hEarlier :
      MeasurableSet[completeEarlierRowsSigma A rowSize n] earlierAtom :=
    earlierRowsAtom_measurable A rowSize n key.1
  have hCurrentPreimage :
      MeasurableSet ((rowCoordinate A rowSize n) ⁻¹' currentFiber) :=
    (rowCoordinate_measurable A rowSize n) hCurrentFull
  have hIndicatorStrong :
      AEStronglyMeasurable (currentFiber.indicator f)
        ((commonMeasure A rowSize).map (rowCoordinate A rowSize n)) :=
    (hfMeasurable.indicator hCurrentFull).aestronglyMeasurable
  have hFactor :=
    (completeEarlierRowsSigma_indep_currentRow A rowSize n).setIntegral_eq_mul
      (completeEarlierRowsSigma_le A rowSize n)
      (rowCoordinate_measurable A rowSize n).aemeasurable
      hEarlier hIndicatorStrong
  rw [augmentedHistoryAtom_eq_inter A]
  calc
    (∫ omega in earlierAtom ∩
          (rowCoordinate A rowSize n) ⁻¹' currentFiber,
        liftRowVariable A rowSize n f omega
        ∂commonMeasure A rowSize) =
        ∫ omega in earlierAtom,
          (currentFiber.indicator f) (rowCoordinate A rowSize n omega)
          ∂commonMeasure A rowSize := by
      rw [← MeasureTheory.setIntegral_indicator hCurrentPreimage]
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => by
        by_cases homega : rowCoordinate A rowSize n omega ∈ currentFiber
        · change (if rowCoordinate A rowSize n omega ∈ currentFiber
              then liftRowVariable A rowSize n f omega else 0) =
            (if rowCoordinate A rowSize n omega ∈ currentFiber
              then f (rowCoordinate A rowSize n omega) else 0)
          rw [if_pos homega, if_pos homega]
          rfl
        · change (if rowCoordinate A rowSize n omega ∈ currentFiber
              then liftRowVariable A rowSize n f omega else 0) =
            (if rowCoordinate A rowSize n omega ∈ currentFiber
              then f (rowCoordinate A rowSize n omega) else 0)
          rw [if_neg homega, if_neg homega]
    _ = (commonMeasure A rowSize).real earlierAtom *
        ∫ omega,
          (currentFiber.indicator f) (rowCoordinate A rowSize n omega)
          ∂commonMeasure A rowSize := hFactor
    _ = (commonMeasure A rowSize).real earlierAtom *
        ∫ row, currentFiber.indicator f row
          ∂commonRowMeasure A rowSize n := by
      congr 1
      rw [← MeasureTheory.integral_map
        (rowCoordinate_measurable A rowSize n).aemeasurable
        hIndicatorStrong,
        commonMeasure_map_coordinate A rowSize n]
    _ = (commonMeasure A rowSize).real earlierAtom *
        ∫ row in currentFiber, f row
          ∂commonRowMeasure A rowSize n := by
      rw [MeasureTheory.integral_indicator hCurrentFull]

/-- The canonical row conditional expectation has the same integral as the row
variable on every current-history fiber. -/
theorem rowCondExp_setIntegral_currentHistoryFiber
    (n k : ℕ) (f : CommonRow A rowSize n → ℝ)
    (key : (A n).HistoryKey (rowSize n)) :
    (∫ row in currentHistoryFiber A rowSize n k key,
        ((A n).mathlibRowMeasure (rowSize n))[
          f | (A n).rowFiltrationSigma (rowSize n) k] row
        ∂commonRowMeasure A rowSize n) =
      ∫ row in currentHistoryFiber A rowSize n k key,
        f row ∂commonRowMeasure A rowSize n := by
  exact MeasureTheory.setIntegral_condExp le_top
    ((A n).integrable_mathlibRowMeasure (rowSize n) f)
    (currentHistoryFiber_measurable A rowSize n k key)

/-- The lifted canonical conditional expectation and the lifted row variable
have equal integrals on every augmented-history atom. -/
theorem canonicalCondExp_setIntegral_augmentedHistoryAtom
    (n k : ℕ) (f : CommonRow A rowSize n → ℝ)
    (key : AugmentedHistoryValue A rowSize n) :
    (∫ omega in augmentedHistoryAtom A rowSize n k key,
        liftRowVariable A rowSize n
          (((A n).mathlibRowMeasure (rowSize n))[
            f | (A n).rowFiltrationSigma (rowSize n) k]) omega
        ∂commonMeasure A rowSize) =
      ∫ omega in augmentedHistoryAtom A rowSize n k key,
        liftRowVariable A rowSize n f omega
        ∂commonMeasure A rowSize := by
  rw [setIntegral_liftRowVariable_augmentedAtom A,
    setIntegral_liftRowVariable_augmentedAtom A,
    rowCondExp_setIntegral_currentHistoryFiber A]

/-! ## Finite unions of augmented atoms -/

def augmentedHistoryAtomUnion (n k : ℕ)
    (keys : Finset (AugmentedHistoryValue A rowSize n)) :
    Set (CommonOmega A rowSize) :=
  ⋃ key ∈ keys, augmentedHistoryAtom A rowSize n k key

theorem augmentedHistoryAtomUnion_measurable
    (n k : ℕ) (keys : Finset (AugmentedHistoryValue A rowSize n)) :
    MeasurableSet[augmentedRowFiltrationSigma A rowSize n k]
      (augmentedHistoryAtomUnion A rowSize n k keys) := by
  classical
  induction keys using Finset.induction_on with
  | empty => simp [augmentedHistoryAtomUnion]
  | @insert key keys hnot ih =>
      rw [show augmentedHistoryAtomUnion A rowSize n k (insert key keys) =
          augmentedHistoryAtom A rowSize n k key ∪
            augmentedHistoryAtomUnion A rowSize n k keys by
        ext omega
        simp [augmentedHistoryAtomUnion]]
      exact (augmentedHistoryAtom_measurable A rowSize n k key).union ih

theorem augmentedHistoryAtom_disjoint_atomUnion
    (n k : ℕ) (key : AugmentedHistoryValue A rowSize n)
    (keys : Finset (AugmentedHistoryValue A rowSize n))
    (hkey : key ∉ keys) :
    Disjoint (augmentedHistoryAtom A rowSize n k key)
      (augmentedHistoryAtomUnion A rowSize n k keys) := by
  classical
  rw [Set.disjoint_left]
  intro omega homega hunion
  change augmentedHistoryProjection A rowSize n k omega = key at homega
  simp only [augmentedHistoryAtomUnion, Set.mem_iUnion,
    augmentedHistoryAtom, Set.mem_setOf_eq] at hunion
  rcases hunion with ⟨other, hother, homegaOther⟩
  have : key = other := homega.symm.trans homegaOther
  subst other
  exact hkey (by simpa [homega] using hother)

/-- Equality on every atom extends to equality on an arbitrary finite union of
atoms. -/
theorem setIntegral_atomUnion_eq
    (n k : ℕ) (f g : CommonOmega A rowSize → ℝ)
    (hf : Integrable f (commonMeasure A rowSize))
    (hg : Integrable g (commonMeasure A rowSize))
    (hAtom : ∀ key : AugmentedHistoryValue A rowSize n,
      (∫ omega in augmentedHistoryAtom A rowSize n k key,
          g omega ∂commonMeasure A rowSize) =
        ∫ omega in augmentedHistoryAtom A rowSize n k key,
          f omega ∂commonMeasure A rowSize)
    (keys : Finset (AugmentedHistoryValue A rowSize n)) :
    (∫ omega in augmentedHistoryAtomUnion A rowSize n k keys,
        g omega ∂commonMeasure A rowSize) =
      ∫ omega in augmentedHistoryAtomUnion A rowSize n k keys,
        f omega ∂commonMeasure A rowSize := by
  classical
  induction keys using Finset.induction_on with
  | empty => simp [augmentedHistoryAtomUnion]
  | @insert key keys hnot ih =>
      have hUnion :
          augmentedHistoryAtomUnion A rowSize n k (insert key keys) =
            augmentedHistoryAtom A rowSize n k key ∪
              augmentedHistoryAtomUnion A rowSize n k keys := by
        ext omega
        simp [augmentedHistoryAtomUnion]
      have hDisjoint :=
        augmentedHistoryAtom_disjoint_atomUnion A
          rowSize n k key keys hnot
      have hMeasurable :=
        augmentedHistoryAtomUnion_measurable A rowSize n k keys
      have hMeasurableFull :
          MeasurableSet (augmentedHistoryAtomUnion A rowSize n k keys) :=
        (augmentedRowFiltrationSigma_le A rowSize n k) _ hMeasurable
      calc
        (∫ omega in augmentedHistoryAtomUnion A rowSize n k (insert key keys),
            g omega ∂commonMeasure A rowSize) =
            (∫ omega in augmentedHistoryAtom A rowSize n k key,
                g omega ∂commonMeasure A rowSize) +
              ∫ omega in augmentedHistoryAtomUnion A rowSize n k keys,
                g omega ∂commonMeasure A rowSize := by
          rw [hUnion]
          exact MeasureTheory.setIntegral_union hDisjoint hMeasurableFull
            hg.integrableOn hg.integrableOn
        _ = (∫ omega in augmentedHistoryAtom A rowSize n k key,
                f omega ∂commonMeasure A rowSize) +
              ∫ omega in augmentedHistoryAtomUnion A rowSize n k keys,
                f omega ∂commonMeasure A rowSize := by
          rw [hAtom key, ih]
        _ = ∫ omega in
              augmentedHistoryAtomUnion A rowSize n k (insert key keys),
                f omega ∂commonMeasure A rowSize := by
          rw [hUnion]
          exact (MeasureTheory.setIntegral_union hDisjoint hMeasurableFull
            hf.integrableOn hf.integrableOn).symm

/-- Every measurable augmented event is a finite union of its observation
fibers. -/
theorem measurable_augmentedEvent_eq_atomUnion
    (n k : ℕ) (s : Set (CommonOmega A rowSize))
    (hs : MeasurableSet[augmentedRowFiltrationSigma A rowSize n k] s) :
    ∃ keys : Finset (AugmentedHistoryValue A rowSize n),
      s = augmentedHistoryAtomUnion A rowSize n k keys := by
  classical
  rw [augmentedRowFiltrationSigma_eq_comap_augmentedHistory A] at hs
  change ∃ u : Set (AugmentedHistoryValue A rowSize n),
    MeasurableSet u ∧
      (augmentedHistoryProjection A rowSize n k) ⁻¹' u = s at hs
  rcases hs with ⟨u, hu, hus⟩
  let keys : Finset (AugmentedHistoryValue A rowSize n) :=
    Finset.univ.filter fun key => key ∈ u
  refine ⟨keys, hus.symm.trans ?_⟩
  ext omega
  simp [keys, augmentedHistoryAtomUnion, augmentedHistoryAtom]

/-- The lifted canonical row conditional expectation has the defining set
integrals on every augmented measurable event. -/
theorem canonicalCondExp_setIntegral_augmentedEvent
    (n k : ℕ) (f : CommonRow A rowSize n → ℝ)
    (s : Set (CommonOmega A rowSize))
    (hs : MeasurableSet[augmentedRowFiltrationSigma A rowSize n k] s) :
    (∫ omega in s,
        liftRowVariable A rowSize n
          (((A n).mathlibRowMeasure (rowSize n))[
            f | (A n).rowFiltrationSigma (rowSize n) k]) omega
        ∂commonMeasure A rowSize) =
      ∫ omega in s, liftRowVariable A rowSize n f omega
        ∂commonMeasure A rowSize := by
  rcases measurable_augmentedEvent_eq_atomUnion A rowSize n k s hs with
    ⟨keys, rfl⟩
  have hfRow := (A n).integrable_mathlibRowMeasure (rowSize n) f
  have hfCommon := liftRowVariable_integrable A rowSize n f hfRow
  have hCondCommon := liftRowVariable_integrable A rowSize n
    (((A n).mathlibRowMeasure (rowSize n))[
      f | (A n).rowFiltrationSigma (rowSize n) k])
    (integrable_condExp (μ := (A n).mathlibRowMeasure (rowSize n)))
  exact setIntegral_atomUnion_eq A rowSize n k
    (liftRowVariable A rowSize n f)
    (liftRowVariable A rowSize n
      (((A n).mathlibRowMeasure (rowSize n))[
        f | (A n).rowFiltrationSigma (rowSize n) k]))
    hfCommon hCondCommon
    (canonicalCondExp_setIntegral_augmentedHistoryAtom A rowSize n k f)
    keys

/-! ## Literal common-space conditional expectation -/

/-- The canonical row conditional expectation pulls back to the literal
common-space conditional expectation for the augmented sigma algebra. -/
theorem commonCondExp_lift_canonical
    (n k : ℕ) (f : CommonRow A rowSize n → ℝ) :
    (commonMeasure A rowSize)[
        liftRowVariable A rowSize n f |
        augmentedRowFiltrationSigma A rowSize n k] =ᵐ[
          commonMeasure A rowSize]
      liftRowVariable A rowSize n
        (((A n).mathlibRowMeasure (rowSize n))[
          f | (A n).rowFiltrationSigma (rowSize n) k]) := by
  let rowCondExp :=
    ((A n).mathlibRowMeasure (rowSize n))[
      f | (A n).rowFiltrationSigma (rowSize n) k]
  have hfCommon :
      Integrable (liftRowVariable A rowSize n f)
        (commonMeasure A rowSize) :=
    liftRowVariable_integrable A rowSize n f
      ((A n).integrable_mathlibRowMeasure (rowSize n) f)
  have hRowCondMeasurable :
      Measurable[(A n).rowFiltrationSigma (rowSize n) k] rowCondExp :=
    stronglyMeasurable_condExp.measurable
  have hCandidateMeasurable :
      Measurable[augmentedRowFiltrationSigma A rowSize n k]
        (liftRowVariable A rowSize n rowCondExp) :=
    liftRowVariable_measurable A rowSize n k rowCondExp
      hRowCondMeasurable
  have hCandidateIntegrable :
      Integrable (liftRowVariable A rowSize n rowCondExp)
        (commonMeasure A rowSize) :=
    liftRowVariable_integrable A rowSize n rowCondExp
      (integrable_condExp (μ := (A n).mathlibRowMeasure (rowSize n)))
  have hUnique :=
    MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
      (m₀ := (inferInstance : MeasurableSpace (CommonOmega A rowSize)))
      (m := augmentedRowFiltrationSigma A rowSize n k)
      (μ := commonMeasure A rowSize)
      (f := liftRowVariable A rowSize n f)
      (g := liftRowVariable A rowSize n rowCondExp)
      (hm := augmentedRowFiltrationSigma_le A rowSize n k)
      hfCommon
      (fun s hs hfinite => hCandidateIntegrable.integrableOn)
      (fun s hs hfinite => by
        exact canonicalCondExp_setIntegral_augmentedEvent A
          rowSize n k f s hs)
      hCandidateMeasurable.aestronglyMeasurable
  exact hUnique.symm

/-- Full closure of `CommonSpaceCondExpPullbackAPI.condExp_lift`. -/
theorem commonCondExp_lift
    (n k : ℕ) (f g : CommonRow A rowSize n → ℝ)
    (hfg : ((A n).mathlibRowMeasure (rowSize n))[
        f | (A n).rowFiltrationSigma (rowSize n) k] =ᵐ[
          (A n).mathlibRowMeasure (rowSize n)] g) :
    (commonMeasure A rowSize)[
        liftRowVariable A rowSize n f |
        augmentedRowFiltrationSigma A rowSize n k] =ᵐ[
          commonMeasure A rowSize]
      liftRowVariable A rowSize n g :=
  (commonCondExp_lift_canonical A rowSize n k f).trans
    (liftRowVariable_ae_eq A rowSize n hfg)

/-- Concrete inhabitant closing the previously isolated API structure. -/
noncomputable def commonSpaceCondExpPullbackAPI :
    CommonSpaceCondExpPullbackAPI A rowSize where
  condExp_lift := by
    intro n k f g hfg
    exact commonCondExp_lift A rowSize n k f g hfg

/-! ## Unconditional lifted martingale-array identities -/

theorem liftedScore_condExp_zero_closed
    (n : ℕ) (t : Fin (3 * rowSize n)) :
    (commonMeasure A rowSize)[
        liftedScore A rowSize n t |
        augmentedRowFiltrationSigma A rowSize n t.1] =ᵐ[
          commonMeasure A rowSize]
      (fun _ : CommonOmega A rowSize => (0 : ℝ)) :=
  liftedScore_condExp_zero A rowSize
    (commonSpaceCondExpPullbackAPI A rowSize) n t

theorem liftedSquaredScore_condExp_eq_oneShotFisher_closed
    (n : ℕ) (hrow : 0 < rowSize n) (t : Fin (3 * rowSize n)) :
    (commonMeasure A rowSize)[
        liftedSquaredScore A rowSize n t |
        augmentedRowFiltrationSigma A rowSize n t.1] =ᵐ[
          commonMeasure A rowSize]
      liftedOneShotFisher A rowSize n t :=
  liftedSquaredScore_condExp_eq_oneShotFisher A rowSize
    (commonSpaceCondExpPullbackAPI A rowSize) n hrow t

theorem liftedLindeberg_condExp_eq_kernel_closed
    (n : ℕ) (t : Fin (3 * rowSize n)) (epsilon : ℝ) :
    (commonMeasure A rowSize)[
        liftedLindebergObservable A rowSize n t epsilon |
        augmentedRowFiltrationSigma A rowSize n t.1] =ᵐ[
          commonMeasure A rowSize]
      liftedOneShotLindebergKernel A rowSize n t epsilon :=
  liftedLindeberg_condExp_eq_kernel A rowSize
    (commonSpaceCondExpPullbackAPI A rowSize) n t epsilon

theorem commonSpace_literal_martingaleDifference_row (n : ℕ) :
    ∀ t : Fin (3 * rowSize n),
      (commonMeasure A rowSize)[
          liftedScore A rowSize n t |
          augmentedRowFiltrationSigma A rowSize n t.1] =ᵐ[
            commonMeasure A rowSize]
        (fun _ : CommonOmega A rowSize => (0 : ℝ)) := by
  intro t
  exact liftedScore_condExp_zero_closed A rowSize n t

theorem commonSpace_literal_predictableQuadraticVariation
    (n : ℕ) (hrow : 0 < rowSize n) :
    (∀ t : Fin (3 * rowSize n),
      (commonMeasure A rowSize)[
          liftedSquaredScore A rowSize n t |
          augmentedRowFiltrationSigma A rowSize n t.1] =ᵐ[
            commonMeasure A rowSize]
        liftedOneShotFisher A rowSize n t) ∧
      liftedPredictableQuadraticVariation A rowSize n =
        liftedExplicitNormalizedFisher A rowSize n := by
  constructor
  · intro t
    exact liftedSquaredScore_condExp_eq_oneShotFisher_closed A
      rowSize n hrow t
  · exact liftedPredictableQuadraticVariation_eq_explicitFisher A
      rowSize n

theorem commonSpace_literal_predictableLindeberg
    (n : ℕ) (epsilon : ℝ) :
    (∀ t : Fin (3 * rowSize n),
      (commonMeasure A rowSize)[
          liftedLindebergObservable A rowSize n t epsilon |
          augmentedRowFiltrationSigma A rowSize n t.1] =ᵐ[
            commonMeasure A rowSize]
        liftedOneShotLindebergKernel A rowSize n t epsilon) ∧
      liftedPredictableLindebergExpression A rowSize n epsilon =
        liftedConditionalLindebergSum A rowSize n epsilon := by
  constructor
  · intro t
    exact liftedLindeberg_condExp_eq_kernel_closed A
      rowSize n t epsilon
  · exact liftedPredictableLindebergExpression_eq_sum A
      rowSize n epsilon

end PullbackClosure

end MixedExactCycleScalarTriangularArrayData
end QubitOracle.Paper
