import CarrySelfAdjointOperator.TailCutoffMomentShiftDiagnosis
import CarrySelfAdjointOperator.FiniteHankelShiftBoundaryCorrection
import Mathlib.Tactic

/-!
# Boundary-completed transport

This file isolates one elementary algebraic pattern which occurs in two
different roles in the development.

* In the **synthesis form**, an interior transport loses a boundary block,
  which is sent to a port.  The port plus interior synthesis is invariant.
* In the **metric form**, a truncated shift misses a boundary column.  A
  boundary correction restores the prescribed Gram transport.

The file deliberately does not identify the two transports.  In particular,
the cutoff shift of a completion tail and the moment-order shift of a Hankel
tower live on different indices.  What they share is the boundary-completion
equation below.
-/

open scoped BigOperators Matrix

namespace CarrySelfAdjointOperator

noncomputable section

open NativeCarrySpectralWeyl.Camera

/-! ## Synthesis form -/

section Synthesis

variable {𝕜 : Type*} [CommRing 𝕜]
variable {P X Y : Type*}
variable [AddCommGroup P] [Module 𝕜 P]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-- Move an interior boundary block into a port and then transport the
remaining interior. -/
def boundaryCompletedTransport
    (boundary : X →ₗ[𝕜] P) (interior : X →ₗ[𝕜] X) :
    (P × X) →ₗ[𝕜] (P × X) where
  toFun state := (state.1 + boundary state.2, interior state.2)
  map_add' left right := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' scalar state := by
    ext <;> simp [smul_add]

/-- Synthesize a port and an interior state into the represented object. -/
def boundarySynthesis
    (port : P →ₗ[𝕜] Y) (interior : X →ₗ[𝕜] Y) :
    (P × X) →ₗ[𝕜] Y where
  toFun state := port state.1 + interior state.2
  map_add' left right := by
    simp [add_assoc, add_left_comm, add_comm]
  map_smul' scalar state := by
    simp [smul_add]

/-- Analyse a state into its boundary trace and its interior defect.  This is
the static reconstruction form used by TFVD; unlike the cutoff move, it does
not itself advance a representation boundary. -/
def boundaryAnalysis
    (trace : Y →ₗ[𝕜] P) (defect : Y →ₗ[𝕜] X) :
    Y →ₗ[𝕜] (P × X) where
  toFun state := (trace state, defect state)
  map_add' left right := by
    ext <;> simp
  map_smul' scalar state := by
    ext <;> simp

/-- Exact recovery of a state from an interior defect and a boundary trace. -/
def IsBoundaryReconstruction
    (port : P →ₗ[𝕜] Y) (green : X →ₗ[𝕜] Y)
    (trace : Y →ₗ[𝕜] P) (defect : Y →ₗ[𝕜] X) : Prop :=
  port.comp trace + green.comp defect = LinearMap.id

/-- The static identity `return ∘ trace + Green ∘ defect = I` is exactly a
left inverse statement for analysis and synthesis. -/
theorem isBoundaryReconstruction_iff_synthesis_comp_analysis_eq_id
    (port : P →ₗ[𝕜] Y) (green : X →ₗ[𝕜] Y)
    (trace : Y →ₗ[𝕜] P) (defect : Y →ₗ[𝕜] X) :
    IsBoundaryReconstruction port green trace defect ↔
      (boundarySynthesis port green).comp
          (boundaryAnalysis trace defect) = LinearMap.id := by
  constructor <;> intro h
  · apply LinearMap.ext
    intro state
    simpa [IsBoundaryReconstruction, boundarySynthesis, boundaryAnalysis,
      LinearMap.add_apply, LinearMap.comp_apply] using congrArg (fun map => map state) h
  · apply LinearMap.ext
    intro state
    simpa [IsBoundaryReconstruction, boundarySynthesis, boundaryAnalysis,
      LinearMap.add_apply, LinearMap.comp_apply] using congrArg (fun map => map state) h

/-- Exact reconstruction makes the analysis map injective: its trace and
defect together retain the whole input state. -/
theorem boundaryAnalysis_injective_of_reconstruction
    (port : P →ₗ[𝕜] Y) (green : X →ₗ[𝕜] Y)
    (trace : Y →ₗ[𝕜] P) (defect : Y →ₗ[𝕜] X)
    (hreconstruct : IsBoundaryReconstruction port green trace defect) :
    Function.Injective (boundaryAnalysis trace defect) := by
  have hleft : Function.LeftInverse (boundarySynthesis port green)
      (boundaryAnalysis trace defect) := by
    intro state
    have hinv := (isBoundaryReconstruction_iff_synthesis_comp_analysis_eq_id
      port green trace defect).mp hreconstruct
    exact congrArg (fun map => map state) hinv
  exact hleft.injective

/-- The boundary equation says that the part lost by interior transport is
exactly what emerges through the port. -/
def IsBoundaryCompletedSynthesis
    (port : P →ₗ[𝕜] Y) (readout : X →ₗ[𝕜] Y)
    (boundary : X →ₗ[𝕜] P) (interior : X →ₗ[𝕜] X) : Prop :=
  port.comp boundary + readout.comp interior = readout

/-- Equivalent defect form of the port equation.  This is the precise
`R (I - S) = J β` identity: what the interior transport fails to preserve is
exactly the boundary emission. -/
theorem isBoundaryCompletedSynthesis_iff_readout_id_sub_interior_eq_port_boundary
    (port : P →ₗ[𝕜] Y) (readout : X →ₗ[𝕜] Y)
    (boundary : X →ₗ[𝕜] P) (interior : X →ₗ[𝕜] X) :
    IsBoundaryCompletedSynthesis port readout boundary interior ↔
      readout.comp ((LinearMap.id : X →ₗ[𝕜] X) - interior) = port.comp boundary := by
  constructor
  · intro hboundary
    apply LinearMap.ext
    intro x
    have hx : port (boundary x) + readout (interior x) = readout x := by
      simpa [IsBoundaryCompletedSynthesis, LinearMap.add_apply,
        LinearMap.comp_apply] using congrArg (fun map => map x) hboundary
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub]
    rw [← hx]
    abel
  · intro hdefect
    apply LinearMap.ext
    intro x
    have hx : readout x - readout (interior x) = port (boundary x) := by
      simpa [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        map_sub] using
        congrArg (fun map => map x) hdefect
    change port (boundary x) + readout (interior x) = readout x
    rw [← hx]
    abel

/-- The boundary equation is precisely the invariance of the synthesized
object under the completed transport. -/
theorem boundarySynthesis_comp_boundaryCompletedTransport
    (port : P →ₗ[𝕜] Y) (readout : X →ₗ[𝕜] Y)
    (boundary : X →ₗ[𝕜] P) (interior : X →ₗ[𝕜] X)
    (hboundary : IsBoundaryCompletedSynthesis port readout boundary interior) :
    (boundarySynthesis port readout).comp
        (boundaryCompletedTransport boundary interior) =
      boundarySynthesis port readout := by
  apply LinearMap.ext
  intro state
  obtain ⟨p, x⟩ := state
  have hx : port (boundary x) + readout (interior x) = readout x := by
    simpa [IsBoundaryCompletedSynthesis, LinearMap.add_apply,
      LinearMap.comp_apply] using congrArg (fun map => map x) hboundary
  simp only [LinearMap.comp_apply, boundaryCompletedTransport,
    boundarySynthesis, LinearMap.coe_mk, AddHom.coe_mk]
  rw [port.map_add]
  calc
    port p + port (boundary x) + readout (interior x) =
        port p + (port (boundary x) + readout (interior x)) := by abel
    _ = port p + readout x := by rw [hx]

/-- Conversely, invariance of synthesis recovers the exact boundary equation
by testing a state with zero port component. -/
theorem isBoundaryCompletedSynthesis_of_synthesis_invariant
    (port : P →ₗ[𝕜] Y) (readout : X →ₗ[𝕜] Y)
    (boundary : X →ₗ[𝕜] P) (interior : X →ₗ[𝕜] X)
    (hinvariant :
      (boundarySynthesis port readout).comp
          (boundaryCompletedTransport boundary interior) =
        boundarySynthesis port readout) :
    IsBoundaryCompletedSynthesis port readout boundary interior := by
  ext x
  have hzero := congrArg (fun map => map (0, x)) hinvariant
  simpa [boundarySynthesis, boundaryCompletedTransport, LinearMap.comp_apply,
    LinearMap.add_apply] using hzero

/-- Exact equivalence between a port identity and cutoff/representation
invariance of the synthesized object. -/
theorem isBoundaryCompletedSynthesis_iff_synthesis_invariant
    (port : P →ₗ[𝕜] Y) (readout : X →ₗ[𝕜] Y)
    (boundary : X →ₗ[𝕜] P) (interior : X →ₗ[𝕜] X) :
    IsBoundaryCompletedSynthesis port readout boundary interior ↔
      (boundarySynthesis port readout).comp
          (boundaryCompletedTransport boundary interior) =
        boundarySynthesis port readout := by
  constructor
  · exact boundarySynthesis_comp_boundaryCompletedTransport
      port readout boundary interior
  · exact isBoundaryCompletedSynthesis_of_synthesis_invariant
      port readout boundary interior

end Synthesis

/-! ## Exact tail instance

The synthesis equation is meaningful for a summable tail.  We state the
instance on functions with a displayed `Summable` hypothesis rather than
silently treating summation as a bounded functional on `ℓ²`.
-/

section Tail

/-- The backward shift of a tail.  Its leading cell is the block crossing the
cutoff boundary. -/
def tailBackwardShift (tail : ℕ → ℂ) : ℕ → ℂ :=
  fun index => tail (index + 1)

/-- The completed cutoff move transfers the leading tail cell to the finite
head and shifts the still-unconsumed tail backward. -/
def tailCompletedCutoffTransport (state : ℂ × (ℕ → ℂ)) : ℂ × (ℕ → ℂ) :=
  (state.1 + state.2 0, tailBackwardShift state.2)

/-- Synthesis of a finite head and a summable unconsumed tail. -/
def tailSynthesis (state : ℂ × (ℕ → ℂ)) : ℂ :=
  state.1 + ∑' index : ℕ, state.2 index

/-- The telescoping Green identity for a summable tail: moving the cutoff
changes the ledger but leaves its synthesized completed value unchanged. -/
theorem tailSynthesis_cutoffTransport
    (head : ℂ) (tail : ℕ → ℂ) (htail : Summable tail) :
    tailSynthesis (tailCompletedCutoffTransport (head, tail)) =
      tailSynthesis (head, tail) := by
  have hsplit := htail.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  unfold tailSynthesis tailCompletedCutoffTransport tailBackwardShift
  rw [← hsplit]
  ring

/-- The literal head plus aligned-center tail ledger at a fixed camera,
cutoff, and native time. -/
def finiteCameraPhysicalCutoffLedger
    (camera cutoff : ℕ) (time : ℝ) : ℂ × (ℕ → ℂ) :=
  (finiteCameraPhysicalRawHead camera cutoff time,
    fun index => centerBracketTerm camera (nativeLine time) (index + cutoff))

/-- The finite head absorbs exactly the leading center block that leaves the
tail when the geometric cutoff advances. -/
theorem finiteCameraPhysicalRawHead_succ_eq_add_centerBracketTerm
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (time : ℝ) :
    finiteCameraPhysicalRawHead camera (cutoff + 1) time =
      finiteCameraPhysicalRawHead camera cutoff time +
        centerBracketTerm camera (nativeLine time) cutoff := by
  have hdelta := finiteCameraPhysicalRawHead_sub_eq_completionTail_sub
    camera cutoff (cutoff + 1) time hcamera
  rw [finiteCameraPhysicalCompletionTail_succ hcamera time] at hdelta
  calc
    finiteCameraPhysicalRawHead camera (cutoff + 1) time =
        (finiteCameraPhysicalRawHead camera (cutoff + 1) time -
          finiteCameraPhysicalRawHead camera cutoff time) +
            finiteCameraPhysicalRawHead camera cutoff time := by ring
    _ = (finiteCameraPhysicalCompletionTail camera cutoff time -
          (finiteCameraPhysicalCompletionTail camera cutoff time -
            centerBracketTerm camera (nativeLine time) cutoff)) +
            finiteCameraPhysicalRawHead camera cutoff time := by rw [hdelta]
    _ = finiteCameraPhysicalRawHead camera cutoff time +
          centerBracketTerm camera (nativeLine time) cutoff := by ring

/-- The literal camera ledger evolves by the abstract completed cutoff move. -/
theorem finiteCameraPhysicalCutoffLedger_succ
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (time : ℝ) :
    tailCompletedCutoffTransport
        (finiteCameraPhysicalCutoffLedger camera cutoff time) =
      finiteCameraPhysicalCutoffLedger camera (cutoff + 1) time := by
  apply Prod.ext
  · simpa [tailCompletedCutoffTransport, finiteCameraPhysicalCutoffLedger] using
      (finiteCameraPhysicalRawHead_succ_eq_add_centerBracketTerm hcamera time).symm
  · funext index
    simp only [tailCompletedCutoffTransport, finiteCameraPhysicalCutoffLedger,
      tailBackwardShift]
    congr 1
    omega

/-- The synthesis of the literal ledger is the existing completed camera
characteristic. -/
theorem finiteCameraPhysicalCutoffLedger_synthesis_eq_completed
    (camera cutoff : ℕ) (time : ℝ) :
    tailSynthesis (finiteCameraPhysicalCutoffLedger camera cutoff time) =
      completedNativeCharacteristic camera cutoff (nativeLine time) := by
  exact finiteCameraPhysicalRawHead_add_completionTail_eq_completed
    camera cutoff time

/-- Exact representation invariance for the literal physical camera ledger.
This is the `Σ U_cut = Σ` instance behind cutoff-independent completion. -/
theorem finiteCameraPhysicalCutoffLedger_synthesis_succ
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (time : ℝ) :
    tailSynthesis (finiteCameraPhysicalCutoffLedger camera (cutoff + 1) time) =
      tailSynthesis (finiteCameraPhysicalCutoffLedger camera cutoff time) := by
  rw [← finiteCameraPhysicalCutoffLedger_succ hcamera time]
  apply tailSynthesis_cutoffTransport
  apply (centerBracketTerm_summable hcamera (by
    rw [nativeLine_re]
    norm_num)).comp_injective
  intro left right h
  exact Nat.add_right_cancel h

end Tail

/-! ## Metric form -/

section Metric

variable {R : Type*} [CommRing R]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Correct a truncated interior transport by a boundary factor
`column * boundary`. -/
def boundaryCompletedMetricTransport
    (interior : Matrix ι ι R) (column : Matrix ι κ R)
    (boundary : Matrix κ ι R) : Matrix ι ι R :=
  interior + column * boundary

/-- If the target Gram transport differs from an interior shift by a factored
boundary defect, solving the column equation restores the target exactly. -/
theorem gram_mul_boundaryCompletedMetricTransport
    (gram interior target : Matrix ι ι R)
    (defect : Matrix ι κ R) (boundary : Matrix κ ι R)
    (column : Matrix ι κ R)
    (hdefect : target - gram * interior = defect * boundary)
    (hcolumn : gram * column = defect) :
    gram * boundaryCompletedMetricTransport interior column boundary = target := by
  unfold boundaryCompletedMetricTransport
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hcolumn]
  rw [← hdefect]
  abel

/-- When the Gram and target forms are symmetric, the completed transport is
self-adjoint for the Gram metric. -/
theorem boundaryCompletedMetricTransport_transpose_mul_gram
    (gram interior target : Matrix ι ι R)
    (boundary : Matrix κ ι R)
    (column : Matrix ι κ R)
    (hgram : gram.IsSymm) (htarget : target.IsSymm)
    (htransport :
      gram * boundaryCompletedMetricTransport interior column boundary = target) :
    (boundaryCompletedMetricTransport interior column boundary).transpose * gram =
      target := by
  calc
    (boundaryCompletedMetricTransport interior column boundary).transpose * gram =
        (gram * boundaryCompletedMetricTransport interior column boundary).transpose := by
          rw [Matrix.transpose_mul, hgram]
    _ = target.transpose := by rw [htransport]
    _ = target := htarget

/-- The finite Hankel construction is an instance of the metric boundary
completion scheme: the single boundary index is the final monomial. -/
theorem finiteHankel_boundaryCompletedMetricTransport_eq_galerkin
    (moments : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram moments (N + 1)).PosDef) :
    boundaryCompletedMetricTransport (κ := Fin 1)
        (finiteHankelRaisingShift N)
        (fun i (_ : Fin 1) => finiteHankelGalerkinBoundaryColumn moments N i)
        (fun (_ : Fin 1) j => finiteHankelLastRow N j) =
      finiteHankelGalerkinMultiplication moments N := by
  rw [finiteHankelGalerkinMultiplication_eq_raisingShift_add_boundaryColumn
    moments N hG]
  ext i j
  simp only [boundaryCompletedMetricTransport, Matrix.add_apply,
    finiteHankelLastColumnRankOne]
  rw [Matrix.mul_apply, Fin.sum_univ_one]

end Metric

end

end CarrySelfAdjointOperator
