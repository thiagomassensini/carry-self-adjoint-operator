import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Category.ModuleCat.Basic
import CarrySelfAdjointOperator.PostT0TowerNumberDescent
import CarrySelfAdjointOperator.PrimeDepthTfvdLogJetCrosswalk

open scoped BigOperators

namespace CarrySelfAdjointOperator

open TensorProduct

noncomputable section

/-! ## Algebraic J/H coequalizer

The audited Python law is `q_jh(d_J, j) = j`: it adds coefficients over the
Jordan divisor coordinate and leaves the tower coordinate untouched.  Here
`Ctx` stands exactly for the passive provenance tuple
`(p_A, tau, flags, role)`; it intentionally contains neither `d_J` nor the
tower variables `(p_T, j)`.
-/

/-- The positive Jordan-divisor coordinate used by the audited finite model. -/
abbrev HistoricalJordanDivisor := PNat

/-- All provenance axes which the J/H coequalizer preserves. -/
abbrev HistoricalJHContext (Ctx : Type*) := Ctx

/-- Finite algebraic provenance records before the J/H coequalization. -/
abbrev HistoricalJHPreCarrier (Ctx : Type*) :=
  (HistoricalJHContext Ctx × HistoricalJordanDivisor) →₀ ℂ

/-- Finite provenance records after the Jordan-divisor coordinate is coequalized. -/
abbrev HistoricalJHQuotientCarrier (Ctx : Type*) :=
  HistoricalJHContext Ctx →₀ ℂ

/-- The historical algebraic J/H coequalizer: forget the Jordan-divisor index
and coalesce collisions by addition. -/
def historicalQJH (Ctx : Type*) :
    HistoricalJHPreCarrier Ctx →ₗ[ℂ] HistoricalJHQuotientCarrier Ctx :=
  Finsupp.lmapDomain ℂ ℂ
    (Prod.fst : HistoricalJHContext Ctx × HistoricalJordanDivisor →
      HistoricalJHContext Ctx)

/-- A basis atom has its Jordan divisor forgotten, with its coefficient
unchanged. -/
theorem historicalQJH_single
    (Ctx : Type*) (ctx : HistoricalJHContext Ctx)
    (d : HistoricalJordanDivisor) (a : ℂ) :
    historicalQJH Ctx (Finsupp.single (ctx, d) a) =
      Finsupp.single ctx a := by
  simp [historicalQJH]

/-- Coalescence law: at a fixed passive provenance context, the post-J/H
coefficient is the finite sum of all pre-J/H Jordan-divisor coefficients in
that context. -/
theorem historicalQJH_apply
    (Ctx : Type*) [DecidableEq Ctx] (x : HistoricalJHPreCarrier Ctx)
    (ctx : HistoricalJHContext Ctx) :
    historicalQJH Ctx x ctx =
      ∑ i ∈ x.support with i.1 = ctx, x i := by
  classical
  simpa [historicalQJH] using
    (Finsupp.mapDomain_apply_eq_sum
      (Prod.fst : HistoricalJHContext Ctx × HistoricalJordanDivisor →
        HistoricalJHContext Ctx)
      x
      (a := (ctx, (1 : HistoricalJordanDivisor))))

/-- Exact normalized two-divisor gauge used by the audited `q_jh` kernel
witness, before adding its independent tower leg `j = 3`. -/
def historicalJHGauge (Ctx : Type*) (ctx : HistoricalJHContext Ctx) :
    HistoricalJHPreCarrier Ctx :=
  Finsupp.single (ctx, (1 : HistoricalJordanDivisor)) (5 / 7 : ℂ) +
    Finsupp.single (ctx, (2 : HistoricalJordanDivisor)) (-(5 / 7 : ℂ))

/-- The exact historical two-divisor gauge is killed by `Q_JH`. -/
theorem historicalJHGauge_mem_ker
    (Ctx : Type*) (ctx : HistoricalJHContext Ctx) :
    historicalJHGauge Ctx ctx ∈ LinearMap.ker (historicalQJH Ctx) := by
  change historicalQJH Ctx (historicalJHGauge Ctx ctx) = 0
  rw [historicalJHGauge, LinearMap.map_add,
    historicalQJH_single, historicalQJH_single]
  ext c
  by_cases h : c = ctx
  · subst c
    simp
  · simp

/-- Surjectivity uses the legitimate historical divisor `d_J = 1`; this is a
proof of surjectivity, not a reverse section for endpoint reconstruction. -/
theorem historicalQJH_surjective (Ctx : Type*) :
    Function.Surjective (historicalQJH Ctx) := by
  intro y
  refine ⟨Finsupp.mapDomain
      (fun ctx : HistoricalJHContext Ctx =>
        (ctx, (1 : HistoricalJordanDivisor))) y, ?_⟩
  change Finsupp.mapDomain Prod.fst
      (Finsupp.mapDomain
        (fun ctx : HistoricalJHContext Ctx =>
          (ctx, (1 : HistoricalJordanDivisor))) y) = y
  rw [← Finsupp.mapDomain_comp]
  change Finsupp.mapDomain (fun ctx : HistoricalJHContext Ctx => ctx) y = y
  exact Finsupp.mapDomain_id

/-- The algebraic quotient by the J/H gauge kernel, before any Hilbert-space
completion. -/
abbrev HistoricalJHAlgebraicQuotient (Ctx : Type*) :=
  HistoricalJHPreCarrier Ctx ⧸ LinearMap.ker (historicalQJH Ctx)

/-- First-isomorphism identification of the algebraic quotient with the
historical post-J/H finite carrier. -/
noncomputable def historicalJHAlgebraicQuotientEquiv
    (Ctx : Type*) :
    HistoricalJHAlgebraicQuotient Ctx ≃ₗ[ℂ]
      HistoricalJHQuotientCarrier Ctx :=
  (historicalQJH Ctx).quotKerEquivOfSurjective
    (historicalQJH_surjective Ctx)

theorem historicalJHAlgebraicQuotientEquiv_mkQ
    (Ctx : Type*) (x : HistoricalJHPreCarrier Ctx) :
    historicalJHAlgebraicQuotientEquiv Ctx
      ((LinearMap.ker (historicalQJH Ctx)).mkQ x) =
      historicalQJH Ctx x := by
  exact (historicalQJH Ctx).quotKerEquivRange_apply_mk x

/-- Typeclass-stable module packaging of the passive pre-J/H provenance
factor.  The underlying module is exactly the finite `Finsupp` carrier above;
the packaging changes no coordinates or coefficients. -/
def historicalJHPreFactorObj (Ctx : Type*) : ModuleCat ℂ :=
  ModuleCat.of ℂ (HistoricalJHPreCarrier Ctx)

/-- Typeclass-stable module packaging of the post-J/H provenance factor. -/
def historicalJHQuotientFactorObj (Ctx : Type*) : ModuleCat ℂ :=
  ModuleCat.of ℂ (HistoricalJHQuotientCarrier Ctx)

abbrev HistoricalJHPreFactor (Ctx : Type*) := historicalJHPreFactorObj Ctx
abbrev HistoricalJHQuotientFactor (Ctx : Type*) :=
  historicalJHQuotientFactorObj Ctx

/-- The same audited J/H coequalizer, viewed between the stable factor
packages. -/
def historicalQJHFactor (Ctx : Type*) :
    HistoricalJHPreFactor Ctx →ₗ[ℂ] HistoricalJHQuotientFactor Ctx :=
  historicalQJH Ctx

/-- The existing algebraic tower carrier, independently packaged as a module
factor.  Its prime `p_T` remains a parameter of the log clock and is never
read by `Q_JH`. -/
def historicalTowerCarrierObj : ModuleCat ℂ := ModuleCat.of ℂ (ℕ → ℂ)

abbrev HistoricalTowerCarrier := historicalTowerCarrierObj

/-- The number operator `diag(j)` on the independent tower factor. -/
def historicalTowerNumber :
    HistoricalTowerCarrier →ₗ[ℂ] HistoricalTowerCarrier :=
  ProjectiveDepth.depthMultiplication

/-- The algebraic tower basis at height `j`.  This is used only by the
pre-existing `ℕ`-indexed algebraic clock; the Hilbert-scale core introduced
later uses the physical positive index `PNat`. -/
abbrev historicalTowerBasis (j : ℕ) : HistoricalTowerCarrier :=
  fun k => if k = j then 1 else 0

/-- The already established prime-power ledger identity, moved out of the
temporary probe so that the historical clock module has no `/tmp` dependency. -/
theorem historicalPrimeDepthLogLedger_primePow
    {p j : ℕ} (hp : p.Prime) :
    primeDepthLogLedger (p ^ j) =
      (j : ℝ) * Real.log p := by
  rw [primeDepthLogLedger_eq_log (pow_ne_zero j hp.ne_zero)]
  norm_num [Nat.cast_pow, Real.log_pow]

abbrev HistoricalFullPreCarrier (Ctx : Type*) :=
  HistoricalJHPreFactor Ctx ⊗[ℂ] HistoricalTowerCarrier

abbrev HistoricalFullPostCarrier (Ctx : Type*) :=
  HistoricalJHQuotientFactor Ctx ⊗[ℂ] HistoricalTowerCarrier

/-- The standard submodule quotient instance, explicit for the algebraic
tensor carrier. -/
local instance historicalFullPreCarrierHasQuotient (Ctx : Type*) :
    HasQuotient (HistoricalFullPreCarrier Ctx)
      (Submodule ℂ (HistoricalFullPreCarrier Ctx)) :=
  @Submodule.hasQuotient ℂ (HistoricalFullPreCarrier Ctx) _ _ _

/-- The historical full coequalizer is exactly `Q_JH tensor I_tower`.
The explicit additive instances keep the tensor map aligned with the canonical
group structure required by `LinearMap.ker` and `Submodule.mapQ`. -/
def historicalQFull (Ctx : Type*) :
    HistoricalFullPreCarrier Ctx →ₗ[ℂ] HistoricalFullPostCarrier Ctx :=
  @TensorProduct.map ℂ ℂ (CommRing.toCommSemiring) (CommRing.toCommSemiring)
    (RingHom.id ℂ)
    (HistoricalJHPreFactor Ctx) HistoricalTowerCarrier
    (HistoricalJHQuotientFactor Ctx) HistoricalTowerCarrier
    AddCommGroup.toAddCommMonoid AddCommGroup.toAddCommMonoid
    AddCommGroup.toAddCommMonoid AddCommGroup.toAddCommMonoid
    _ _ _ _
    (historicalQJHFactor Ctx)
    (LinearMap.id : HistoricalTowerCarrier →ₗ[ℂ] HistoricalTowerCarrier)

/-- The tower number is exactly `I_JH tensor diag(j)`. -/
def historicalTowerNumberFull (Ctx : Type*) :
    HistoricalFullPreCarrier Ctx →ₗ[ℂ] HistoricalFullPreCarrier Ctx :=
  @TensorProduct.map ℂ ℂ (CommRing.toCommSemiring) (CommRing.toCommSemiring)
    (RingHom.id ℂ)
    (HistoricalJHPreFactor Ctx) HistoricalTowerCarrier
    (HistoricalJHPreFactor Ctx) HistoricalTowerCarrier
    AddCommGroup.toAddCommMonoid AddCommGroup.toAddCommMonoid
    AddCommGroup.toAddCommMonoid AddCommGroup.toAddCommMonoid
    _ _ _ _
    (LinearMap.id : HistoricalJHPreFactor Ctx →ₗ[ℂ] HistoricalJHPreFactor Ctx)
    historicalTowerNumber

/-- Concrete historical instance of the generic tensor-kernel theorem. -/
theorem historicalQJH_towerNumber_kernel_invariant
    (Ctx : Type*) :
    LinearMap.ker (historicalQFull Ctx) ≤
      (LinearMap.ker (historicalQFull Ctx)).comap
        (historicalTowerNumberFull Ctx) := by
  simpa [historicalQFull, historicalTowerNumberFull] using
    (probe_tensor_rightMap_preserves_leftMap_ker
      (historicalQJHFactor Ctx) historicalTowerNumber)

/-- Canonical algebraic post-T0 number operator, induced on the quotient by
the kernel of the concrete historical full coequalizer. -/
noncomputable def historicalPostT0TowerNumber
    (Ctx : Type*) :
    (HistoricalFullPreCarrier Ctx ⧸ LinearMap.ker (historicalQFull Ctx)) →ₗ[ℂ]
      (HistoricalFullPreCarrier Ctx ⧸ LinearMap.ker (historicalQFull Ctx)) :=
  (LinearMap.ker (historicalQFull Ctx)).mapQ
    (LinearMap.ker (historicalQFull Ctx))
    (historicalTowerNumberFull Ctx)
    (historicalQJH_towerNumber_kernel_invariant Ctx)

/-- The first concrete historical post-T0 intertwining equation. -/
theorem historicalPostT0TowerNumber_intertwining
    (Ctx : Type*) :
    (historicalPostT0TowerNumber Ctx).comp
        (LinearMap.ker (historicalQFull Ctx)).mkQ =
        (LinearMap.ker (historicalQFull Ctx)).mkQ.comp
        (historicalTowerNumberFull Ctx) := by
  simpa [historicalPostT0TowerNumber, probe_inducedEndOfKernelStable] using
    (probe_inducedEndOfKernelStable_intertwining
      (historicalQFull Ctx)
      (historicalTowerNumberFull Ctx)
      (historicalQJH_towerNumber_kernel_invariant Ctx))

/-- The full pre-quotient logarithmic tower clock. -/
def historicalTowerLogClock (Ctx : Type*) (p : ℕ) :
    HistoricalFullPreCarrier Ctx →ₗ[ℂ] HistoricalFullPreCarrier Ctx :=
  (Real.log (p : ℝ) : ℂ) • historicalTowerNumberFull Ctx

/-- The descended logarithmic tower clock on the canonical algebraic quotient. -/
noncomputable def historicalPostT0TowerLogClock
    (Ctx : Type*) (p : ℕ) :
    (HistoricalFullPreCarrier Ctx ⧸ LinearMap.ker (historicalQFull Ctx)) →ₗ[ℂ]
      (HistoricalFullPreCarrier Ctx ⧸ LinearMap.ker (historicalQFull Ctx)) :=
  (Real.log (p : ℝ) : ℂ) • historicalPostT0TowerNumber Ctx

theorem historicalPostT0TowerLogClock_intertwining
    (Ctx : Type*) (p : ℕ) (x : HistoricalFullPreCarrier Ctx) :
    (LinearMap.ker (historicalQFull Ctx)).mkQ
        (historicalTowerLogClock Ctx p x) =
      historicalPostT0TowerLogClock Ctx p
        ((LinearMap.ker (historicalQFull Ctx)).mkQ x) := by
  simp [historicalTowerLogClock, historicalPostT0TowerLogClock,
    historicalPostT0TowerNumber]

/-- The literal `(d_J,j)=(1,3),(2,3)` gauge from the Python audit. -/
def historicalJHGaugeFactor (Ctx : Type*) (ctx : HistoricalJHContext Ctx) :
    HistoricalJHPreFactor Ctx :=
  historicalJHGauge Ctx ctx

def historicalFullJHGauge (Ctx : Type*) (ctx : HistoricalJHContext Ctx) :
    HistoricalFullPreCarrier Ctx :=
  historicalJHGaugeFactor Ctx ctx ⊗ₜ[ℂ] historicalTowerBasis 3

theorem historicalFullJHGauge_mem_ker
    (Ctx : Type*) (ctx : HistoricalJHContext Ctx) :
    historicalFullJHGauge Ctx ctx ∈ LinearMap.ker (historicalQFull Ctx) := by
  change historicalQFull Ctx (historicalFullJHGauge Ctx ctx) = 0
  rw [historicalFullJHGauge, historicalQFull, TensorProduct.map_tmul]
  have hg : historicalQJHFactor Ctx (historicalJHGaugeFactor Ctx ctx) = 0 := by
    change historicalQJH Ctx (historicalJHGauge Ctx ctx) = 0
    exact historicalJHGauge_mem_ker Ctx ctx
  rw [hg]
  simp

theorem historicalTowerNumber_basis (j : ℕ) :
    historicalTowerNumber (historicalTowerBasis j) =
      (j : ℂ) • historicalTowerBasis j := by
  funext k
  by_cases h : k = j
  · subst k
    change (j : ℂ) * (if j = j then 1 else 0) =
      (j : ℂ) * (if j = j then 1 else 0)
    simp
  · change (k : ℂ) * (if k = j then 1 else 0) =
      (j : ℂ) * (if k = j then 1 else 0)
    simp [h]

theorem historicalTowerNumberFull_tmul_basis
    (Ctx : Type*) (a : HistoricalJHPreFactor Ctx) (j : ℕ) :
    historicalTowerNumberFull Ctx (a ⊗ₜ[ℂ] historicalTowerBasis j) =
      (j : ℂ) • (a ⊗ₜ[ℂ] historicalTowerBasis j) := by
  rw [historicalTowerNumberFull, TensorProduct.map_tmul,
    historicalTowerNumber_basis]
  simp

/-- On every historical J/H provenance vector, the descended prime-power
clock has the native prime-depth eigenvalue.  This specializes the already
proved quotient intertwining; it does not reconstruct the tensor descent. -/
theorem historicalPostT0PrimePowerClock_eq_primeDepthClock
    (Ctx : Type*) {p j : ℕ} (hp : p.Prime)
    (a : HistoricalJHPreFactor Ctx) :
    (primeDepthLogLedger (p ^ j) : ℂ) •
        ((LinearMap.ker (historicalQFull Ctx)).mkQ
          (a ⊗ₜ[ℂ] historicalTowerBasis j)) =
      historicalPostT0TowerLogClock Ctx p
        ((LinearMap.ker (historicalQFull Ctx)).mkQ
          (a ⊗ₜ[ℂ] historicalTowerBasis j)) := by
  let x : HistoricalFullPreCarrier Ctx := a ⊗ₜ[ℂ] historicalTowerBasis j
  have hnumber : historicalTowerNumberFull Ctx x = (j : ℂ) • x := by
    exact historicalTowerNumberFull_tmul_basis Ctx a j
  have hintertwining := historicalPostT0TowerLogClock_intertwining Ctx p x
  calc
    (primeDepthLogLedger (p ^ j) : ℂ) •
        ((LinearMap.ker (historicalQFull Ctx)).mkQ x) =
      ((j : ℂ) * (Real.log (p : ℝ) : ℂ)) •
        ((LinearMap.ker (historicalQFull Ctx)).mkQ x) := by
          rw [historicalPrimeDepthLogLedger_primePow hp]
          congr 1
          push_cast
          ring
    _ = (LinearMap.ker (historicalQFull Ctx)).mkQ
          (((j : ℂ) * (Real.log (p : ℝ) : ℂ)) • x) := by
          rw [LinearMap.map_smul]
    _ = (LinearMap.ker (historicalQFull Ctx)).mkQ
          (historicalTowerLogClock Ctx p x) := by
          congr 1
          rw [historicalTowerLogClock, LinearMap.smul_apply, hnumber,
            smul_smul]
          congr 1
          ring
    _ = historicalPostT0TowerLogClock Ctx p
          ((LinearMap.ker (historicalQFull Ctx)).mkQ x) := hintertwining

theorem historicalPostT0PrimePowerClock_eq_j_log
    (Ctx : Type*) {p j : ℕ} (hp : p.Prime)
    (a : HistoricalJHPreFactor Ctx) :
    historicalPostT0TowerLogClock Ctx p
        ((LinearMap.ker (historicalQFull Ctx)).mkQ
          (a ⊗ₜ[ℂ] historicalTowerBasis j)) =
      ((j : ℂ) * (Real.log (p : ℝ) : ℂ)) •
        ((LinearMap.ker (historicalQFull Ctx)).mkQ
          (a ⊗ₜ[ℂ] historicalTowerBasis j)) := by
  calc
    historicalPostT0TowerLogClock Ctx p
        ((LinearMap.ker (historicalQFull Ctx)).mkQ
          (a ⊗ₜ[ℂ] historicalTowerBasis j)) =
      (primeDepthLogLedger (p ^ j) : ℂ) •
        ((LinearMap.ker (historicalQFull Ctx)).mkQ
          (a ⊗ₜ[ℂ] historicalTowerBasis j)) :=
      (historicalPostT0PrimePowerClock_eq_primeDepthClock Ctx hp a).symm
    _ = ((j : ℂ) * (Real.log (p : ℝ) : ℂ)) •
        ((LinearMap.ker (historicalQFull Ctx)).mkQ
          (a ⊗ₜ[ℂ] historicalTowerBasis j)) := by
      rw [historicalPrimeDepthLogLedger_primePow hp]
      congr 1
      push_cast
      ring


end

end CarrySelfAdjointOperator
