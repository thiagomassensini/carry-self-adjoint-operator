import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! A finite-dimensional, source-independent comparison bound for the
Hermitian moment forms.  The hypotheses control every coefficient; the
conclusion keeps all off-diagonal crossings. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- The real value of the complex Hankel pairing. -/
def complexSourceMomentForm (m : ℕ → ℝ) (s N : ℕ) (x : Fin N → ℂ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    (star (x i) * x j).re * m (i.val + j.val + s)

def c2ErrorA0 {N : ℕ} (x : Fin N → ℂ) : ℝ :=
  ∑ i : Fin N, (16 : ℝ)^i.val * ‖x i‖

def c2ErrorA1 {N : ℕ} (x : Fin N → ℂ) : ℝ :=
  ∑ i : Fin N, (i.val : ℝ) * (16 : ℝ)^i.val * ‖x i‖

/-- On real inputs the Hermitian form is exactly the existing native
`sourceMomentQuadratic`; the comparison theorem therefore applies directly
to the all-order source form. -/
theorem complexSourceMomentForm_ofReal (m : ℕ → ℝ) (s N : ℕ)
    (x : Fin N → ℝ) :
    complexSourceMomentForm m s N (fun i => (x i : ℂ)) =
      sourceMomentQuadratic m s N x := by
  simp only [complexSourceMomentForm, sourceMomentQuadratic, sourceMomentMatrix,
    Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.conj_ofReal]
  ring

private theorem complex_cross_abs (u v : ℂ) :
    |(star u * v).re| ≤ ‖u‖ * ‖v‖ := by
  calc
    |(star u * v).re| ≤ ‖star u * v‖ := Complex.abs_re_le_norm _
    _ = ‖u‖ * ‖v‖ := by simp

/-- Coefficientwise jet control implies a quantitative bound for the whole
complex Hankel form, including every cross term. -/
theorem complexSourceMomentForm_error_lower
    (m mt : ℕ → ℝ) (s N : ℕ) (η : ℝ)
    (hm : ∀ j, |m j - mt j| ≤ ((j+1 : ℕ) : ℝ) *
      (16 : ℝ)^(j+1) * η) (x : Fin N → ℂ) :
    complexSourceMomentForm m s N x ≥ complexSourceMomentForm mt s N x -
      (16 : ℝ)^(s+1) * η *
        (((s+1 : ℕ) : ℝ) * (c2ErrorA0 x)^2 +
          2 * c2ErrorA0 x * c2ErrorA1 x) := by
  classical
  let w : Fin N → ℝ := fun i => (16 : ℝ)^i.val * ‖x i‖
  have hc (i j : Fin N) :
      |(star (x i) * x j).re * (m (i.val+j.val+s)-mt (i.val+j.val+s))| ≤
        (16 : ℝ)^(s+1) * η * w i * w j *
          ((s+1 : ℕ) + i.val + j.val : ℕ) := by
    have hcross := complex_cross_abs (x i) (x j)
    have hcoef := hm (i.val+j.val+s)
    have hpow : (16 : ℝ)^(i.val+j.val+s+1) =
        (16 : ℝ)^(s+1) * (16 : ℝ)^i.val * (16 : ℝ)^j.val := by
      rw [show i.val+j.val+s+1 = (s+1)+i.val+j.val by omega, pow_add, pow_add]
    rw [abs_mul]
    calc
      |(star (x i) * x j).re| * |m (i.val+j.val+s)-mt (i.val+j.val+s)|
          ≤ (‖x i‖ * ‖x j‖) *
            (((i.val+j.val+s+1 : ℕ) : ℝ) *
              (16 : ℝ)^(i.val+j.val+s+1) * η) := by
                exact mul_le_mul hcross hcoef (abs_nonneg _) (by positivity)
      _ = (16 : ℝ)^(s+1) * η * w i * w j *
          ((s+1 : ℕ) + i.val + j.val : ℕ) := by
            dsimp [w]
            rw [hpow]
            push_cast
            ring
  have hsum :
      |∑ i : Fin N, ∑ j : Fin N,
          (star (x i) * x j).re * (m (i.val+j.val+s)-mt (i.val+j.val+s))| ≤
        ∑ i : Fin N, ∑ j : Fin N,
          ((16 : ℝ)^(s+1) * η * w i * w j *
            ((s+1 : ℕ) + i.val + j.val : ℕ)) := by
    calc
      _ ≤ ∑ i : Fin N, |∑ j : Fin N,
          (star (x i) * x j).re * (m (i.val+j.val+s)-mt (i.val+j.val+s))| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, ∑ j : Fin N,
          |(star (x i) * x j).re * (m (i.val+j.val+s)-mt (i.val+j.val+s))| := by
            apply Finset.sum_le_sum
            intro i hi
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            exact hc i j
  have hfactor :
      (∑ i : Fin N, ∑ j : Fin N,
          w i * w j * ((s+1 : ℕ) + i.val + j.val : ℕ)) =
        ((s+1 : ℕ) : ℝ) * (∑ i, w i)^2 +
          2 * (∑ i, w i) * (∑ i, (i.val : ℝ) * w i) := by
    have hterm (i j : Fin N) :
        w i * w j * ((s+1 : ℕ) + i.val + j.val : ℕ) =
          ((s+1 : ℕ) : ℝ) * (w i*w j) +
            ((i.val : ℝ)*w i)*w j + w i*((j.val : ℝ)*w j) := by
      push_cast
      ring
    have h00 : (∑ i : Fin N, ∑ j : Fin N, w i*w j) = (∑ i, w i)^2 := by
      simpa [pow_two] using (Fintype.sum_mul_sum w w).symm
    have h10 : (∑ i : Fin N, ∑ j : Fin N, ((i.val : ℝ)*w i)*w j) =
        (∑ i, (i.val : ℝ)*w i) * (∑ j, w j) := by
      exact (Fintype.sum_mul_sum (fun i : Fin N => (i.val : ℝ)*w i) w).symm
    have h01 : (∑ i : Fin N, ∑ j : Fin N, w i*((j.val : ℝ)*w j)) =
        (∑ i, w i) * (∑ j, (j.val : ℝ)*w j) := by
      exact (Fintype.sum_mul_sum w (fun j : Fin N => (j.val : ℝ)*w j)).symm
    have hc : (∑ i : Fin N, ∑ j : Fin N,
        ((s+1 : ℕ) : ℝ) * (w i*w j)) =
        ((s+1 : ℕ) : ℝ) * (∑ i, w i)^2 := by
      calc
        _ = ((s+1 : ℕ) : ℝ) * (∑ i : Fin N, ∑ j : Fin N, w i*w j) := by
          simp only [← Finset.mul_sum]
        _ = _ := by rw [h00]
    calc
      _ = ∑ i : Fin N, ∑ j : Fin N,
          (((s+1 : ℕ) : ℝ) * (w i*w j) +
            ((i.val : ℝ)*w i)*w j + w i*((j.val : ℝ)*w j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              exact hterm i j
      _ = (∑ i : Fin N, ∑ j : Fin N, ((s+1 : ℕ) : ℝ) * (w i*w j)) +
          (∑ i : Fin N, ∑ j : Fin N, ((i.val : ℝ)*w i)*w j) +
          (∑ i : Fin N, ∑ j : Fin N, w i*((j.val : ℝ)*w j)) := by
            simp only [Finset.sum_add_distrib]
      _ = ((s+1 : ℕ) : ℝ) * (∑ i, w i)^2 +
          (∑ i, (i.val : ℝ)*w i) * (∑ j, w j) +
          (∑ i, w i) * (∑ j, (j.val : ℝ)*w j) := by
            rw [hc, h10, h01]
      _ = _ := by ring
  have hsum' :
      (∑ i : Fin N, ∑ j : Fin N,
          ((16 : ℝ)^(s+1) * η * w i * w j *
            ((s+1 : ℕ) + i.val + j.val : ℕ))) =
        (16 : ℝ)^(s+1) * η *
          (((s+1 : ℕ) : ℝ) * (∑ i, w i)^2 +
            2 * (∑ i, w i) * (∑ i, (i.val : ℝ) * w i)) := by
    calc
      _ = ∑ i : Fin N, ∑ j : Fin N,
          (16 : ℝ)^(s+1) * η *
            (w i * w j * ((s+1 : ℕ) + i.val + j.val : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (16 : ℝ)^(s+1) * η *
          ∑ i : Fin N, ∑ j : Fin N, w i * w j *
            ((s+1 : ℕ) + i.val + j.val : ℕ) := by
              simp only [Finset.mul_sum]
      _ = (16 : ℝ)^(s+1) * η *
          (((s+1 : ℕ) : ℝ) * (∑ i, w i)^2 +
            2 * (∑ i, w i) * (∑ i, (i.val : ℝ) * w i)) := by
              rw [hfactor]
  have hrewrite :
      complexSourceMomentForm m s N x - complexSourceMomentForm mt s N x =
        ∑ i : Fin N, ∑ j : Fin N,
          (star (x i) * x j).re * (m (i.val+j.val+s)-mt (i.val+j.val+s)) := by
    simp only [complexSourceMomentForm]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hbound := hsum.trans_eq hsum'
  rw [← hrewrite] at hbound
  have habs := (abs_le.mp hbound).1
  have hA0 : c2ErrorA0 x = ∑ i : Fin N, w i := by rfl
  have hA1 : c2ErrorA1 x = ∑ i : Fin N, (i.val : ℝ)*w i := by
    unfold c2ErrorA1 w
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hA0, hA1]
  linarith

end
end CarrySelfAdjointOperator
