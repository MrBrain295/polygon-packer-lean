module

public import PolygonPackerProofs.Interval

/-!
# Soundness of the enclosures of `π`, `cos` and `sin`
-/

@[expose] public section

namespace PolygonPacker

open Complex

lemma fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, ih, Nat.factorial_succ]

lemma pi_mem : Ival.Mem Real.pi piIval := by
  unfold Ival.Mem piIval
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · push_cast; norm_num at h1 ⊢; linarith
  · push_cast; norm_num at h2 ⊢; linarith

private lemma term_eq (r : ℚ) (j : ℕ) :
    (((r : ℂ) * I) ^ j / (j.factorial : ℂ)) =
      ((cosTerm r j : ℚ) : ℝ) + ((sinTerm r j : ℚ) : ℝ) * I := by
  have hI : I ^ j = I ^ (j % 4) := pow_eq_pow_mod j I_pow_four
  rw [mul_pow, hI]
  have h4 : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold cosTerm sinTerm
  rw [fact_eq]
  interval_cases h : j % 4 <;> simp <;> ring_nf

lemma taylor_eq (n : ℕ) (r : ℚ) :
    (∑ m ∈ Finset.range n, ((r : ℂ) * I) ^ m / (m.factorial : ℂ)) =
      ((cosTaylor n r : ℚ) : ℝ) + ((sinTaylor n r : ℚ) : ℝ) * I := by
  induction n with
  | zero => simp [cosTaylor, sinTaylor]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, term_eq]
    simp only [cosTaylor, sinTaylor, List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    push_cast; ring

private lemma qabs_cast (q : ℚ) : ((qabs q : ℚ) : ℝ) = |(q : ℝ)| := by
  unfold qabs
  split_ifs with h
  · have : (q : ℝ) < 0 := by exact_mod_cast h
    rw [abs_of_neg this]; push_cast; ring
  · have : (0 : ℝ) ≤ q := by exact_mod_cast not_lt.mp h
    rw [abs_of_nonneg this]

/-- `expBox T` encloses `exp (t * I)` for every `t ∈ T`. -/
theorem expBox_sound {t : ℝ} {T : Ival} (ht : Ival.Mem t T) :
    Box.Mem (exp (t * I)) (expBox T) := by
  unfold expBox
  simp only
  split_ifs with hc
  · set r : ℚ := (T.lo + T.hi) / 2
    set η : ℚ := (T.hi - T.lo) / 2
    set n := taylorTerms
    have hc' : 2 * |(r : ℝ)| ≤ (n + 1 : ℕ) := by
      rw [← qabs_cast]; exact_mod_cast hc
    -- distance from `t` to the midpoint
    have hη : |t - r| ≤ η := by
      obtain ⟨h1, h2⟩ := ht
      simp only [r, η]; push_cast
      rw [abs_le]; constructor <;> linarith
    have hlip : ‖exp (t * I) - exp ((r : ℝ) * I)‖ ≤ η := by
      have : exp (t * I) - exp ((r : ℝ) * I) =
          exp ((r : ℝ) * I) * (exp (I * ((t - r : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
      rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (by simpa [Real.norm_eq_abs] using hη)
    have htay := Complex.exp_bound' (x := ((r : ℂ) * I)) (n := n) (by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ratCast]
      rw [div_le_iff₀ (by positivity)]
      push_cast at hc' ⊢; linarith)
    rw [taylor_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_ratCast] at htay
    have hexp : ((r : ℂ) * I) = (((r : ℝ)) : ℂ) * I := by push_cast; rfl
    rw [hexp] at htay
    set C : ℝ := ((cosTaylor n r : ℚ) : ℝ) with hC
    set Sn : ℝ := ((sinTaylor n r : ℚ) : ℝ) with hS
    set e : ℚ := qabs r ^ n / (fact n : ℚ) * 2 + η with he_def
    have he : ((e : ℚ) : ℝ) = |(r : ℝ)| ^ n / (n.factorial : ℝ) * 2 + η := by
      rw [he_def]; push_cast [qabs_cast, fact_eq]; ring
    have htot : ‖exp (t * I) - (C + Sn * I)‖ ≤ (e : ℝ) := by
      rw [he]
      exact (norm_sub_le_norm_sub_add_norm_sub _ (exp ((r : ℝ) * I)) _).trans (by linarith)
    have hre := (Complex.abs_re_le_norm (exp (t * I) - (C + Sn * I))).trans htot
    have him := (Complex.abs_im_le_norm (exp (t * I) - (C + Sn * I))).trans htot
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
      Complex.mul_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hre him
    rw [abs_le] at hre him
    constructor
    · apply Ival.mem_round
      unfold Ival.Mem
      simp only [Rat.cast_sub, Rat.cast_add]
      constructor <;> linarith [hre.1, hre.2]
    · apply Ival.mem_round
      unfold Ival.Mem
      simp only [Rat.cast_sub, Rat.cast_add]
      constructor <;> linarith [him.1, him.2]
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.neg_one_le_cos, Real.cos_le_one, Real.neg_one_le_sin,
      Real.sin_le_one]

end PolygonPacker
