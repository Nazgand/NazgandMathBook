import analysis.special_functions.trigonometric.basic
import analysis.special_functions.exponential
import analysis.special_functions.complex.log
import algebra.group_with_zero.defs

open classical complex asymptotics real normed_space
open_locale classical big_operators nat

lemma expTsumForm (z:ℂ) : exp z = tsum (λ (k:ℕ), z ^ k / k.factorial):=
begin
  rw [exp_eq_exp_ℂ, exp_eq_tsum_div],
end

-- rues is the Root of Unity Exponential Sum function 
-- inspired by the relationship between exp and cosh
noncomputable
def rues (n:ℕ) (z:ℂ) : ℂ :=
  tsum (λ (k:ℕ), z ^ (n*k) / (n*k).factorial)

lemma ruesSummable (n:ℕ) (z:ℂ) : summable (λ (k:ℕ), z ^ (n*k) / (n*k).factorial):=
begin
  rw [summable],
  sorry,
end

lemma imagPartsOfSumEqSumOfImagParts (f:ℕ→ℂ) (hf:summable f):
      im (∑' (k : ℕ), f k) = (∑' (k : ℕ), im (f k)):=
begin
  let h:= continuous_linear_map.map_tsum complex.im_clm hf,
  continuity,
end

lemma realPartsOfSumEqSumOfRealParts (f:ℕ→ℂ) (hf:summable f):
      re (∑' (k : ℕ), f k) = (∑' (k : ℕ), re (f k)):=
begin
  let h:= continuous_linear_map.map_tsum complex.re_clm hf,
  continuity,
end

lemma ruesRealToReal (n:ℕ) (h:n>0) (x:ℝ) : (rues n x).im = 0 :=
begin
  rw [rues, imagPartsOfSumEqSumOfImagParts],
  {
    suffices h : ∑' (k : ℕ), im (↑x ^ (n * k) / ↑(n * k)!) = ∑' (k : ℕ), 0,
    simp only [tsum_zero, h],
    congr' 1,
    ext1,
    sorry,
  },
  exact ruesSummable n x,
end

lemma cpowIntExponentSplitBase (z1 z2:ℂ) (n:ℕ) : (z1 * z2) ^ n = z1 ^ n * z2 ^ n:=
begin
  induction n with n ih,
  simp only [pow_zero, mul_one],
  rw [pow_succ,pow_succ,pow_succ],
  have h: z1 * z1 ^ n * (z2 * z2 ^ n) = z1 * z2 * (z1 ^ n * z2 ^ n),
    ring,
  rw h,
  congr' 1,
end

lemma cpowIntExponentSplitExponent (z1:ℂ) (n k:ℕ) : z1 ^ (n + k) = z1 ^ n * z1 ^ k:=
begin
  induction k with k ih,
  simp only [add_zero, pow_zero, mul_one],
  have h: k.succ =  k + 1,
  simp only [eq_self_iff_true],
  rw [pow_succ, h],
  have h2: n + (k + 1) = (n+k)+1,
  simp only [add_comm, add_assoc],
  rw h2,
  have h3: n + k + 1=(n + k).succ,
  simp only [eq_self_iff_true],
  rw [h3, pow_succ],
  have h4: z1 ^ n * (z1 * z1 ^ k) = z1 * (z1 ^ n * z1 ^ k),
  ring,
  rw h4,
  congr' 1,
end

lemma cpowIntTimesIntExponent (z1:ℂ) (n k:ℕ) : z1 ^ (n * k) = (z1 ^ n) ^ k:=
begin
  induction k with k ih,
  simp only [mul_zero, pow_zero],
  rw [pow_succ],
  have h: n * k.succ = n*(k+1),
    simp only [eq_self_iff_true],
  rw h,
  have h2: n * (k + 1) = n+n*k,
    ring,
  rw h2,
  have h3:z1 ^ (n + n * k) = z1 ^ n * z1 ^ (n * k),
    exact cpowIntExponentSplitExponent z1 n (n * k),
    rw h3,
  congr' 1,
end

lemma ruesRotationallySymmetric (n:ℕ) (h:n>0) (z rou:ℂ) (h:rou ^ n = 1):rues n z=rues n (z*rou):=
begin
  rw [rues, rues],
  congr' 1,
  ext1,
  have h2: (z * rou) ^ (n * x) = z ^ (n * x) * rou ^ (n * x),
    exact cpowIntExponentSplitBase z rou (n * x),
  have h3: rou ^ (n * x) = (rou ^ n) ^ x,
    exact cpowIntTimesIntExponent rou n x,
  simp [h2,h3,h],
end

-- The zero coefficients are needed for proof of ruesNEqExpSum
-- m=0 is same as rues, ruesDiff is the mth derivative of rues
noncomputable
def ruesDiff (n:ℕ) (m:ℤ) (z:ℂ) : ℂ :=
  tsum (λ (k:ℕ), if ((k:ℤ)+m)%n=0 then z ^ k / k.factorial else 0)

-- The sums need to be stretched with additional zero coefficients general form
lemma tsum_mul_ite {α} [topological_space α] [t2_space α] [add_comm_monoid α]
  (f : ℕ → α) {n : ℕ} (h : 0 < n) :
  ∑' (k : ℕ), f (n * k) = ∑' (k : ℕ), ite (n ∣ k) (f k) 0 :=
begin
  rw [(show ∑' (c : ℕ), f (n * c) = ∑' (a : set.range ((*) n)), f ↑a, from
    (equiv.of_injective ((*) n) (nat.mul_right_injective h)).tsum_eq (λ a, f a.val)), tsum_subtype],
  exact tsum_congr (λ a, by simp [set.indicator, has_dvd.dvd, eq_comm]),
end

-- The sums need to be stretched with additional zero coefficients specific form
lemma needZeroCoeff (f:ℕ→ℂ) (n:ℕ) (h : n>0) : ∑' (k : ℕ), f (n * k) = ∑' (k : ℕ), ite (n ∣ k) (f k) 0 :=
tsum_mul_ite _ h

lemma ruesDiffM0EqRues_first_try (n:ℕ) (h:n>0) (z:ℂ) : rues n z = ruesDiff n 0 z :=
begin
  rw [rues, ruesDiff],
  simp, -- nontermal simps are bad; squeeze it to see the names of what you're using, you might learn something
  -- Let's isolate the problem
  convert needZeroCoeff (λ n, z ^ n / n!) n h,
  ext1, -- cancel lambdas
  congr' 1, -- cancel ITEs
  apply propext, -- make equality of propositions into an iff
  -- the problem is now isolated. Now let's solve it
  exact int.coe_nat_dvd, -- library_search found it (and might have found it quicker had
  -- you not done `import all` but I'm not sure)
end

-- second go now we know the name of the lemma
lemma ruesDiffM0EqRues (n:ℕ) (h:n>0) (z:ℂ) : rues n z = ruesDiff n 0 z :=
begin
  simp only [rues, ruesDiff, add_zero, euclidean_domain.mod_eq_zero,
    int.coe_nat_dvd, needZeroCoeff (λ n, z ^ n / n!) n h],
end

lemma ruesDiffMPeriodic (n:ℕ) (m k:ℤ) (z:ℂ) : ruesDiff n m z = ruesDiff n (m+k*n) z :=
begin
  rw [ruesDiff, ruesDiff],
  congr' 1,
  ext1,
  congr' 1,
  apply propext,
  have h : (↑x + m) % ↑n = ((↑x + m) + k * ↑n) % ↑n,
    rw int.add_mul_mod_self,
  rw h,
  ring_nf,
end

lemma ruesDiffHasDeriv (n:ℕ) (m:ℤ) (z:ℂ) : has_deriv_at (ruesDiff n m) (ruesDiff n (m+1) z) z :=
begin
  rw [has_deriv_at_iff_is_o_nhds_zero],
  refine is_o_iff_forall_is_O_with.mpr _,
  intros c cGt0,
  rw [asymptotics.is_O_with, filter.eventually],
  simp only [algebra.id.smul_eq_mul, complex.norm_eq_abs],
  
  sorry,
end

lemma ruesDiffDeriv (n:ℕ) (m:ℤ) (z:ℂ) : deriv (ruesDiff n m) z = ruesDiff n (m+1) z :=
begin
  rw (ruesDiffHasDeriv n m z).deriv,
end

open finset

lemma exp_pi_mul_I_half : exp (↑real.pi * I / 2) = I :=
begin
  -- would rather the /2 is real
  rw (show (real.pi : ℂ) * I / 2 = (real.pi / 2 : ℝ) * I, by {simp, ring, } ),
  -- now apply Euler, which was bound to be there in some form
  rw exp_mul_I,
  -- now hope simplifier knows all the facts about cos(pi/2) etc.
  simp only [of_real_div, of_real_bit0, of_real_one, complex.cos_pi_div_two, complex.sin_pi_div_two, one_mul, zero_add],
  -- it does!
end

lemma expToPowersOfI (k:ℕ): exp (↑real.pi * I * k / 2) = I^k :=
begin
  induction k with k ih,
  simp only [nat.cast_zero, zero_div, mul_zero, complex.exp_zero, pow_zero],
  rw [pow_succ],
  have h1: k.succ = k + 1,
    exact rfl,
  rw h1,
  have h2: ↑real.pi * I * ↑(k + 1) = ↑real.pi * I + ↑real.pi * I * ↑(k),
    ring_nf,
    congr' 1,
    congr' 1,
    exact nat.cast_succ k,
  rw h2,
  have h3: (↑real.pi * I + ↑real.pi * I * ↑k) / 2 = ↑real.pi * I / 2 + ↑real.pi * I * ↑k / 2,
    ring_nf,
  rw h3,
  rw exp_add (↑real.pi * I / 2) (↑real.pi * I * ↑k / 2),
  congr' 1,
  exact exp_pi_mul_I_half,
end

lemma expPowEqExpMul (z:ℂ) (n : ℕ) : exp (z) ^ n = exp (z * n) :=
begin
  induction n with n ih,
  simp only [pow_zero, nat.cast_zero, mul_zero, complex.exp_zero],
  rw [pow_succ],
  rw (show (n.succ:ℂ) = n + 1, by {simp} ),
  rw (show (z * (n + 1)) = z + z * n, by {ring} ),
  rw complex.exp_add z _,
  congr,
  exact ih,
end

lemma ruGeomSumEqIte (n k:ℕ) (h:n>0) (z:ℂ) :
    ∑ m in range n, (complex.exp (2 * real.pi * (k / n) * I)) ^ m = ite (n ∣ k) n 0 :=
begin
  have h: n ∣ k ∨ ¬n ∣ k,
  exact classical.em (n ∣ k),
  cases h,
  {
    have h2 : ∑ (m : ℕ) in range n, exp (2 * ↑real.pi * (↑k / ↑n) * I) ^ m = 
              ∑ (m : ℕ) in range n, 1,
    congr,
    ext1,
    obtain ⟨m, rfl⟩ := h_1, -- need to replace k with a multiple of n to proceed
    have h3: ↑(n * m) / ↑n = (m:ℂ),
    rw nat.cast_mul n m,
    ring_nf,
    field_simp,
    rw mul_div_cancel,
    exact_mod_cast h.lt.ne.symm,
    rw h3,
    let h4:= expToPowersOfI (4*m),
    simp only [nat.cast_mul, nat.cast_bit0, nat.cast_one] at h4,
    rw (show ↑real.pi * I * (4 * ↑m) / 2 = 2 * ↑real.pi * ↑m * I, by ring) at h4,
    rw h4,
    rw cpowIntTimesIntExponent I 4 m,
    simp only [I_pow_bit0, neg_one_sq, one_pow],
    rw h2,
    simp only [sum_const, card_range, nat.smul_one_eq_coe],
    rw if_pos h_1, -- need to evaluate ite with h_1
  },
  {
    rw geom_sum_eq,
    rw if_neg h_1,
    rw expPowEqExpMul _ n,
    rw (show 2 * ↑real.pi * (↑k / ↑n) * I * ↑n = 2 * ↑real.pi * ↑k * I  * ↑n / ↑n, by {field_simp}),
    rw mul_div_cancel,
    let h5:= expToPowersOfI (4*k),
    simp only [nat.cast_mul, nat.cast_bit0, nat.cast_one] at h5,
    rw (show ↑real.pi * I * (4 * ↑k) / 2 = 2 * ↑real.pi * ↑k * I, by ring) at h5,
    rw h5,
    rw cpowIntTimesIntExponent I 4 k,
    simp only [I_pow_bit0, neg_one_sq, one_pow, sub_self, zero_div],
    exact_mod_cast h.lt.ne.symm,
    intro eq1,
    apply h_1,
    obtain ⟨m, he⟩ := complex.exp_eq_one_iff.1 eq1,
    rw ← int.coe_nat_dvd, use ↑m,
    rw (show 2 * ↑real.pi * (↑k / ↑n) * I = (↑k / ↑n) * (2 * ↑real.pi * I), by ring) at he,
    have h6: 2 * ↑real.pi * I ≠ 0,
    apply mul_ne_zero,
    apply mul_ne_zero,
    norm_num,
    norm_cast,
    exact real.pi_ne_zero,
    exact I_ne_zero,
    let h7:= mul_right_cancel₀ h6 he,
    let h8:= congr_arg (λ(z2:ℂ),z2*n) h7,
    simp only [mul_eq_mul_left_iff, nat.cast_eq_zero] at h8,
    field_simp at h8,
    rw mul_div_cancel at h8,
    rw (show (m:ℂ) * (n:ℂ) = (n:ℂ) * (m:ℂ), by ring) at h8,
    exact_mod_cast h8,
    exact_mod_cast h.lt.ne.symm,
  },
end

lemma ruesNEqExpSum (n:ℕ) (h:n>0) (z:ℂ) :
    rues n z = (∑ m in range n, exp (z * exp (2 * real.pi * (m / n) * I)))/n :=
begin
  sorry,
end

lemma rues1EqExp (z:ℂ) : rues 1 z = exp z :=
begin
  rw [expTsumForm z, rues],
  simp,
end

lemma rues2EqCosh (z:ℂ) : rues 2 z = cosh z :=
begin
  rw [complex.cosh, ruesNEqExpSum],
  rw finset.sum,
  simp only [range_coe, multiset.range_succ, multiset.range_zero, nat.cast_bit0, nat.cast_one, multiset.map_cons, one_div,
  nat.cast_zero, zero_div, mul_zero, zero_mul, complex.exp_zero, mul_one, multiset.map_zero, multiset.sum_cons,
  multiset.sum_zero, add_zero],
  rw exp_mul_I,
  rw (show 2 * ↑real.pi * (2:ℂ)⁻¹ = ↑real.pi, by ring),
  simp only [complex.cos_pi, complex.sin_pi, zero_mul, add_zero, mul_neg, mul_one],
  ring,
  norm_num,
end

lemma rues4EqCoshCosh (z:ℂ) : rues 4 z = cosh (z/(1+I)) * cosh (z/(1-I)) :=
begin
  rw [complex.cosh, complex.cosh, ruesNEqExpSum],
  rw finset.sum,
  simp only [range_coe, multiset.range_succ, multiset.range_zero, nat.cast_bit0, nat.cast_one, multiset.map_cons, nat.cast_bit1,
  one_div, nat.cast_zero, zero_div, mul_zero, complex.exp_zero, mul_one, multiset.map_zero, multiset.sum_cons,
  multiset.sum_zero, add_zero],
  {
    rw [exp_mul_I, exp_mul_I, exp_mul_I],
    simp only [zero_mul, complex.exp_zero, mul_one],
    rw (show 2 * ↑real.pi * 4⁻¹ = (real.pi/2:ℂ), by ring),
    simp only [complex.cos_pi_div_two, complex.sin_pi_div_two, one_mul, zero_add],
    rw (show (2:ℂ) * ↑real.pi * (2 / 4) = ↑real.pi, by ring),
    simp only [complex.cos_pi, complex.sin_pi, zero_mul, add_zero, mul_neg, mul_one],
    rw (show 2 * ↑real.pi * (3 / 4) = (3/2*real.pi:ℂ), by ring),
    rw (exp_mul_I _).symm,
    let h:=expToPowersOfI 3,
    rw (show (3:ℂ) / 2 * ↑real.pi * I = ↑real.pi * I * ↑3 / 2, by {simp, ring}),
    rw h,
    simp only [I_pow_bit1, pow_one, neg_mul, one_mul, mul_neg],
    ring_nf,
    have hinv1: (-I + 1)⁻¹ = (I + 1)/2,
      rw [complex.inv_def, norm_sq],
      simp only [map_add, conj_neg_I, map_one, monoid_with_zero_hom.coe_mk, add_re, neg_re, I_re, neg_zero', one_re, zero_add, mul_one,
      add_im, neg_im, I_im, one_im, add_zero, mul_neg, neg_neg, of_real_inv, of_real_add, of_real_one],
      congr' 1,
    rw hinv1,
    have hinv2: (I + 1)⁻¹ = (-I + 1)/2,
      rw [complex.inv_def, norm_sq, star_ring_end],
      simp only [ring_equiv.coe_to_ring_hom, star_ring_aut_apply, is_R_or_C.star_def, map_add, conj_I, map_one,
  monoid_with_zero_hom.coe_mk, add_re, I_re, one_re, zero_add, mul_one, add_im, I_im, one_im, add_zero, of_real_inv,
  of_real_add, of_real_one],
      congr' 1,
    rw hinv2,
    rw (show (1 / 4 * exp ((I + 1) / 2 * z) + 1 / 4 * exp (-((I + 1) / 2 * z))) * exp ((-I + 1) / 2 * z) =
    1 / 4 * exp ((I + 1) / 2 * z) * exp ((-I + 1) / 2 * z) + 1 / 4 * exp (-((I + 1) / 2 * z)) * exp ((-I + 1) / 2 * z), by {ring}),
    rw (show 1 / 4 * exp ((I + 1) / 2 * z) * exp ((-I + 1) / 2 * z) =
        1 / 4 * (exp ((I + 1) / 2 * z) * exp ((-I + 1) / 2 * z)), by {ring}),
    rw [(complex.exp_add _ _).symm],
    rw (show (I + 1) / 2 * z + (-I + 1) / 2 * z = z, by {ring}),
    rw (show 1 / 4 * exp (-((I + 1) / 2 * z)) * exp ((-I + 1) / 2 * z) =
            1 / 4 * (exp (-((I + 1) / 2 * z)) * exp ((-I + 1) / 2 * z)), by {ring}),
    rw [(complex.exp_add _ _).symm],
    rw (show -((I + 1) / 2 * z) + (-I + 1) / 2 * z = -I * z, by {ring}),
    rw (show (1 / 4 * exp ((I + 1) / 2 * z) + 1 / 4 * exp (-((I + 1) / 2 * z))) * exp (-((-I + 1) / 2 * z)) =
            1 / 4 * exp ((I + 1) / 2 * z) * exp (-((-I + 1) / 2 * z)) + 1 / 4 * exp (-((I + 1) / 2 * z)) * exp (-((-I + 1) / 2 * z)), by {ring}),
    rw (show 1 / 4 * exp ((I + 1) / 2 * z) * exp (-((-I + 1) / 2 * z)) =
            1 / 4 * (exp ((I + 1) / 2 * z) * exp (-((-I + 1) / 2 * z))), by {ring}),
    rw [(complex.exp_add _ _).symm],
    rw (show (I + 1) / 2 * z + -((-I + 1) / 2 * z) = I*z, by {ring}),
    rw (show 1 / 4 * exp (-((I + 1) / 2 * z)) * exp (-((-I + 1) / 2 * z)) =
            1 / 4 * (exp (-((I + 1) / 2 * z)) * exp (-((-I + 1) / 2 * z))), by {ring}),
    rw [(complex.exp_add _ _).symm],
    ring_nf,
  },
  norm_num,
end