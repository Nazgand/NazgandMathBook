import all
import ruesDiffDeriv

open classical complex asymptotics real normed_space finset
open_locale classical big_operators nat

-- Help received from https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/definition.20of.20exp.20using.20tsum
lemma expTsumForm (z:ℂ) : exp z = tsum (λ (k:ℕ), z ^ k / k.factorial):=
begin
  rw [exp_eq_exp_ℂ, exp_eq_tsum_div],
end

lemma expTaylorSeriesSummable (z:ℂ) : summable (λ (k:ℕ), z ^ k / k.factorial):=
begin
  exact (exp_series_div_summable ℂ z)
end

lemma expNegInv (z:ℂ) : exp z = (exp (-z))⁻¹:=
begin
  have h0 := (-z).exp_neg,
  simp only [neg_neg] at h0,
  exact h0,
end

-- rues is the Root of Unity Exponential Sum function 
-- inspired by the relationship between exp and cosh
noncomputable
def rues (n:ℕ) (z:ℂ) : ℂ :=
  tsum (λ (k:ℕ), z ^ (n*k) / (n*k).factorial)

-- Help received from https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Showing.20a.20sum.20is.20summable
lemma ruesSummable (n:ℕ) (h:0<n) (z:ℂ) : summable (λ (k:ℕ), z ^ (n*k) / (n*k).factorial):=
(exp_series_div_summable ℂ z).comp_injective (strict_mono_mul_left_of_pos h).injective

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

lemma ruesRealToReal (n:ℕ) (h:0<n) (x:ℝ) : (rues n x).im = 0 :=
begin
  rw [rues, imagPartsOfSumEqSumOfImagParts],
  {
    suffices h : ∑' (k : ℕ), im (↑x ^ (n * k) / ↑(n * k)!) = ∑' (k : ℕ), 0,
    simp only [tsum_zero, h],
    congr' 1,
    ext1,
    norm_cast at *,
  },
  exact ruesSummable n h x,
end

lemma ruesRotationallySymmetric (n:ℕ) (h₀:0<n) (z rou:ℂ) (h₁:rou ^ n = 1):rues n z=rues n (z*rou):=
begin
  rw [rues, rues],
  congr' 1,
  ext1,
  have h2: (z * rou) ^ (n * x) = z ^ (n * x) * rou ^ (n * x),
    exact mul_pow z rou (n * x),
  have h3: rou ^ (n * x) = (rou ^ n) ^ x,
    exact pow_mul rou n x,
  simp [h2,h3,h₁],
end

-- The zero coefficients are needed for proof of ruesNEqExpSum
-- m=0 is same as rues, ruesDiff is the mth derivative of rues
lemma ruesDiffTsumForm (n:ℕ) (m:ℤ) (z:ℂ) : ruesDiff n m z = tsum (λ (k:ℕ), if ((k:ℤ)+m)%n=0 then z ^ k / k.factorial else 0) :=
begin
  have h0 : z ∈ emetric.ball (0:ℂ) (rues_series n m).radius,
  {
    rw rues_series_radius,
    rw metric.emetric_ball_top,
    simp only [set.mem_univ],
  },
  have h1 := formal_multilinear_series.has_sum (rues_series n m) h0,
  have h2 := has_sum.tsum_eq h1,
  rw ruesDiff,
  rw h2.symm,
  simp only [formal_multilinear_series.apply_eq_pow_smul_coeff, algebra.id.smul_eq_mul, euclidean_domain.mod_eq_zero],
  rw rues_series,
  rw plain_old_series,
  congr' 1,
  ext1,
  rw formal_multilinear_series.coeff,
  simp only [continuous_multilinear_map.mk_pi_field_apply, pi.one_apply, finset.prod_const_one, algebra.id.smul_eq_mul, one_mul],
  rw rues_coeff,
  simp only [euclidean_domain.mod_eq_zero, one_div, mul_ite, mul_zero],
  congr' 1,
end

lemma ruesDiffSummable (n:ℕ) (m:ℤ) (z:ℂ) : summable (λ (k:ℕ), if ((k:ℤ)+m)%n=0 then z ^ k / k.factorial else 0) :=
begin
  have h0 : z ∈ emetric.ball (0:ℂ) (rues_series n m).radius,
  {
    rw rues_series_radius,
    rw metric.emetric_ball_top,
    simp only [set.mem_univ],
  },
  have h1 := formal_multilinear_series.summable (rues_series n m) h0,
  simp only [formal_multilinear_series.apply_eq_pow_smul_coeff, algebra.id.smul_eq_mul] at h1,
  have h2 : (λ (k : ℕ), ite ((↑k + m) % ↑n = 0) (z ^ k / ↑k!) 0) = (λ (n_1 : ℕ), z ^ n_1 * (rues_series n m).coeff n_1),
  {
    ext1,
    rw rues_series,
    rw plain_old_series,
    rw formal_multilinear_series.coeff,
    rw rues_coeff,
    simp only [euclidean_domain.mod_eq_zero, one_div, continuous_multilinear_map.mk_pi_field_apply, pi.one_apply,
  finset.prod_const_one, algebra.id.smul_eq_mul, mul_ite, one_mul, mul_zero],
    congr' 1,
  },
  simp_rw h2,
  exact h1,
end

lemma ruesDiffM0EqRues (n:ℕ) (h:0<n) (z:ℂ) : rues n z = ruesDiff n 0 z :=
begin
  sorry,
end

lemma rouNot0 (n:ℕ) (h₀:0<n) (rou:ℂ) (h₁:rou ^ n = 1) : rou ≠ 0 :=
begin
  have h0 := cpow_def rou n,
  have h1 : n ≠ 0,
  exact ne_of_gt h₀,
  have h2 : ¬ (n:ℂ) = 0,
  exact_mod_cast h1,
  simp_rw if_neg h2 at h0,
  rw_mod_cast h₁ at h0,
  have h3 : (rou = 0) → false,
  {
    intros h4,
    rw if_pos h4 at h0,
    simp only [one_ne_zero] at h0,
    exact h0,
  },
  contradiction,
end

lemma ruesDiffRotationallySymmetric (n:ℕ) (h₀:0<n) (m:ℤ) (z rou:ℂ) (h₁:rou ^ n = 1) : ruesDiff n m (z * rou) = rou ^ -m * ruesDiff n m z :=
begin
  simp_rw ruesDiffTsumForm,
  rw tsum_mul_left.symm,
  {
    congr' 1,
    ext1,
    simp only [euclidean_domain.mod_eq_zero, zpow_neg, mul_ite, mul_zero],
    have h0 := classical.em (↑n ∣ ↑x + m),
    cases h0,
    {
      rw [if_pos h0,if_pos h0],
      rw mul_pow z rou x,
      have h1 : rou ^ x = (rou ^ m)⁻¹,
      {
        let k := (x:ℤ) + m,
        have h2 : (x:ℤ) + m = k,
        exact rfl,
        rw h2 at h0,
        clear_value k,
        obtain ⟨k1, rfl⟩ := h0,
        have h3 : rou ^ ((x:ℤ) + m) = 1,
        {
          rw h2,
          rw zpow_mul rou ↑n k1,
          have h4 : rou ^ (n:ℤ) = 1,
          {
            exact_mod_cast h₁,
          },
          rw h4,
          simp only [one_zpow],
        },
        have h5 := congr_arg (λ (z₀:ℂ),z₀*(rou ^ m)⁻¹) h3.symm,
        simp only [one_mul] at h5,
        rw h5,
        have h6 := rouNot0 n h₀ rou h₁,
        rw zpow_add₀ h6 (x:ℤ) m,
        simp only [zpow_coe_nat],
        have h7 : rou ^ m ≠ 0,
        exact zpow_ne_zero m h6,
        field_simp,
      },
      rw h1,
      ring_nf,
    },
    {
      rw [if_neg h0,if_neg h0],
    },
  },
  exact topological_semiring.mk,
  exact polish_space.t2_space ℂ,
end

lemma ruesDiffMPeriodic (n:ℕ) (m k:ℤ) (z:ℂ) : ruesDiff n m z = ruesDiff n (m+k*n) z :=
begin
  rw [ruesDiffTsumForm, ruesDiffTsumForm],
  congr' 1,
  ext1,
  congr' 1,
  apply propext,
  have h : (↑x + m) % ↑n = ((↑x + m) + k * ↑n) % ↑n,
    rw int.add_mul_mod_self,
  rw h,
  ring_nf,
end

open finset

-- Help received from https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/lemma.20exp_pi_mul_I_half.20.3A.20exp.20.28.E2.86.91real.2Epi.20*.20I.20.2F.202.29.20.3D.20I.20.3A.3D
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

lemma expToNatPowersOfI (k:ℕ): exp (↑real.pi * I * k / 2) = I^k :=
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

lemma expToIntPowersOfI (k:ℤ): exp (↑real.pi * I * k / 2) = I^k :=
begin
  induction k,
  exact expToNatPowersOfI _,
  rw expNegInv _,
  simp only [int.cast_neg_succ_of_nat, nat.cast_add, nat.cast_one, neg_add_rev, zpow_neg_succ_of_nat, inv_inj],
  rw (show -(↑real.pi * I * (-1 + -↑k) / 2) = (↑real.pi * I * (1 + ↑k) / 2), by ring_nf),
  have h0 : (1:ℂ) + ↑k = ↑(k + 1),
  norm_cast at *,
  exact add_comm 1 k,
  rw h0,
  rw expToNatPowersOfI (k + 1),
end

-- Help received from https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/exponential.20function.20to.20a.20natural.20power
-- Help received from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Help.20with.20geom_sum.20ite.20lemma
lemma ruGeomSumEqIte (n:ℕ) (k:ℤ) (h:0<n) :
    ∑ m in range n, (complex.exp (2 * real.pi * (k / n) * I)) ^ m = ite ((n:ℤ) ∣ k) n 0 :=
begin
  have h0 := classical.em ((n:ℤ) ∣ k),
  cases h0,
  {
    have h2 : ∑ (m : ℕ) in range n, exp (2 * ↑real.pi * (↑k / ↑n) * I) ^ m = 
              ∑ (m : ℕ) in range n, 1,
    congr,
    ext1,
    obtain ⟨m2, rfl⟩ := h0, -- need to replace k with a multiple of n to proceed
    have h3: ↑(↑n * m2) / ↑n = (m2:ℂ),
    rw int.cast_mul n m2,
    ring_nf,
    field_simp,
    rw mul_div_cancel,
    exact_mod_cast h.ne.symm,
    rw h3,
    let h4:= expToIntPowersOfI (4*m2),
    simp only [int.cast_mul, int.cast_bit0, int.cast_one] at h4,
    rw (show ↑real.pi * I * (4 * ↑m2) / 2 = 2 * ↑real.pi * ↑m2 * I, by ring) at h4,
    rw h4,
    rw zpow_mul I 4 m2,
    simp only [I_zpow_bit0, zpow_bit0_neg, one_zpow, one_pow],
    rw h2,
    simp only [sum_const, card_range, nat.smul_one_eq_coe],
    rw if_pos h0, -- need to evaluate ite with h0
  },
  {
    rw geom_sum_eq,
    rw if_neg h0,
    rw (complex.exp_nat_mul _ n).symm,
    rw (show ↑n * (2 * ↑real.pi * (↑k / ↑n) * I) = 2 * ↑real.pi * ↑k * I  * ↑n / ↑n, by {ring_nf}),
    rw mul_div_cancel,
    let h5:= expToIntPowersOfI (4*k),
    simp only [int.cast_mul, int.cast_bit0, int.cast_one] at h5,
    rw (show ↑real.pi * I * (4 * ↑k) / 2 = 2 * ↑real.pi * ↑k * I, by ring) at h5,
    rw h5,
    rw zpow_mul I 4 k,
    simp only [I_zpow_bit0, zpow_bit0_neg, one_zpow, sub_self, zero_div],
    exact_mod_cast h.ne.symm,
    intro eq1,
    apply h0,
    obtain ⟨m, he⟩ := complex.exp_eq_one_iff.1 eq1,
    use ↑m,
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
    exact_mod_cast h.ne.symm,
  },
end

lemma ruGeomSumEqIte2 (n:ℕ) (k:ℤ) (h:0<n) :
    ∑ m in range n, (complex.exp (2 * real.pi * (m / n) * I)) ^ k = ite ((n:ℤ) ∣ k) n 0 :=
begin
  have h0 : ∀ (m:ℕ), complex.exp (2 * real.pi * (m / n) * I) ^ k = complex.exp ((k:ℂ) * (2 * real.pi * (m / n) * I)),
  {
    intros m,
    exact (complex.exp_int_mul (2 * real.pi * (m / n) * I) k).symm,
  },
  simp_rw h0,
  have h1 : ∀ (x:ℕ), ↑k * (2 * ↑real.pi * (↑x / ↑n) * I) = ↑x * (2 * ↑real.pi * (↑k / ↑n) * I),
  {
    intros x,
    ring_nf,
  },
  simp_rw h1,
  have h2 : ∀ (x:ℕ), exp (↑x * (2 * ↑real.pi * (↑k / ↑n) * I)) = exp (2 * ↑real.pi * (↑k / ↑n) * I) ^ x,
  {
    intros x,
    exact complex.exp_nat_mul _ x,
  },
  simp_rw h2,
  exact ruGeomSumEqIte n k h,
end

lemma ruesNEqExpSum (n:ℕ) (h:0<n) (z:ℂ) :
    rues n z = (∑ m in range n, exp (z * exp (2 * real.pi * (m / n) * I)))/n :=
begin
  simp_rw expTsumForm,
  have h0 : (∀ m ∈ range n, summable (λ (k:ℕ), (z * exp (2 * real.pi * (m / n) * I)) ^ k / k.factorial)),
  {
    intros m h1,
    exact expTaylorSeriesSummable (z * exp (2 * real.pi * (m / n) * I)),
  },
  have h2 := (tsum_sum h0).symm,
  clear h0,
  simp_rw expTsumForm at h2,
  simp_rw h2,
  clear h2,
  simp_rw (expTsumForm _).symm,
  simp_rw mul_pow z _ _,
  have h3 : ∀ (b x : ℕ), z ^ b * exp (2 * ↑real.pi * (↑x / ↑n) * I) ^ b / ↑b! = (z ^ b / ↑b!) * exp (2 * ↑real.pi * (↑x / ↑n) * I) ^ b,
  {
    intros b x,
    ring_nf,
  },
  simp_rw h3,
  clear h3,
  simp_rw mul_sum.symm,
  have h4 : ∀ (b:ℕ), ∑ (x : ℕ) in range n, exp (2 * ↑real.pi * (↑x / ↑n) * I) ^ b = ite ((n:ℤ) ∣ b) n 0,
  {
    intros b,
    exact ruGeomSumEqIte2 n b h,
  },
  simp_rw h4,
  clear h4,
  have h5 : rues n z * ↑n = (∑' (b : ℕ), z ^ b / ↑b! * ite (↑n ∣ (b:ℤ)) ↑n 0),
  {
    rw [ruesDiffM0EqRues,ruesDiffTsumForm],
    rw tsum_mul_right.symm,
    {
      congr,
      ext1,
      simp only [add_zero, euclidean_domain.mod_eq_zero, ite_mul, zero_mul, mul_ite, mul_zero],
    },
    exact topological_semiring.mk,
    exact polish_space.t2_space ℂ,
    exact h,
  },
  have h6 := congr_arg (λ (z₀:ℂ),z₀/n) h5,
  clear h5,
  simp only [mul_ite, mul_zero] at h6,
  have h7 : n ≠ 0,
  exact (ne_of_lt h).symm,
  have h8 : (n:ℂ) ≠ 0,
  exact_mod_cast h7,
  clear h7,
  field_simp at h6 ⊢,
  simp_rw h6,
  clear h6,
  congr' 1,
  ext1,
  have h9 := classical.em ((n:ℤ) ∣ ↑x),
  cases h9,
  {
    simp_rw if_pos h9,
  },
  {
    simp_rw if_neg h9,
    simp only [zero_div],
  },
end

lemma ruesN0Eq1 (n:ℕ) (h:0<n) : rues n 0 = 1:=
begin
  rw ruesNEqExpSum n h 0,
  simp only [zero_mul, complex.exp_zero, sum_const, card_range, nat.smul_one_eq_coe],
  have h0 : n ≠ 0,
  exact (ne_of_lt h).symm,
  have h1 : (n:ℂ) ≠ 0,
  exact_mod_cast h0,
  field_simp,
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
  simp only [range_val, multiset.range_succ, multiset.range_zero, multiset.cons_zero, nat.cast_bit0, algebra_map.coe_one,
  multiset.map_cons, one_div, multiset.map_singleton, algebra_map.coe_zero, zero_div, mul_zero, zero_mul,
  complex.exp_zero, mul_one, multiset.sum_cons, multiset.sum_singleton],
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
  simp only [range_val, multiset.range_succ, multiset.range_zero, multiset.cons_zero, nat.cast_bit0, algebra_map.coe_one,
  multiset.map_cons, nat.cast_bit1, one_div, multiset.map_singleton, algebra_map.coe_zero, zero_div, mul_zero, zero_mul,
  complex.exp_zero, mul_one, multiset.sum_cons, multiset.sum_singleton],
  {
    rw [exp_mul_I, exp_mul_I, exp_mul_I],
    rw (show 2 * ↑real.pi * 4⁻¹ = (real.pi/2:ℂ), by ring),
    simp only [complex.cos_pi_div_two, complex.sin_pi_div_two, one_mul, zero_add],
    rw (show (2:ℂ) * ↑real.pi * (2 / 4) = ↑real.pi, by ring),
    simp only [complex.cos_pi, complex.sin_pi, zero_mul, add_zero, mul_neg, mul_one],
    rw (show 2 * ↑real.pi * (3 / 4) = (3/2*real.pi:ℂ), by ring),
    rw (exp_mul_I _).symm,
    let h:=expToNatPowersOfI 3,
    rw (show (3:ℂ) / 2 * ↑real.pi * I = ↑real.pi * I * ↑3 / 2, by {simp, ring}),
    rw h,
    simp only [I_pow_bit1, pow_one, neg_mul, one_mul, mul_neg],
    ring_nf,
    have hinv1: (-I + 1)⁻¹ = (I + 1)/2,
      rw [complex.inv_def, norm_sq],
      simp only [map_add, conj_neg_I, map_one, monoid_with_zero_hom.coe_mk, add_re, neg_re, I_re, neg_zero, one_re, zero_add, mul_one,
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

lemma ruesDiffSumOfRuesDiff (n k:ℕ) (h:0<n*k) (m:ℤ) (z:ℂ) : ruesDiff n m z = ∑ k₀ in range k, ruesDiff (n*k) (n*k₀+m) z:=
begin
  simp_rw ruesDiffTsumForm,
  have h0 : ∀ x ∈ range k, summable (λ (k_1:ℕ), ite ((↑k_1 + (↑n * ↑x + m)) % ↑(n * k) = 0) (z ^ k_1 / ↑k_1!) 0),
  {
    intros x h1,
    exact ruesDiffSummable (n * k) _ z,
  },
  rw (tsum_sum h0).symm,
  clear h0,
  congr' 1,
  ext1,
  sorry,
end

lemma expSumOfRuesDiff (k:ℕ) (h:0<k) (z:ℂ) : exp z = ∑ k₀ in range k, ruesDiff k k₀ z:=
begin
  have h0 : 0 < 1 * k,
  {
    simp only [one_mul],
    exact h,
  },
  rw (rues1EqExp z).symm,
  have h1 : 0<1,
  {
    simp only [nat.lt_one_iff],
  },
  rw ruesDiffM0EqRues 1 h1 z,
  have h2 := ruesDiffSumOfRuesDiff 1 k h0 0 z,
  simp only [one_mul, nat.cast_one, add_zero] at h2,
  exact h2,
end

-- Help received from https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20Commuting.20sum.20sigmas.20with.20a.20sum.20of.20sum.20of.20sum
lemma sum_three_cycle {M α β γ : Type*} [add_comm_monoid M] {s : finset α} {t : finset β}
  {u : finset γ} {f : α → β → γ → M} : ∑ a in s, ∑ b in t, ∑ c in u, f a b c =
    ∑ b in t, ∑ c in u, ∑ a in s, f a b c :=
begin
  rw finset.sum_comm,
  simp_rw @finset.sum_comm _ γ,
end

lemma nNeqComplex0 (n:ℕ) (h:0<n) : (n:ℂ) ≠ 0 :=
begin
  have h0 : 0 ≠ n,
  exact ne_of_lt h,
  exact_mod_cast h0.symm,
end

lemma standardRouForm (n:ℕ) (h:0<n) : ∀ (x:ℕ), exp (2 * ↑real.pi * (↑x / ↑n) * I) ^ n = 1 :=
begin
    intros x,
  rw (complex.exp_nat_mul _ n).symm,
  rw complex.exp_eq_one_iff,
  use (x:ℤ),
  have h0 := nNeqComplex0 n h,
  field_simp,
  ring_nf,
end

lemma ruesArgumentSumRule (n:ℕ) (h:0<n) (z₀ z₁:ℂ) :
        rues n (z₀ + z₁) = ∑ k in range n, (ruesDiff n k z₀ * ruesDiff n (n - k) z₁) :=
begin
  rw ruesNEqExpSum n h _,
  have h0 : ∀ (m : ℕ), (z₀ + z₁) * exp (2 * ↑real.pi * (↑m / ↑n) * I) =
    z₀ * exp (2 * ↑real.pi * (↑m / ↑n) * I) +
    z₁ * exp (2 * ↑real.pi * (↑m / ↑n) * I),
  {
    intros m,
    ring_nf,
  },
  simp_rw h0,
  clear h0,
  simp_rw complex.exp_add,
  have h1 : ∀ (x : ℕ), exp (z₀ * exp (2 * ↑real.pi * (↑x / ↑n) * I)) =
    ∑ (k₀ : ℕ) in range n, ruesDiff n ↑k₀ (z₀ * exp (2 * ↑real.pi * (↑x / ↑n) * I)),
  {
    intros x,
    exact expSumOfRuesDiff n h (z₀ * complex.exp ((2:ℂ) * (real.pi:ℂ) * ((x:ℂ) / (n:ℂ)) * I)),
  },
  simp_rw h1,
  clear h1,
  have h2 : ∀ (x : ℕ), exp (z₁ * exp (2 * ↑real.pi * (↑x / ↑n) * I)) =
    ∑ (k₀ : ℕ) in range n, ruesDiff n ↑k₀ (z₁ * exp (2 * ↑real.pi * (↑x / ↑n) * I)),
  {
    intros x,
    exact expSumOfRuesDiff n h (z₁ * complex.exp ((2:ℂ) * (real.pi:ℂ) * ((x:ℂ) / (n:ℂ)) * I)),
  },
  simp_rw h2,
  clear h2,
  have h3 := standardRouForm n h,
  have h6 : ∀ (k₀ x : ℕ) (z : ℂ), ruesDiff n ↑k₀ (z * exp (2 * ↑real.pi * (↑x / ↑n) * I)) =
    exp (2 * ↑real.pi * (↑x / ↑n) * I) ^ -↑k₀ * ruesDiff n ↑k₀ z,
  {
    intros k₀ x z,
    exact ruesDiffRotationallySymmetric n h k₀ z (exp (2 * ↑real.pi * (↑x / ↑n) * I)) (h3 x),
  },
  simp_rw h6 _ _ _,
  clear h6,
  simp_rw [finset.sum_mul, finset.mul_sum],
  have h7 : ∀ (x x_1 x_2 : ℕ), exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ^ -(x_1:ℤ) * ruesDiff n x_1 z₀ *
  (exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ^ -(x_2:ℤ) * ruesDiff n x_2 z₁) =
  ruesDiff n x_1 z₀ * ruesDiff n x_2 z₁ * (exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ^ -(x_1:ℤ) *
  exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ^ -(x_2:ℤ)),
  {
    intros x x_1 x_2,
    ring_nf,
  },
  simp_rw h7,
  clear h7,
  have h8 : ∀ (x x_1 x_2 : ℕ), exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ^ -(x_1:ℤ) * exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ^ -(x_2:ℤ) =
  exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ^ (-(x_1:ℤ) + -(x_2:ℤ)),
  {
    intros x x_1 x_2,
    have h9 : exp (2 * ↑real.pi * ((x:ℂ) / (n:ℂ)) * I) ≠ 0,
    {
      exact rouNot0 n h (exp (2 * ↑real.pi * (↑x / ↑n) * I)) (h3 x),
    },
    exact (zpow_add₀ h9 (-(x_1:ℤ)) (-(x_2:ℤ))).symm,
  },
  simp_rw h8,
  clear h8,
  rw sum_three_cycle,
  simp_rw finset.mul_sum.symm,
  have h9 : ∀ (x x_1 : ℕ), ∑ (m : ℕ) in range n, exp (2 * ↑real.pi * ((m:ℂ) / (n:ℂ)) * I) ^ (-(x:ℤ) + -(x_1:ℤ)) =
    ite (↑n ∣ -(x:ℤ) + -(x_1:ℤ)) ↑n 0,
  {
    intros x x_1,
    exact ruGeomSumEqIte2 n (-↑x + -↑x_1) h,
  },
  simp_rw h9,
  clear h9,
  ring_nf,
  simp_rw [finset.mul_sum],
  simp only [mul_ite, mul_zero],
  have h10 := nNeqComplex0 n h,
  field_simp,
  sorry,
end
