-- Help received from https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Having.20trouble.20taking.20a.20derivative
import analysis.analytic.basic
import analysis.complex.basic
import analysis.calculus.deriv
import analysis.calculus.fderiv_analytic
import analysis.analytic.radius_liminf
import analysis.normed_space.exponential

noncomputable theory

open formal_multilinear_series
open filter
open_locale nnreal ennreal

variables {𝕜 E : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
  [complete_space E] {p q : formal_multilinear_series 𝕜 𝕜 E} {n : ℕ} {f : 𝕜 → E} {w : 𝕜} {r : ennreal}

def plain_old_series (𝕜 : Type*) [nontrivially_normed_field 𝕜] {E : Type*}  [normed_add_comm_group E]
  [normed_space 𝕜 E] (a : ℕ → E) : formal_multilinear_series 𝕜 𝕜 E :=
λ n, continuous_multilinear_map.mk_pi_field 𝕜 (fin n) (a n)

lemma plain_old_series_coeff {a : ℕ → E} {n : ℕ} : (plain_old_series 𝕜 a).coeff n = a n :=
by simp [formal_multilinear_series.coeff, plain_old_series]

noncomputable def formal_multilinear_series.deriv (p : formal_multilinear_series 𝕜 𝕜 E) :
  formal_multilinear_series 𝕜 𝕜 E :=
λ n, (n + 1) • (p (n + 1)).curry_left 1

lemma coeff_deriv : p.deriv.coeff n = (n + 1) • p.coeff (n + 1) :=
begin
  simp only [formal_multilinear_series.deriv, formal_multilinear_series.coeff],
  simp only [fin.prod_cons, continuous_multilinear_map.smul_apply, apply_eq_prod_smul_coeff,
    continuous_multilinear_map.curry_left_apply, pi.one_apply, finset.prod_const_one, mul_one],
end

lemma apply_eq_iff_coeff_eq : p n = q n ↔ p.coeff n = q.coeff n :=
begin
  simp only [continuous_multilinear_map.ext_iff],
  split; intro h,
  { simpa using h 1 },
  { simp [h] }
end

lemma eq_iff_coeff_eq : p = q ↔ ∀ n, p.coeff n = q.coeff n :=
by simp [formal_multilinear_series.ext_iff, apply_eq_iff_coeff_eq]

lemma change_origin_series_eq_deriv :
  p.change_origin_series 1 n 1 (fin.snoc matrix.vec_empty 1) = p.deriv n 1 :=
begin
  change p.change_origin_series 1 n 1 1 = p.deriv n 1,
  let S : finset {s : finset (fin (1 + n)) // s.card = n} := finset.univ,
  suffices : S.card • p.coeff (1 + n) = p.deriv.coeff n,
    simpa [change_origin_series, change_origin_series_term] using this,
  simp [coeff_deriv, S, add_comm 1 n, finset.card_univ]
end

lemma has_fpower_series_on_ball.deriv (hp : has_fpower_series_on_ball f p w r) :
  has_fpower_series_on_ball (deriv f) p.deriv w r :=
begin
  let ev : (𝕜 →L[𝕜] E) →L[𝕜] E := continuous_linear_map.apply _ _ 1,
  convert ← (ev.comp_has_fpower_series_on_ball hp.fderiv),
  refine eq_iff_coeff_eq.mpr (λ n, _),
  simp only [ev, formal_multilinear_series.coeff, linear_isometry_equiv.coe_coe'',
    continuous_linear_map.comp_formal_multilinear_series_apply, change_origin_series_eq_deriv,
    function.comp_app, continuous_linear_map.comp_continuous_multilinear_map_coe,
    continuous_multilinear_curry_fin1_apply, continuous_linear_map.apply_apply, matrix.zero_empty]
end

lemma has_fpower_series_on_ball.has_deriv_at (hp : has_fpower_series_on_ball f p w r) {z : 𝕜}
  (hz : z ∈ emetric.ball w r) : has_deriv_at f (p.deriv.sum (z - w)) z :=
begin
  have h1 := hp.deriv,
  have h2 : differentiable_at 𝕜 f z,
    from hp.differentiable_on.differentiable_at (is_open.mem_nhds emetric.is_open_ball hz),
  have h3 := has_deriv_at_deriv_iff.mpr h2,
  convert h3,
  have h4 : z - w ∈ emetric.ball (0 : 𝕜) r,
    by simpa [edist_comm z w, ← edist_sub_left z w z] using hz,
  simpa [formal_multilinear_series.sum] using (h1.has_sum h4).tsum_eq,
end

lemma radius_le_radius_of_nnnorm_le (h : ∀ n, ∥p n∥₊ ≤ ∥q n∥₊) : q.radius ≤ p.radius :=
begin
  simp [radius_eq_liminf],
  refine @liminf_le_liminf ennreal ℕ _ at_top _ _ _ _ _,
  { refine eventually_of_forall (λ n, _),
    simp only [ennreal.inv_le_inv, ennreal.coe_le_coe],
    exact nnreal.rpow_le_rpow (h n) (by positivity) },
  { exact ⟨0, by simp⟩ },
  { exact ⟨⊤, by simp⟩ }
end

lemma radius_le_radius_of_nnnorm_le' (h : ∀ n, ∥p.coeff n∥ ≤ ∥q.coeff n∥) : q.radius ≤ p.radius :=
radius_le_radius_of_nnnorm_le (by simp [← norm_to_nnreal, h])

------------------------

def rues_coeff (n m k : ℕ) : ℂ := if (k + m) % n = 0 then (1 : ℂ) / k.factorial else 0

def rues_series (n m : ℕ) := plain_old_series ℂ (rues_coeff n m)

@[simp] lemma rues_series_radius {n m : ℕ} : (rues_series n m).radius = ⊤ := 
begin
  have h:∀ (k:ℕ), ∥(rues_series n m).coeff k∥ ≤ ∥(exp_series ℂ ℂ).coeff k∥,
  {
    intro k,
    rw [coeff,coeff],
    rw [rues_series,exp_series],
    rw [plain_old_series],
    simp only [continuous_multilinear_map.mk_pi_field_apply, pi.one_apply, finset.prod_const_one, algebra.id.smul_eq_mul, one_mul,
  complex.norm_eq_abs, continuous_multilinear_map.smul_apply, continuous_multilinear_map.mk_pi_algebra_fin_apply,
  absolute_value.map_mul, map_inv₀, complex.abs_cast_nat],
    rw rues_coeff,
    have h3:=classical.em ((k + m) % n = 0),
    cases h3,
    {
      rw [if_pos h3],
      simp only [one_div, map_inv₀, complex.abs_cast_nat],
      rw list.prod_of_fn,
      simp only [pi.one_apply, finset.prod_const_one, absolute_value.map_one, mul_one],
    },
    {
      rw [if_neg h3],
      simp only [absolute_value.map_zero],
      rw list.prod_of_fn,
      simp only [pi.one_apply, finset.prod_const_one, absolute_value.map_one, mul_one, inv_nonneg, nat.cast_nonneg],
    },
  },
  have h2:=radius_le_radius_of_nnnorm_le' h,
  rw (exp_series_radius_eq_top ℂ ℂ) at h2,
  exact eq_top_iff.mpr h2,
end

lemma inv_mul_other_mul_self_cancel (z1 z2:ℂ) (h:z1≠0): z1⁻¹ * z2 * z1 = z2:=
  by field_simp

@[simp] lemma rues_series.deriv {n m : ℕ} : (rues_series n m).deriv = rues_series n (m + 1) :=
begin
  refine eq_iff_coeff_eq.mpr (λ k, _),
  simp [coeff_deriv, rues_series, plain_old_series_coeff],
  rw [rues_coeff,rues_coeff],
  simp only [nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one, one_div, mul_inv_rev, mul_ite, mul_zero],
  rw (show k + (m + 1)=k + 1 + m, by ring),
  congr' 1,
  norm_cast at *,
  ring_nf,
  have h1:↑(k + 1)≠(0:ℂ),
  norm_cast at *,
  rw inv_mul_other_mul_self_cancel (↑(k + 1)) ((↑(k.factorial))⁻¹) h1,
end

def rues_function (n m : ℕ) : ℂ → ℂ := (rues_series n m).sum

lemma ruesDiffHasDeriv (n m : ℕ) (z : ℂ) :
  has_deriv_at (rues_function n m) (rues_function n (m + 1) z) z :=
begin
  have h1 : ∀ {n m}, 0 < (rues_series n m).radius := by simp,
  have h2 := (rues_series n m).has_fpower_series_on_ball h1,
  have h3 : z ∈ emetric.ball (0 : ℂ) (rues_series n m).radius := by simp,
  simpa [rues_function] using h2.has_deriv_at h3
end
