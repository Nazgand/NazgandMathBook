import algebra.group_with_zero.defs

def hyperoperation : ℕ → ℕ → ℕ → ℕ
| 0 _ b := 1 + b
| 1 a 0 := a
| 2 _ 0 := 0
| _ _ 0 := 1
| (n + 1) a (b + 1) := hyperoperation n a (hyperoperation (n + 1) a b)

lemma hyperoperation_1_addition (a b : ℕ) : hyperoperation 1 a b = a + b :=
begin
  induction b with bn bih,
  rw [nat_add_zero a, hyperoperation],
  {
    rw hyperoperation,
    have h1 : 0 + 1 = 1,
    exact rfl,
    rw [h1,bih],
    -- rw hyperoperation, --should work; does not work
    sorry,
  },
end

lemma hyperoperation_2_multiplication (a b : ℕ) : hyperoperation 2 a b = a * b :=
begin
  sorry,
end

lemma hyperoperation_succn_2_2_eq_4 (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 :=
begin
  sorry,
end
