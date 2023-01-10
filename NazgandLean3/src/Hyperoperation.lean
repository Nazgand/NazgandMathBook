import algebra.group_with_zero.defs
import tactic

def hyperoperation : ℕ → ℕ → ℕ → ℕ
| 0 _ b := b + 1
| 1 a 0 := a
| 2 _ 0 := 0
| (n + 3) _ 0 := 1
| (n + 1) a (b + 1) := hyperoperation n a (hyperoperation (n + 1) a b)

-- Basic hyperoperation lemmas

lemma hyperoperation_0ab_b.succ (a b : ℕ) : hyperoperation 0 a b = b + 1 :=
begin
  rw hyperoperation,
end

lemma hyperoperation_1a0_a (a : ℕ) : hyperoperation 1 a 0 = a :=
begin
  rw hyperoperation,
end

lemma hyperoperation_2a0_0 (a : ℕ) : hyperoperation 2 a 0 = 0 :=
begin
  rw hyperoperation,
end

lemma hyperoperation_n3a0_1 (n a : ℕ) : hyperoperation (n + 3) a 0 = 1 :=
begin
  rw hyperoperation,
end

lemma hyperoperation_n1ab1_recurse (n a b : ℕ) :
  hyperoperation (n + 1) a (b + 1) = hyperoperation n a (hyperoperation (n + 1) a b) :=
begin
  -- rw hyperoperation, -- does not work; should work
  sorry,
end

-- Interesting hyperoperation lemmas

lemma hyperoperation_1_addition (a b : ℕ) : hyperoperation 1 a b = a + b :=
begin
  induction b with bn bih,
  rw [nat_add_zero a, hyperoperation_1a0_a],
  {
    rw hyperoperation_n1ab1_recurse,
    rw (show 0 + 1 = 1, by refl),
    rw bih,
    rw hyperoperation_0ab_b.succ,
    rw (show bn.succ = bn + 1, by refl),
    exact nat.add_assoc a bn 1,
  },
end

lemma hyperoperation_2_multiplication (a b : ℕ) : hyperoperation 2 a b = a * b :=
begin
  induction b with bn bih,
  {
    rw hyperoperation_2a0_0,
    exact (nat.mul_zero a).symm,
  },
  {
    rw [hyperoperation_n1ab1_recurse,hyperoperation_1_addition],
    rw (show 1 + 1 = 2, by refl),
    rw bih,
    ring,
  },
end

lemma hyperoperation_succn_2_2_eq_4 (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 :=
begin
  induction n with nn nih,
  {
    rw (show 0 + 1 = 1, by refl),
    rw hyperoperation_1_addition,
  },
  {
    rw (show nn.succ + 1 = nn + 2, by refl),
    -- rw hyperoperation, --should work, fails to work
    sorry,
  },
end
