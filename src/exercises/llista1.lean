import data.real.basic
import data.int.parity
import algebra.geom_sum

open set
open finset

open_locale big_operators

noncomputable theory

-- exercici 9
example (θ χ : Prop) : θ ↔ (θ ∧ χ) ∨ (θ ∧ (¬ χ)) :=
begin
  sorry
end

example (θ χ : Prop) : θ ↔ (θ ∧ χ) ∨ (θ ∧ (¬ χ)) :=
begin
  split;finish,
end

-- exercici 11
def R := λ (x y : ℕ), x < y
def S := λ (x y : ℕ), x > y

example : ∀ x, ∃ y, R x y :=
begin
  unfold R,
  intro x,
  use x+10,
  linarith,
end

example : ¬ (∀ x, ∃ y, S x y) :=
begin
  unfold S,
  push_neg,
  use 0,
  intro y,
  exact zero_le y,
end

-- exercici 12
def S' := λ (a b c : ℕ), c = a + b

example : ∃ (x : ℕ), ∃ (z : ℕ), (¬ x = z) ∧
  (∃ y, S' y y x) ∧
  (∃ t, S' t t z) :=
begin
  unfold S',
  use 0,
  use 2,
  split,
  {
    change 0 ≠ 2,
    exact two_ne_zero.symm,
  },
  split,
  {
    use 0,
  },
  {
    use 1,
  }
end


example : ¬ (∃ x, (∀ y, ∃ z, S' y z x)) :=
begin
  sorry
end

--@[simp]
--lemma simp_succ (n : ℕ) : n.succ = n + 1 := rfl


-- 14a
example (n : ℕ) : ∑ k in range (n + 1), (k : ℝ) = n * (n + 1) / 2 :=
begin
  induction n with n hn,
  { 
    norm_num,
  },
  {
    rw sum_range_succ,
    simp at hn ⊢,
    rw hn,
    ring,
  }
end

-- 14b
example (n : ℕ) : ∑ k in range (n + 1), (k^2 : ℝ) = n*(n + 1)*(2*n + 1) / 6 :=
begin
  induction n with n hn,
  { 
    norm_num,
  },
  {
    rw sum_range_succ,
    simp at hn ⊢,
    rw hn,
    ring,
  }
end

-- 14c
example (n : ℕ) : 6 ∣ (n * (n^2 + 5)) :=
begin
  sorry
end

-- exercici 15
example (n : ℕ) : 3 ∣ (4:ℤ)^n - 1 :=
begin
  sorry
end

example : ∃ (n:ℕ), ¬ 3 ∣ (4:ℤ)^n + 1 :=
begin
  sorry
end


-- exercici 17
example (a : ℕ → ℝ) (h1 : (∀ n, 0 < a n) ∨ (∀ n, a n < 0)) 
(h2 : ∀ n, a n > -1) (n : ℕ):
1 + ∑ i in range (n+2), a i < ∏ i in range (n+2), (1 + a i):=
begin
  induction n with n hn,
  sorry
end


-- exercici 17bis
example (a : ℕ → ℝ) (h1 : (∀ n, 0 < a n) ∨ (∀ n, a n < 0)) (h2 : ∀ n, a n > -1) :
∀ n : ℕ, 2 ≤ n → 1 + ∑ i in range n, a i < ∏ i in range n, (1 + a i):=
begin
  sorry
end



