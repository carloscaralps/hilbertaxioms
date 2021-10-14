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
  -- sorry
  split,
  {  
    intro t,
    by_cases c : χ,
    {
      left,
      split,
      {
        exact t,
      },
      {
        exact c,
      }
    },
    { 
      right,
      split,
      {
        exact t,
      },
      {
        exact c,
      }
    }
  },
  {
    intro h,
    cases h with h1 h1;
    {
      exact h1.1,
    },
  }
  -- sorry
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
  -- sorry
  intro x,
  unfold R,
  use x + 1,
  exact lt_add_one x,
  -- sorry
end

example : ¬ (∀ x, ∃ y, S x y) :=
begin
  -- sorry
  unfold S,
  push_neg,
  use 0,
  intro y,
  exact zero_le y,
  -- sorry
end

-- exercici 12
def S' := λ (a b c : ℕ), c = a + b

example : ∃ (x : ℕ), ∃ (z : ℕ), (¬ x = z) ∧
  (∃ y, S' y y x) ∧
  (∃ t, S' t t z) :=
begin
  -- sorry
  unfold S',
  use 0, use 2,
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
  -- sorry
end


example : ¬ (∃ x, (∀ y, ∃ z, S' y z x)) :=
begin
  -- sorry
  unfold S',
  push_neg,
  intro x,
  use x + 1,
  intro z,
  rw add_assoc,
  intro h,
  linarith,
  -- sorry
end


-- 14a
example (n : ℕ) : ∑ k in range (n + 1), (k : ℝ) = n * (n + 1) / 2 :=
begin
  -- sorry
  induction n with d hd,
  {
    simp,
  },
  {
    rw range_succ,
    rw sum_insert not_mem_range_self,
    rw hd,
    field_simp,
    ring,
  }
  -- sorry
end

-- 14b
example (n : ℕ) : ∑ k in range (n + 1), (k^2 : ℝ) = n*(n + 1)*(2*n + 1) / 6 :=
begin
  -- sorry
  induction n with d hd,
  {
    simp,
  },
  {
    rw range_succ,
    rw sum_insert not_mem_range_self,
    rw hd,
    field_simp,
    left,
    ring,
  }
  -- sorry
end

-- 14c
example (n : ℕ) : 6 ∣ (n * (n^2 + 5)) :=
begin
  -- sorry
  induction n with d hd,
  {
    use 0,
    ring_nf,
  },
  {
    obtain ⟨k, hk⟩ := hd,
    have he : even (d^2+d),
    {
      by_cases H : even d,
      {
        obtain ⟨e, he⟩ := H,
        use 2*e^2 + e,
        nlinarith,
      },
      {
        rw nat.even_iff_not_odd at H,
        push_neg at H,
        obtain ⟨o, ho⟩ := H,
        use 2*o^2 + 3*o + 1,
        rw ho,
        ring,
      }
    },
    obtain ⟨d2, hd2⟩ := he,
    use k + 1 + d2,
    rw add_pow_two _ 1,
    norm_num,
    rw add_mul _ 1,
    norm_num,
    rw mul_add 6 _,
    rw mul_add 6 _,
    rw ←hk,
    have six : 6 = 3 * 2, by norm_num,
    rw six,
    nth_rewrite_rhs 1 mul_assoc 3 2,
    rw ←hd2,
    nlinarith,
  }
  -- sorry
end

-- exercici 15
example (n : ℕ) : 3 ∣ (4:ℤ)^n - 1 :=
begin
  -- sorry
  rw ←mul_geom_sum,
  use geom_sum 4 n,
  refl,
  -- sorry
end

example : ∃ (n:ℕ), ¬ 3 ∣ (4:ℤ)^n + 1 :=
begin
  -- sorry
  use 1,
  simp,
  ring_nf,
  norm_num,
  -- sorry
end


-- exercici 17
example (a : ℕ → ℝ) (h1 : (∀ n, 0 < a n) ∨ (∀ n, a n < 0)) (h2 : ∀ n, a n > -1) (n : ℕ):
1 + ∑ i in range (n+2), a i < ∏ i in range (n+2), (1 + a i):=
begin
  -- sorry
  have explicit_range_2 : range 2 = ([0, 1]).to_finset := rfl,
  -- Fem inducció en n
  induction n with d hd,
  { -- Cas base: n = 0
    simp only [nat.nat_zero_eq_zero, zero_add],

    calc
    1 + ∑ (i : ℕ) in range 2, a i
        = 1 + ( a 0 + a 1) : by { simp [explicit_range_2]}
    ... < 1 + a 0 + a 1 + a 0 * a 1 : by {
      cases h1,
      {
       nlinarith [h1 0, h1 1],
      },
      {
        nlinarith [h1 0, h1 1],
      },
      --cases h1; nlinarith [h1 0, h1 1]}
    }
    ... = (1 + a 0) * (1 + a 1) : by ring
    ... = ∏ (x : ℕ) in range 2, (1 + a x) : by simp [explicit_range_2]
  },
  -- range k = [0, 1, ..., k-1]. Per tant, d+2 no pertany a range (d+2)
  have hd2 : d + 2 ∉ range (d+2) := not_mem_range_self,

  -- range (d+2) és no buit, té d+2 elements
  have nonempty_range : (range (d+2)).nonempty, by finish,

  -- aquesta és l'observació clau
  have hpos : 0 < a (d + 2) * ∑ (x : ℕ) in range (d + 2), a x,
  {
    cases h1,
    work_on_goal 0 {apply mul_pos (h1 (d+2))},
    work_on_goal 1 {apply mul_pos_of_neg_of_neg (h1 (d+2))},
    all_goals
    {      
      rw ←sum_const_zero,
      apply sum_lt_sum_of_nonempty nonempty_range (λ i _, h1 i),
    }
  },
  rw [range_succ, sum_insert hd2, finset.prod_insert hd2],
  nlinarith [hpos, h2 (d+2)],
  -- sorry
end


-- exercici 17bis
example (a : ℕ → ℝ) (h1 : (∀ n, 0 < a n) ∨ (∀ n, a n < 0)) (h2 : ∀ n, a n > -1) :
∀ n : ℕ, 2 ≤ n → 1 + ∑ i in range n, a i < ∏ i in range n, (1 + a i):=
begin
  -- sorry
  -- Descripció explícita de range 2 = [0, 1]
  have H2 : range 2 = ([0, 1]).to_finset := rfl,

  -- Fem inducció en n
  apply nat.le_induction,
  {
    -- Cas base: n = 0
    simp only [nat.nat_zero_eq_zero, zero_add, H2],
    calc
    1 + ∑ (x : ℕ) in [0, 1].to_finset, a x
        = 1 + (a 0 + a 1) : by { simp }
    ... < 1 + a 0 + a 1 + a 0 * a 1 : by {cases h1; nlinarith [h1 0, h1 1]}
    ... = (1 + a 0) * (1 + a 1) : by ring
    ... = ∏ (x : ℕ) in [0, 1].to_finset, (1 + a x) : by simp
  },
  intros d htwo hd,
  -- range k = [0, 1, ..., k-1]. Per tant, d no pertany a range d
  have hd2 : d ∉ range d := not_mem_range_self,

  -- range d és no buit, té d elements i d ≥ 2
  have nonempty_range : (range d).nonempty, by finish,

  -- aquesta és l'observació clau
  have hpos : 0 < a d * ∑ (x : ℕ) in range d, a x,
  {
    cases h1,
    work_on_goal 0 {apply mul_pos (h1 d)},
    work_on_goal 1 {apply mul_pos_of_neg_of_neg (h1 d)},
    all_goals
    { 
      rw ←sum_const_zero,
      apply sum_lt_sum_of_nonempty nonempty_range (λ i _, h1 i),
    }
  },
  rw [range_succ, sum_insert hd2, finset.prod_insert hd2],
  nlinarith [hpos, h2 d, htwo],
  -- sorry
end


