import incidenceplane
import auxiliar_lemmas
open IncidencePlane set

variables {Ω : Type} [IncidencePlane Ω]

/-
To prove some of the theorems in this world we need to introduce the `by_cases` tactic.
This tactic will split the main goal into two cases, assuming a statement on
the first case and his negation on the second.
-/

/- Lemma : no-side-bar
Either a point is in a line or it is not.
-/
lemma point_in_line_or_not {A : Ω}	{r : Line Ω} : A ∈ r ∨ A ∉ r :=
begin
  -- sorry
  by_cases h : A ∈ r,
  { 
    left,
    exact h,
  },
  { 
    right,
    exact h,
  }
  -- sorry
end

/-
Now that we have introduced the basic LEAN tactic is time to prove our 
first theorems. We will start with some of the theorems you have seen 
in the theory classes using incidence axioms.

To prove this theorem we will need the lemma, that commes directly from the
incidence axioms,

lemma line_through_left (P Q : Ω) : P ∈ (line_through P Q)

Similarly, we will also have the lemma

lemma line_through_right (P Q : Ω) : Q ∈ (line_through P Q)
-/

/- Theorem :
Giving a line there exists a point that it is not in it.
-/
theorem exists_point_not_in_line (l : Line Ω) : ∃ (P : Ω), P ∉ l :=
begin
  -- sorry
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : A ∈ l,
  {
    by_cases hB : B ∈ l,
    {
      use C,
      have ltA := line_through_left A B,
      have ltB := line_through_right A B,
      have : line_through A B = l,
      {
        exact equal_lines_of_contain_two_points hAB ltA hA ltB hB,
      },
      rw ← this,
      exact h,
    },
    {
      use B,
    }
  },
  {
    use A,
  }
  -- sorry
end

/-
In order to prove the next theorem, we will need to prove this lemma that 
will help us to deduce that the two points are different.
-/

/- Lemma : no-side-bar
If a point `P` is in a line and a point `Q` is not, then they are different.
-/
lemma point_in_line_not_point {P Q: Ω} {r : Line Ω} (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q :=
begin
  -- sorry
  intro H,
  rw H at hP,
  exact hQ hP,
  -- sorry
end

/-
Using the lemma specified before, we are going to prove the next incidence theorem.
-/

/- Theorem :
Given a point `P`, there exist two points `Q` and `R`, such that the three points are collinear.
-/
theorem point_existnce_postulate (P : Ω) : ∃ (Q R : Ω), P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ 
¬ R ∈ (line_through P Q) :=
begin
  -- sorry
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : P = A,
  {
    rw hA,
    use B, use C,
    exact ⟨hAB, hAC, hBC, h⟩,
  },
  {
    have := exists_point_not_in_line (line_through' P A),
    cases this with D hD,
    use A, use D,
    have hPD := point_in_line_not_point (line_through_left P A) hD,
    have hAD := point_in_line_not_point (line_through_right P A) hD,
    exact ⟨hA, hPD, hAD, hD⟩,
  }
  -- sorry
end

/-
As we have done with the last theorem, to prove the next, we need to first prove
a basic lemma that will help us simplify the proof.
-/

/- Lemma : no-side-bar
If two lines `r` and `s` do not share a point, then they are not equal.
-/
lemma if_pont_in_line_and_not_in_other_diferent {P : Ω} {r l : Line Ω} (hPr : P ∈ r)
(hPl : P ∉ l): r ≠ l :=
begin
  -- sorry
  intro H,
  rw H at hPr,
  exact hPl hPr,
  -- sorry
end

/-
Using the lemma we have just proved, we can now prove the following theorem.
-/

/- Theorem :
Given a point `P`, there are at least two different lines that pass through it.
-/
theorem point_exists_two_lines {P : Ω} : ∃ (r l: Line Ω), P ∈ l ∧ P ∈ r ∧ l ≠ r :=
begin
  -- sorry
  rcases (point_existnce_postulate P) with ⟨Q, R, ⟨hPQ, hPR, hQR,H⟩⟩,
  use line_through P Q, use line_through P R,
  repeat { split },
  {
    exact line_through_left P R,
  },
  {
    exact line_through_left P Q,
  },
  {
    exact if_pont_in_line_and_not_in_other_diferent (line_through_right P R) H,
  }
  -- sorry
end

/-
We will end this world by proving the last theorem using only incidence axioms. 
Notice that with this theorem we are essentially proving the existence of triangles, and 
only using incidence axioms!
-/

/- Theorem :
There exist three lines that do not have a point in common.
-/
theorem three_distinct_lines : ∃ (r l t: Line Ω), (∀ (P : Ω), ¬(P ∈ r ∧ P ∈ l ∧ P ∈ t)) :=
begin
  -- sorry
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  use line_through A B, use line_through A C, use line_through B C,
  intros P H,
  have h1 : line_through A C ≠ line_through A B, 
  {
    exact if_pont_in_line_and_not_in_other_diferent (line_through_right A C) h,
  },
  by_cases hPA : P = A,
  {
    have hAlBC : A ∈ line_through B C,
    {
      rw ← hPA,
      exact H.2.2,
    },
    have H1 : line_through A C = line_through B C,
    {
      exact equal_lines_of_contain_two_points hAC (line_through_left A C) hAlBC (line_through_right A C) (line_through_right B C),
    },
    have H2 : line_through A C = line_through A B, 
    {
      rw H1,
      exact equal_lines_of_contain_two_points hAB hAlBC (line_through_left A B) (line_through_left B C) (line_through_right A B),
    },
    exact h1 H2,
  },
  {
    have h2 : line_through A C = line_through A B, 
    {
      exact equal_lines_of_contain_two_points hPA H.2.1 H.1 (line_through_left A C) (line_through_left A B),
    },
    exact h1 h2,
  }
  -- sorry
end