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
  sorry
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
  sorry
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
  sorry
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
  sorry
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
  sorry
end

/-
Using the lemma we have just proved, we can now prove the following theorem.
-/

/- Theorem :
Given a point `P`, there are at least two different lines that pass through it.
-/
theorem point_exists_two_lines {P : Ω} : ∃ (r l: Line Ω), P ∈ l ∧ P ∈ r ∧ l ≠ r :=
begin
  sorry
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
  sorry
end
