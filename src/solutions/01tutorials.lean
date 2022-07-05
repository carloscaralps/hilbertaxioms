import incidenceplane
open IncidencePlane set

variables {Ω : Type} [IncidencePlane Ω]

/-
We will start by practising with the simplest tactic, namely *refl*. This just proves goals
of the form $A = A$, no matter how complicated $A$ is. Let's see it in action!
-/

/- Lemma : no-side-bar
If A is a point, then A = A.
-/
lemma refl_example (A : Ω) : A = A :=
begin
  -- sorry
  refl,
  -- sorry
end

/-
The next tactic we will learn is `rw` (from rewrite). It rewrites equalities. That is,
if we have a proof `h : A = B` and we want to prove `⊢ A = C`, then after `rw h` the goal
will become `⊢ B = C`.

After many tactics (and `rw` is one of them) Lean tries to apply `refl`. This is why
in the following proof you may get away with only two tactic applications.

-/

/- Hint : Click here for a hint, in case you get stuck.
Delete `sorry` and type `rw h,` (don't forget the comma!). Lean tries `refl` afterwards,
so you will see that this suffices.
-/



/- Lemma : no-side-bar
If A, B and C are points with A = B and B = C, then A = C.
-/
lemma example_rw (A B C : Ω) (h1 : A = B) (h2 : B = C) : A = C :=
begin
  -- sorry
  rw h1,
  rw h2,
  -- sorry
end

/-
Let's practice a little bit more with the `rw` tactic. The hypotheses in this level are
a bit different than before, so you should use `rw ←` instead. You can
type the little arrow by typing \l, and the system will change it automatically.
-/

/- Lemma : no-side-bar
If A, B and C are points with B = C and B = C, then A = C.
-/
lemma example_exact (A B C: Ω) (h1 : B = A) (h2 : B = C) : A = C :=
begin
  -- sorry
  rw ←h1,
  rw h2,
  -- sorry
end

/-
In this level we learn the tactic `exact`, which solves a goal that is exactly one of the hypotheses.
The lemma is the same as in the previous level, but we will solve it in a different way.
-/

/- Lemma : no-side-bar
If A, B and C are points with A = B and B = C, then A = C.
-/
lemma example_exact' (A B C: Ω) (h1 : A = B) (h2 : B = C) : A = C :=
begin
  -- sorry
  rw h1,
  exact h2,
  -- sorry
end

/-
We can apply a theorem that we have already proven by using `exact`
and the appropriate hypotheses.
-/

/- Lemma :  no-side-bar
A point lies in the line through it.
-/
lemma point_on_line {A B : Ω} {r : Line Ω} :
B ∈ line_through A B :=
begin
  -- sorry
  exact line_through_right A B,
  -- sorry
end

/-
This level introduces the `intros` tactic. This allows you to introduce
a new hypothesis in the context. You can learn more about it in the side bar.
-/

/- Lemma :
If two lines contain two distinct points, then they are the same
-/
lemma equal_lines_of_contain_two_points {A B : Ω} {r s : Line Ω} :
A ≠ B → A ∈ r →  A ∈ s → B ∈ r → B ∈ s → 	r = s :=
begin
  -- sorry
  intros hAB hAr hAs hBr hBs,
  rw incidence hAB hAr hBr,
  rw incidence hAB hAs hBs,
  -- sorry
end

/-
In this level we will learn the `split` tactic. It breaks a goal `P ∧ Q` into two goals (proving `P`, and then proving `Q`),
and also breaks goals of the form `P ↔ Q` into proving each of the implications separately.
-/

/- Lemma : no-side-bar
If two lines contain two distinct points, then they are the same
-/
lemma line_through_contains_points (P Q : Ω) : P ∈ (line_through P Q) ∧ Q ∈ (line_through P Q)
:=
begin
  -- sorry
  split,
  exact line_through_left P Q,
  exact line_through_right P Q,
  -- sorry
end

/-
We have seen how to prove a goal of the form `P ∧ Q`, now you will learn how to prove
a goal of the form `P ∨ Q`, which means that either `P` holds or `Q` holds.
In this case, you will have to decide whether you can prove `P` or `Q`. The `left` and `right`
tactics will allow you to change the goal to ⊢ P or ⊢ Q accordingly.

The theorem `mem_singleton_iff` may be useful depending on how you set things up.
-/

/- Lemma : no-side-bar
An example of the usage of left/right
-/
lemma left_right_example (A B C : Ω) (h : C ∈ line_through A B) :
A = C ∨ collinear ({A, B, C} : set Ω) :=
begin
  -- sorry
  right,
  use line_through A B,
  intros P hP,
  cases hP,
  {
    rw hP,
    exact line_through_left A B
  },
  cases hP,
  {
    rw hP,
    exact line_through_right A B,
  },
  {
    rw mem_singleton_iff at hP,
    rw hP,
    exact h,
  }
  -- sorry
end

/-
Sometimes we will need to prove that there exists an object satisfying certain properties.
The goal will then look like ⊢ ∃ x, P x. In this case, the `use` tactic is useful. If we know
that an object `a` satisfies the  property `P`, then `use a` will transform the goal into ⊢ P a.
-/

/- Lemma : no-side-bar
Given a point, there is always a line containing it.
-/
lemma line_containing_point (P : Ω) : ∃ ℓ : Line Ω, P ∈ ℓ :=
begin
  -- sorry
  use line_through P P,
  exact line_through_left P P,
  -- sorry
end

/-
In this level we introduce the new tactic `have`. It is used to add a new hypothesis
to the context (of course, you will have to prove it!). This is sometimes useful to
structure our proofs. In this particular level, it is convenient to prove first that
`r = line_through B C`, then that `s = line_through B C` and that allows us to
finish the prove very easily.
-/

/- Lemma : no-side-bar
If two lines share two distinct points then they are the same
-/
lemma equal_lines_example (B C : Ω) (h : B ≠ C) (r s : Line Ω)
(h1 :  B ∈ r ∧ C ∈ r)
(h2 : B ∈ s ∧ C ∈ s)
: r = s :=
begin
  -- sorry
  have hr : r = line_through B C,
  {
    exact incidence h h1.1 h1.2,
  },
  have hs : s = line_through B C,
  {
    exact incidence h h2.1 h2.2,
  },
  rw hr,
  rw hs,
  -- sorry
end

/-
The next tactic we introduce is `cases`, and since it does many things
we will have a couple levels seeing when to apply it. This tactic works
always on hypotheses, and it transforms them in different ways. The first
instance that we learn arises when you have a hypothesis that says that `P`
or `Q` holds. That is, you have `h : P ∧ Q`. Then `cases h with h₁ h₂` will 
replace `h` with two new hypotheses, namely `h₁ : P` and `h₂ : Q`.

This is done usually for aesthetic reasons, since `h.1` and `h.2` also serve
as proofs of `P` and `Q`.
-/

/- Lemma : no-side-bar
...
-/
lemma line_through_from_and (P Q : Ω) (ℓ : Line Ω) (h1 : P ≠ Q)
(h2 : P ∈ ℓ ∧ Q ∈ ℓ) : ℓ = line_through P Q :=
begin
  -- sorry
  cases h2 with hP hQ,
  exact incidence h1 hP hQ,
  -- sorry
end

/-
Suppose now that your hypothesis says that `P`
**or** `Q` holds. That is, you have `h : P ∨ Q`. Then `cases h` will
create two new goals, and in each of them it will
replace `h` with `h : P` in the first case, and with `h : Q` in the second.

-/

/- Lemma : no-side-bar
If X is any set in Ω and either P or Q is in X, then X is not empty.
-/
lemma nonempty_example (P Q : Ω) (X : set Ω) (h : P ∈ X ∨ Q ∈ X) : ∃ R, R ∈ X :=
begin
  -- sorry
  cases h,
  {
    use P,
    exact h
  },
  {
    use Q,
    exact h
  }
  -- sorry
end

/-
Suppose now that your hypothesis says there is some element `x` satisfying a certain
property `P`. That is, you have `h : ∃ x, P x`. Then `cases h with x hx` will
replace `h` with `x : X` and `hx : P x`. That is, from the fact that you know that
some `x` exists, it will give you one such `x` with the property that it is supposed
to satisfy.

-/

/- Lemma :
...
-/
lemma exists_line_example (P Q R S : Ω) (h : Q ≠ R) (h1 : ∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ ∧ R ∈ ℓ)
(h2 : ∃ ℓ : Line Ω, Q ∈ ℓ ∧ R ∈ ℓ ∧ S ∈ ℓ) :
∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ ∧ R ∈ ℓ ∧ S ∈ ℓ :=
begin
  -- sorry
  cases h1 with r hr,
  cases h2 with s hs,
  have hr' : r = line_through Q R,
  {
    apply incidence h hr.2.1 hr.2.2,
  },
  have hs' : s = line_through Q R,
  {
    apply incidence h hs.1 hs.2.1,
  },
  have H : r = s,
  {
    rw hr',
    rw hs',
  },
  use r,
  split,
  exact hr.1,
  split,
  exact hr.2.1,
  split,
  exact hr.2.2,
  rw H,
  exact hs.2.2,
  -- sorry
end

/-
In this level we introduce the new tactic `apply`. Suppose that you have a theorem `h`
that states exactly that your goal is true, provided that some hypotheses are satisfied. Then
`apply h` will change your goal into proving your new hypotheses.
-/

/- Lemma :
The line through two points is a symmetrical concept
-/
lemma line_through_symmetrical {P Q : Ω} (h : P ≠ Q) : line_through Q P = line_through P Q :=
begin
  -- sorry
  apply incidence,
  exact h,
  exact line_through_right Q P,
  exact line_through_left Q P,
  -- sorry
end

/-
In this level we introduce a high level tactic called `simp`. This simplifies statements
using (some) lemmas already in our database. As a simple example, for `S` a segment we have a lemma
`mem_pts : P ∈ S ↔ P = S.A ∨ P = S.B ∨ (S.A * P * S.B)`, and it is tagged as a simp lemma
in this game. This means that the `simp` tactic will replace occurrences of `P ∈ S` with
the right-hand side, which is more concrete. Try it below.
-/

/- Lemma : no-side-bar
A point in between the endpoints of a segment is in the segment.
-/
lemma simp_example (P : Ω) (S : Segment Ω) (h : S.A * P * S.B) : P ∈ S :=
begin
  -- sorry
  simp,
  right,
  right,
  exact h,
  -- sorry
end

/-
In this level we introduce the new tactic `exfalso`. Look at what it does, it is a bit
strange at first. We will also need one of the axioms for our plane, the one that says that
the line through two points contains each of them. You can see the statement of this theorem
on the left sidebar.
-/

/- Lemma : no-side-bar
Prove that 2+2 is 5, using a false hypothesis.
-/
lemma two_plus_two_equals_five (P Q : Ω) (h: P ∉ line_through P Q) : 2 + 2 = 5:=
begin
  -- sorry
  exfalso,
  apply h,
  exact line_through_left P Q,
  -- sorry
end 

/-
This is an extra level you can use for practice.
-/

/- Lemma :
The only point on the segment A⬝A is A itself.
-/
lemma one_point_segment (A B : Ω) : B ∈ A⬝A ↔ B = A :=
begin
  -- sorry
  split,
  {
    intro hx,
    cases hx,
    {
      exact hx,
    },
    {
      cases hx,
      {
        exact hx,
      },
      {
        exfalso,
        apply (different_of_between hx).2.1,
        refl,
      }
    }
  },
  {
    intro h,
    rw h,
    left,
    refl,
  },
  -- sorry
end