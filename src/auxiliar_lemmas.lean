import incidenceplane
open IncidencePlane 

variables {Ω : Type} [IncidencePlane Ω]

lemma equal_lines_of_contain_two_points {A B : Ω} {r s : Line Ω} :
A ≠ B → A ∈ r →  A ∈ s → B ∈ r → B ∈ s → 	r = s :=
λ hAB hAr hAs hBr hBs, by rwa [incidence hAB hAr hBr, incidence hAB hAs hBs]