import LeanTestground.Basic

noncomputable def another_path {A : Sort u} (v : A) : path.{u, 1} v v := by
  intro P x
  classical
  exact if h : P v = Bool then
    cast h.symm (!(cast h x))
  else
    x

theorem another_path_ne_id {A : Sort u} (v : A) :
    another_path v ≠ id_path v := by
  intro heq
  have hx := congrFun (congrFun heq (fun _ ↦ Bool)) true
  simp [another_path, id_path] at hx

theorem exists_another_path {A : Sort u} (v : A) :
    ∃ p : path.{u, 1} v v, p ≠ id_path v :=
  ⟨another_path v, another_path_ne_id v⟩

theorem there_must_not_be_another_path_is_false {A : Sort u} (v : A) :
    ¬ ((∃ p : path.{u, 1} v v, p ≠ id_path v) → False) := by
  intro h
  exact h (exists_another_path v)

theorem prop_path_unique {A : Sort u} (v : A) (p : path.{u, 0} v v) :
    p = id_path v := by
  funext P x
  exact proof_irrel _ _

theorem there_must_not_be_another_prop_path {A : Sort u} (v : A) :
    (∃ p : path.{u, 0} v v, p ≠ id_path v) → False := by
  rintro ⟨p, hp⟩
  exact hp (prop_path_unique v p)

#print axioms another_path_ne_id
#print axioms exists_another_path
#print axioms there_must_not_be_another_path_is_false
#print axioms there_must_not_be_another_prop_path
#print there_must_not_be_another_path
#print axioms there_must_not_be_another_path
