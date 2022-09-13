
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro not_p,
  exact not_p p,
end

theorem doubleneg_elim : -- OLHAR ESSE BY_CASES
  ¬¬P → P  :=
begin
  intro not_not_p,
  by_cases h: P,
  exact h,
  exfalso,
  exact not_not_p h,
  
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,

end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p_or_q,
  cases p_or_q with p q,
  right,
  exact p,
  left,
  exact q,  
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p_and_q,
  cases p_and_q with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro np_or_q,
  intro p,
  cases np_or_q with np q,
  contradiction,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro p_or_q,
  intro np,
  cases p_or_q with p q,
  contradiction,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro p_imp_q,
  intro nq,
  intro p,
  have q:= p_imp_q p,
  contradiction,  
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  := -- OLLHAR ESSE BY_CASES
begin
  intro h,
  intro p,
  by_cases q: Q,
  exact q,
  have np := h q,
  exfalso,
  exact np p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  right,
  intro p,
  have p_or_np: P∨¬P,
  left,
  exact p,
  exact h p_or_np,  
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro np,
  have p_imp_q: P→Q,
  intro p,
  contradiction,
  have p := h p_imp_q,
  exact np p, 
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro p_or_q,
  intro np_and_nq,
  cases np_and_nq with np nq,
  cases p_or_q with p q,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_and_q,
  intro np_or_nq,
  cases p_and_q with p q,
  cases np_or_nq with np nq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  := --olhar como contornar essas repetições
begin
  intro n_p_or_q,
  split,
  intro p,
  have p_or_q: P∨Q,
  left,
  exact p,
  contradiction,
  intro q,
  have p_or_q: P∨Q,
  right,
  exact q,
  contradiction,  
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro np_and_nq,
  intro p_or_q,
  cases np_and_nq,
  cases p_or_q with p q,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nq_or_np,
  intro p_and_q,
  cases p_and_q with p q,
  cases nq_or_np with np nq,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  sorry,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p q_or_r,
  cases q_or_r with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with p_and_q p_and_r,
  cases p_and_q with p q,
  split,
  exact p,
  left,
  exact q,
  cases p_and_r with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h with p q_and_r,
  split,
  left,
  exact p,
  left,
  exact p,
  cases q_and_r with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with p_or_q p_or_r,
  cases p_or_q with p q,
  left,
  exact p,
  cases p_or_r with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro p,
  intro q,
  have p_and_q: P∧Q, -- olhar se nao dá para encontrar direto P∧Q sem ter que demonstrar
  split,
  exact p,
  exact q,
  exact h p_and_q,  
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h,
  intro p_and_q,
  cases p_and_q with p q,
  have q_imp_r := h p,
  exact q_imp_r q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro p_and_q,
  cases p_and_q with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p_and_q,
  cases p_and_q with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p_and_p,
  cases p_and_p with p1 p2,
  exact p1,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro p_or_p,
  cases p_or_p with p1 p2,
  exact p1,
  exact p2,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  := -- Olhar de novo
begin
  intro h,
  intro x,
  intro p_x,
  apply h,
  existsi x,
  exact p_x,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h1,
  intro h2,
  cases h2 with x p_x,
  have n_p_x := h1 x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,  
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h1,
  intro h2,
  cases h1 with x n_p_x,
  have p_x := h2 x,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,

end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h1,
  intro h2,
  cases h1 with x p_x,
  have n_p_x := h2 x,
  contradiction,

end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h1,
  intro h2,
  cases h2 with x n_p_x,
  have p_x := h1 x,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h1,
  cases h1 with x px_and_qx,
  cases px_and_qx with p_x q_x,
  split,
  existsi x,
  exact p_x,
  existsi x,
  exact q_x,  

end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h1,
  cases h1 with x px_or_qx,
  cases px_or_qx with px qx,
  left,
  existsi x,
  exact px,
  right,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h1,
  cases h1 with p_x q_x,
  cases p_x with x px,
  existsi x,
  left,
  exact px,
  cases q_x with x qx,
  existsi x,
  right,  
  exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h1,
  split,
  intro x,
  have px_and_qx := h1 x,
  cases px_and_qx with px qx,
  exact px,
  intro x,
  have px_and_qx := h1 x,
  cases px_and_qx with px qx,
  exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h1,
  intro x,
  cases h1 with p_x q_x,
  split,
  have px := p_x x,
  exact px,
  have qx := q_x x,
  exact qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h1,
  intro x,
  cases h1 with p_x q_x,
  left,
  have px := p_x x,
  exact px,
  right,
  have qx := q_x x,
  exact qx,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
