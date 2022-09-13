
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p not_p,
  exact not_p p,
end

theorem doubleneg_elim : 
  ¬¬P → P  :=
begin
  intro not_not_p,
  by_cases h: P,
    -- Case P
    exact h,
    -- Case ¬P
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
    --Case P
    right,
    exact p,
    --Case Q
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
    --Case ¬P
    exfalso,
    exact np p,
    --Case Q
    exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros p_or_q np,
  cases p_or_q with p q,
    --Case P
    exfalso,
    exact np p,
    --Case Q
    exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros p_imp_q nq p,
  apply nq,
  exact p_imp_q p, 
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  := 
begin
  intros h p,
  by_cases q: Q,
    --Case Q
    exact q,
    --Case ¬Q
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
    --Demons PV¬P
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
  intros h np,
  apply np,
  apply h,
  intro p,
  exfalso,
  exact np p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros p_or_q np_and_nq,
  cases np_and_nq with np nq,
  cases p_or_q with p q,
    --Case P
    exact np p,
    --Case Q
    exact nq q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_and_q,
  intro np_or_nq,
  cases p_and_q with p q,
  cases np_or_nq with np nq,
    --Case P
    exact np p,
    --Case Q
    exact nq q,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  := 
begin
  intro n_p_or_q,
  split,
  --Parte ¬P
  intro p,
  apply n_p_or_q,
  left,
  exact p,
  --Parte ¬Q
  intro q,
  apply n_p_or_q,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros np_and_nq p_or_q,
  cases np_and_nq with np nq,
  cases p_or_q with p q,
    --Case P
    exact np p,
    --Case Q
    exact nq q,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  := 
begin
  intro n_p_and_q,
  by_cases h: Q,
    --Case Q
    right,
    intro p,
    apply n_p_and_q,
    split,
    exact p,
    exact h,
    --Case ¬Q 
    left,
    exact h,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros nq_or_np p_and_q,
  cases p_and_q with p q,
  cases nq_or_np with nq np,
    --Case P
    exact nq q,
    --Case Q
    exact np p,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
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
    --Case Q
    left,
    split,
    exact p,
    exact q,
    --case R
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
    --Case P∧Q
    cases p_and_q with p q,
    split,
    exact p,
    left,
    exact q,
    --Case PVQ
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
    --Case P
    split,
    left,
    exact p,
    left,
    exact p,
    --Case Q∧R
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
    --Case P
    left,
    exact p,
    --Case Q
    cases p_or_r with p r,
      --Case P
      left,
      exact p,
      --Case R
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
  intros h p q,
  exact h ⟨p,q⟩,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h p_and_q,
  cases p_and_q with p q,
  apply h,
  exact p,
  exact q,
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
  exact weaken_conj_right P P,
  intro p,
  split,
  repeat {exact p},
end

theorem disj_idempot :
  (P∨P) ↔ P  := 
begin
  split,
  intro p_or_p,
  cases p_or_p with p1 p2,
  --Case P(left)
  exact p1,
  --Case P(right)
  exact p2,
  exact weaken_disj_right P P,
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
  ¬(∃x, P x) → (∀x, ¬P x)  := 
begin
  intros h x p_x,
  apply h,
  existsi x,
  exact p_x,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h1 h2,
  cases h2 with x p_x,  
  have n_p_x := h1 x,
  exact n_p_x p_x,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h1,
  by_contra,
  apply h1,
  intro x,
  by_contra hboom,
  apply h,
  existsi x,
  exact hboom,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros h1 h2,
  cases h1 with x n_p_x,
  have p_x := h2 x,
  exact n_p_x p_x,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
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
  intros h1 h2,
  cases h1 with x p_x,
  have n_p_x := h2 x,
  exact n_p_x p_x,

end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h1 h2,
  cases h2 with x n_p_x,
  have p_x := h1 x,
  exact n_p_x p_x,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros h x,
  by_contra hboom,
  apply h,
  existsi x,
  exact hboom,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  by_contra hboom,
  apply h,
  intros x p_x,
  apply hboom,
  existsi x,
  exact p_x,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with x px_and_qx,
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
  intro h,
  cases h with x px_or_qx,
  cases px_or_qx with px qx,
    --Case P x
    left,
    existsi x,
    exact px,
    -- Case Q x
    right,
    existsi x,
    exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with p_x q_x,
    --Case ∃x, P x
    cases p_x with x px,
    existsi x,
    left,
    exact px,
    --Case ∃x, Q x
    cases q_x with x qx,
    existsi x,
    right,  
    exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro x,
  cases h x with px qx,
  exact px,
  intro x,
  cases h x with px qx,
  exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros h x,
  cases h with p_x q_x,
  split,
  exact p_x x,
  exact q_x x,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros h x,
  cases h with p_x q_x,
    --Case ∀x, P x
    left,    
    exact p_x x,
    --Case ∀x, Q x
    right,
    exact q_x x,
    
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
