section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro q,
  exact q p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  by_cases h : P,
  intro j,
  exact h,
  intro g,
  exfalso,
  exact g h,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  by_cases h : P,
  intro j,
  exact h,
  intro g,
  exfalso,
  exact g h,
  intro p,
  intro q,
  exact q p,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro poq,
  cases poq with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro peq,
  cases peq with p q,
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
  intro h,
  intro p,
  cases h with notp q,
  exfalso,
  exact notp p,
  exact q, 
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro poq,
  intro notp,
  cases poq with p q,
  exfalso,
  exact notp p,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro piq,
  intro nq,
  intro p,
  have q : Q := piq p,
  exact nq q,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro nqinp,
  intro p,
  by_contradiction hboom,
  have np := nqinp hboom,
  exact np p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro piq,
  intro nq,
  by_contradiction hboom,
  have q := piq hboom,
  exact nq q,
  intro nqinp,
  intro p,
  by_contradiction hboom,
  have np := nqinp hboom,
  exact np p,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_ponq,
  have r: P∨¬P,
  by_cases p:P,
  left,
  exact p,
  right,
  exact p,
  exact n_ponq r,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro piq_i_p,
  intro np,
  have piq : (P → Q),
  intro p,
  exfalso,
  exact np p,
  exact np(piq_i_p(piq)),
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro poq,
  by_contradiction npenq,
  cases npenq with np nq,
  cases poq with p q,
  exact np p,
  exact nq q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro peq,
  by_contradiction nponq,
  cases peq with p q,
  cases nponq with np nq,
  exact np p,
  exact nq q,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_poq,
  split,
  intro p,
  have poq : (P∨Q),
  left,
  exact p,
  exact n_poq poq,
  intro q,
  have poq : (P∨Q),
  right,
  exact q,
  exact n_poq poq,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npenq,
  cases npenq with np nq,
  by_contradiction poq,
  cases poq with p q,
  exact np p,
  exact nq q,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
sorry,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqonp,
  by_contradiction peq,
  cases nqonp with nq np,
  cases peq with p q,
  exact nq q,
  cases peq with p q,
  exact np p,
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
  intro pe_qor,
  cases pe_qor with p qor,
  cases qor with q r,
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
  intro peq_o_pe_qor,
  cases peq_o_pe_qor with peq per,
  cases peq with p q,
  split,
  exact p,
  left,
  exact q,
  split,
  cases per with p r,
  exact p,
  cases per with p r,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro po_qer,
  cases po_qer with p qer,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qer with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro poq_e_por,
  cases poq_e_por with poq por,
  cases poq with p q,
  left,
  exact p,
  cases por with p r,
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
  intro peq_i_r,
  intro p,
  intro q,
  have peq : P∧Q,
  split,
  exact p,
  exact q,
  exact peq_i_r peq,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro piqir,
  intro peq,
  cases peq with p q,
  have qir := piqir p,
  exact qir q,
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
  intro peq,
  cases peq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  cases peq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pep,
  cases pep with p1 p2,
  exact p1,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idemp :
  (P∨P) ↔ P  :=
begin
  split,
  intro pop,
  cases pop with p1 p2,
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
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro none_P,
  intro x,
  intro P,
  apply none_P,
  existsi x,
  exact P,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro all_nP,
  intro some_P,
  cases some_P with x P,
  have nP := all_nP x,
  exact nP P,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro some_dont_P, --exists x such that not P of x
  intro all_P,  --for all x, P of x
  cases some_dont_P with x nPx,
  have Px := all_P x,
  exact nPx Px,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro some_P,
  intro all_nP,
  cases some_P with x Px,
  have nPx := all_nP x, 
  exact nPx Px,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro all_P,
  intro some_nP,
  cases some_nP with x nPx,
  have Px := all_P x,
  exact nPx Px,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro none_nP,
  by_contradiction n_all_P,
  apply n_all_P,
  intro x,
  by_contradiction n_P,
  apply none_nP,
  existsi x,
  exact n_P,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro n_all_nP,
  by_contradiction none_P,
  apply n_all_nP,
  intro x,
  intro p,
  apply none_P,
  existsi x,
  exact p,  
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro all_P,
  intro some_nP,
  cases some_nP with x nP,
  apply nP,
  exact all_P x,
  intro none_nP,
  by_contradiction n_all_P,
  apply none_nP,
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
  intro some_P_e_Q,
  cases some_P_e_Q with x P_e_Q,
  cases P_e_Q with P Q,
  split,
  existsi x,
  exact P,
  existsi x,
  exact Q,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro some_PoQ,
  cases some_PoQ with x P_o_Q,
  cases P_o_Q with P Q,
  left,
  existsi x,
  exact P,
  right,
  existsi x,
  exact Q,

end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro someP_or_someQ,
  cases someP_or_someQ with some_P some_Q,
  cases some_P with x Px,
  existsi x,
  left,
  exact Px,
  cases some_Q with x Qx,
  existsi x,
  right,
  exact Qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro allP_e_allQ,
  split,
  intro x,
  have P_e_Q := allP_e_allQ x,
  cases P_e_Q with P Q,
  exact P,
  intro x,
  have P_e_Q := allP_e_allQ x,
  cases P_e_Q with P Q,
  exact Q,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro allP_e_allQ,
  cases allP_e_allQ with allP allQ,
  intro x,
  split,
  exact allP x,
  exact allQ x,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro allP_or_allQ,
  intro x,
  cases allP_or_allQ with allP allQ,
  left,
  exact allP x,
  right,
  exact allQ x,
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
