From Stdlib Require Import Arith.

Section lambda.

(*  DEFINIZIONE SINTASSI *)

Inductive lambda_type : Type :=
  | Bool : lambda_type
  | arrow_type : lambda_type -> lambda_type -> lambda_type.

Inductive lambda_term : Type :=
  | lambda_true : lambda_term
  | lambda_false : lambda_term
  | var : nat -> lambda_term
  | lam : nat -> lambda_type -> lambda_term -> lambda_term
  | app : lambda_term -> lambda_term -> lambda_term
  | lambda_if: lambda_term -> lambda_term -> lambda_term -> lambda_term.

(* NOTAZIONI *)

Notation "'trueH'" := (lambda_true)
  (at level 0).

Notation "'falseH'" := (lambda_false)
  (at level 0).

Notation "T1 '~>' T2" := (arrow_type T1 T2)
  (at level 99, right associativity).

Notation "'[' x ']'" := (var x)
  (at level 0, x at level 0).

Notation "t1 '@' t2" := (app t1 t2)
  (at level 11, left associativity).

Notation "'Lam' x ':' T '=>' body" := (lam x T body)
  (at level 200, x at level 0, T at level 99, body at level 200, right associativity).

Notation "'IF' c 'THEN' t1 'ELSE' t2" := (lambda_if c t1 t2)
  (at level 200, right associativity).

(* SOSTITUZIONE *)

Reserved Notation "{ x '<-' t } term" (at level 199).

Fixpoint subst (x : nat) (s : lambda_term) (t : lambda_term) : lambda_term :=
  match t with
  | trueH => trueH
  | falseH => falseH
  
  | [y] => if Nat.eqb x y then s else [y]

  | Lam y : T => body =>
    if Nat.eqb x y then
      Lam y : T => body
    else
      Lam y : T => {x <- s} body
        
  | t1 @ t2 => ({x <- s} t1) @ ({x <- s} t2)

  | IF c THEN t1 ELSE t2 =>
      IF ({x <- s} c) THEN ({x <- s} t1) ELSE ({x <- s} t2)
  end

where "{ x '<-' t } term" := (subst x t term).

(* Semantica operazionale call-by-value *)

Definition value (term : lambda_term) : Prop :=
  match term with
  | trueH => True
  | falseH => True
  | (Lam x : T => body) => True
  | _ => False
  end.

Inductive cbv : lambda_term -> lambda_term -> Prop :=
  | beta {x : nat} {v2 t1 : lambda_term} {T2 : lambda_type} :
    (value v2) ->
    cbv ((Lam x : T2 => t1) @ v2) ({x <- v2} t1)
  
  | app1 {t₁ t₁' t₂ : lambda_term} :
    cbv t₁ t₁' ->
    cbv (t₁ @ t₂) (t₁' @ t₂)

  | app2 {v₁ t₂ t₂' : lambda_term} :
    value v₁ ->
    cbv t₂ t₂' ->
    cbv (v₁ @ t₂) (v₁ @ t₂')
  
  | if_true {t₁ t₂ : lambda_term} :
    cbv (IF trueH THEN t₁ ELSE t₂) (t₁)

  | if_false {t₁ t₂ : lambda_term} :
    cbv (IF falseH THEN t₁ ELSE t₂) (t₂)
  
  | if_step {t₁ t₁' t₂ t₃: lambda_term} :
    cbv t₁ t₁' ->
    cbv (IF t₁ THEN t₂ ELSE t₃) (IF t₁' THEN t₂ ELSE t₃).

(* Funzione di valutazione riflessiva e transitiva *)

Reserved Notation "t₁ '->*' t₂" (at level 40).

Inductive eval : lambda_term -> lambda_term -> Prop :=
  | eval_refl : forall t,
    eval t t
  
  | eval_trans : forall t₁ t₂ t₃,
    cbv t₁ t₂ ->
    eval t₂ t₃ ->
    eval t₁ t₃

where "t₁ '->*' t₂" := (eval t₁ t₂).

(* TYPE SYSTEM *)

(**
  Definisco l'environment come una funzione da naturali a tipi del lambda calcolo.
  L'env vuoto è definito ritornando sempre None, invece la funzione update gestisce
  la modifica dentro l'env.
**)

Definition env : Type := (nat -> option lambda_type).
Definition empty_env : env := fun _ => None.
Definition update (x : nat) (T : lambda_type) (Γ : env) : env :=
  fun y =>
    if x =? y then
      Some T
    else
      Γ y.

Check update.

(**
    Definiamo l'inclusione tra env come: Γ ⊆ Γ' ⟺ ∀x.∀T. (Γ, x : T) -> (Γ', x : T)
**)

Definition env_included (Γ Γ' : env) : Prop :=
  forall (x : nat) (T : lambda_type), Γ x = Some T -> Γ' x = Some T.

Notation "Γ ⊆ Γ'" := (env_included Γ Γ') (at level 50, no associativity).

Reserved Notation "Γ '⊢' t 'in' T" (at level 40).

Inductive has_type : env -> lambda_term -> lambda_type -> Prop :=
  | base {Γ : env} {x : nat} {T : lambda_type} :
    Γ x = Some T ->
    Γ ⊢ [x] in T
  
  | true_type {Γ : env} :
    Γ ⊢ trueH in Bool
      
  | false_type {Γ : env} :
    Γ ⊢ falseH in Bool
      
  | lam_type {Γ : env} {x : nat} {term : lambda_term} {T₁ T₂ : lambda_type} :
    (update x T₁ Γ) ⊢ term in T₂ ->
    Γ ⊢ (Lam x : T₁ => term) in (T₁ ~> T₂)

  | app_type {Γ : env} {term₁ term₂ : lambda_term} {T₁ T₂ : lambda_type} :
    Γ ⊢ term₁ in (T₁ ~> T₂) -> 
    Γ ⊢ term₂ in T₁ ->
    Γ ⊢ (term₁ @ term₂) in T₂
      
  | if_type {Γ : env} {t₁ t₂ t₃ : lambda_term} {T : lambda_type} :
    Γ ⊢ t₁ in Bool ->
    Γ ⊢ t₂ in T ->
    Γ ⊢ t₃ in T ->
    Γ ⊢ (IF t₁ THEN t₂ ELSE t₃) in T
    
where "Γ '⊢' t 'in' T" := (has_type Γ t T).

(* Lemma per il primo teorema : T1 = (T1 ~> T2) -> False *)
Lemma type_no_cyclic :
  forall T1 T2 : lambda_type,
    T1 = (T1 ~> T2) -> False.
Proof.
  induction T1; intros T2 H.
    * discriminate H.
    * injection H as H1 H2.
      apply IHT1_1 in H1.
      exact H1.
Qed.

Theorem th1 :
  ~ ( exists S T : lambda_type,
    forall x : nat,
      empty_env ⊢ (Lam x : S => ([x] @ [x])) in T).
Proof.
  intros H.
  destruct H as [S [T H]].
  specialize (H 0).

  (* sviluppiamo l'albero di tipaggio fino a derivare i tipi S e T *)
  inversion H; subst.
  inversion H5; subst.

  inversion H3; subst.
  inversion H6; subst.

  (* calcoliamo i tipi *)
  injection H2 as HP1.
  injection H4 as HP2.

  (* dimostriamo l'assurdo : (T₁ = (T₁ ~> T₂) -> False) *)
  rewrite HP1 in HP2.
  apply type_no_cyclic with (T2 := T₂) (T1 := T₁).

  symmetry.
  exact HP2.

Qed.

(* Definisco delle variabili con valori arbitrari da usare nel secondo teorema *)
Definition x := 0.
Definition y := 1.
Definition z := 2.

Theorem th2 {B : lambda_type} :
  empty_env ⊢ Lam x : Bool ~> B =>
    Lam y : Bool ~> Bool =>
      Lam z : Bool =>
        [x] @ ([y] @ [z]) in ((Bool ~> B) ~> (Bool ~> Bool) ~> Bool ~> B).
Proof.
  unfold x.
  unfold y.
  unfold z.

  (* Il tipaggio si ottiene applicando correttamente le regole del type system *)

  apply lam_type.
  apply lam_type.
  apply lam_type.

  eapply app_type.
    - apply base.
      compute.
      reflexivity.
    
    - eapply app_type.

      + apply base.
        compute.
        reflexivity.
      
      + apply base.
        compute.
        reflexivity.
Qed.

(* Usiamo una x arbitraria come variabile e dimostriamo applicando le regole di cbv *)

Theorem th3 :
  ((Lam x : Bool ~> Bool => [x]) @
    ((Lam x : Bool => IF [x] THEN falseH ELSE trueH) @ trueH)) ->* falseH.

Proof.

  eapply eval_trans.
    - eapply app2.
        + compute.
          exact I.
        
        + eapply beta.
          compute.
          exact I.
    
    - eapply eval_trans.
        + eapply app2.
            * compute.
              exact I.
            * eapply if_true.
        
        + eapply eval_trans.
            * eapply beta.
              compute.
              exact I.
            * eapply eval_refl.
Qed.

(**
    Per dimostrare la subject reduction reduction abbiamo bisogno di alcuni
    lemmi preliminari tra i quali il substitution lemma.
    
    Dimostriamo inizialmente che dati due env tali che Γ ⊆ Γ', se un termine t ha tipo T in Γ,
    allora mantiene lo stesso tipo T nell'insieme Γ' che è più grande.
**)

Lemma weakening :
  forall (Γ : env) (t : lambda_term) (T : lambda_type),
    Γ ⊢ t in T ->
      forall Γ' : env, (* Lo scrivo qua per applicare l'induzione da questo punto*)
        Γ ⊆ Γ' ->
          Γ' ⊢ t in T.
Proof.
  intros Γ t T H.

  (* Per induzione sull'albero di tipaggio *)
  induction H.
    * intros Γ' H0.
      apply base.
      apply H0.
      exact H.
    * intros Γ' H. apply true_type.
    * intros Γ' H. apply false_type.
  
  (* Per il caso lambda abbiamo due sottocasi in base a come si ramifica update *)
  
    * intros Γ' H0.
      apply lam_type.
      apply IHhas_type.

      unfold update in *.
      unfold env_included in *.

      intros x1 T H1.
      destruct (x0 =? x1).
        + exact H1.
        + apply H0. exact H1.
  
    * intros Γ' H1.
        eapply app_type.
          + apply IHhas_type1. exact H1.
          + apply IHhas_type2. exact H1.
  
    * intros Γ' H2.
      eapply if_type.
        + apply IHhas_type1. exact H2.
        + apply IHhas_type2. exact H2.
        + apply IHhas_type3. exact H2.
Qed.

(** Dimostriamo che dato un tipaggio in un ambiente vuoto, lo stesso tipaggio
    lo possiamo ottenere in un ambiente non vuoto. è un caso particolare del
    lemma precedente.
**)

Lemma weakening_empty :
  forall (Γ : env) (t : lambda_term) (T : lambda_type),
    empty_env ⊢ t in T -> 
      Γ ⊢ t in T.
Proof.
  intros.
  eapply weakening.
    + exact H.
    + unfold env_included.
      intros x0 T0 H0.
      discriminate.
Qed.

(** Dimostrazione del lemma di sostituzione. Per evitare di dover gestire la
    cattura di variabile assumiamo che t' sia tipato in un ambiente vuoto.
**)

Lemma substitution_lemma :
  forall t x t' A B Γ,
    ((update x B Γ) ⊢ t in A) /\ (empty_env ⊢ t' in B) ->
      Γ ⊢ {x <- t'} t in A.
Proof.

  (* Per induzione sul termine t *)
  induction t; intros x t' A B Γ H; destruct H as [H_typeA H_typeB]; simpl.
    * inversion H_typeA; subst; apply true_type. (* Caso t = true_type *)
    * inversion H_typeA; subst; apply false_type. (* Caso t = false_type *)
    
    (* Caso t = var, ci sono i due sottocasi se x = n o se x != n *)
    * unfold update in *.
      destruct (x =? n) eqn:Heq.
        + inversion H_typeA; subst.
          rewrite Heq in H1.
          injection H1 as H1.
          subst.
          apply weakening_empty.
          exact H_typeB.
        
        + inversion H_typeA; subst.
          rewrite Heq in H1.
          apply base.
          exact H1.
    
    (* Caso t = lambda type *)
    * destruct (x =? n) eqn:Heq.
        + inversion H_typeA; subst.
          apply lam_type.
          eapply weakening.
            - exact H4.
            - intros y U H.
              unfold update in *.
              apply Nat.eqb_eq in Heq.
              subst x.
              destruct (n =? y).
              -- exact H.
              -- exact H.
        + inversion H_typeA; subst.
          apply lam_type.
          eapply IHt.
          split.
            - eapply weakening.
                --  exact H4.
                --  intros y U H.
                    unfold update in *.
                    destruct (x =? y) eqn:Hxy.
                      ++  apply Nat.eqb_eq in Hxy.
                          destruct (n =? y) eqn:Hny.
                          +++ apply Nat.eqb_eq in Hny.
                              apply Nat.eqb_neq in Heq.
                              congruence.
                          +++ exact H.
                      ++ exact H.
            - exact H_typeB.

    (* Caso t = tipo applicazione *)
    
    * inversion H_typeA; subst.
      eapply app_type.
        + eapply IHt1.
          split.
            - exact H2.
            - exact H_typeB.
        + eapply IHt2.
          split.
            - exact H4.
            - exact H_typeB.
    
    (* Caso t = tipo if then else *)
    
    * inversion H_typeA; subst.
        eapply if_type.
          + eapply IHt1; split.
              - exact H3.
              - exact H_typeB.
          + eapply IHt2; split.
              - exact H5.
              - exact H_typeB.
          + eapply IHt3; split.
              - exact H6.
              - exact H_typeB.
Qed.

(**
    Dimostrazione che un singolo passo di valutazione dei termini preserva il tipo.
**)

Lemma preservation_cbv :
  forall t t' : lambda_term,
    (cbv t t') ->
      forall T : lambda_type,
        (empty_env ⊢ t in T) ->
            (empty_env ⊢ t' in T).
Proof.
  intros t t' H_step.
  
  (* Per induzione sull'albero di valutazione *)
  induction H_step; intros T H_type.

  (* Caso beta*)
  - inversion H_type; subst.
    inversion H3; subst.
    eapply substitution_lemma.
    + split.
      * exact H2.
      * exact H5.

  (* Caso app1 *)
  - inversion H_type; subst.
    eapply app_type.
    + apply IHH_step. exact H2.
    + exact H4.

  (* Caso app2 *)
  - inversion H_type; subst.
    eapply app_type.
    + exact H3.
    + apply IHH_step. exact H5.

  (* Caso if_true *)
  - inversion H_type; subst.
    exact H5.

  (* Caso if_false *)
  - inversion H_type; subst.
    exact H6.

  (* Caso if_step *)
  - inversion H_type; subst.
    eapply if_type.
    + apply IHH_step. exact H3.
    + exact H5.
    + exact H6.
Qed.

Theorem subject_reduction :
  forall t t' : lambda_term, forall T : lambda_type,
    ((empty_env ⊢ t in T) /\ (t ->* t')) -> empty_env ⊢ t' in T.
Proof.
  intros t t' T.
  intro H.
  
  destruct H as [H_type H_eval].
  
  induction H_eval.
    * assumption.
    * apply IHH_eval.
      eapply preservation_cbv.
      + exact H.
      + exact H_type.
Qed.

