From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var (x : var)
| Lam (m : {bind term})
| App (m n : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

Inductive clo : Type :=
| Clo : term -> list (option clo) -> clo.

Definition env : Type := list (option clo).
Definition stack : Type := list clo.
Definition konfig : Type := term * env * stack.

Notation "m ::: ms" := (Some m :: ms) (right associativity, at level 30).

Inductive step : term -> term -> Prop :=
| step_app m m' n :
  step m m' ->
  step (App m n) (App m' n)
| step_beta m n :
  step (App (Lam m) n) m.[n/].

Inductive kam : konfig -> konfig -> Prop :=
| kam_lam m e c s :
  kam (Lam m, e, c :: s) (m, c ::: e, s)
| kam_app m n e s :
  kam (App m n, e, s) (m, e, Clo n e :: s)
| kam_var x e e' m s :
  nth None e x = Some (Clo m e') ->
  kam (Var x, e, s) (m, e', s).

Notation sred := (star step).
Notation kred := (star kam).

Ltac step_simpl1 :=
  match goal with
  | [ |- step (App (Lam _) _) _ ] => apply step_beta
  | [ |- step (App _ _) _ ] => apply step_app
  end.
Ltac step_simpl := repeat (progress step_simpl1).
Ltac step_solve :=
  repeat
    (eauto;
     match goal with
     | [ |- sred (App (Lam _) _) _ ] =>
         eapply star_trans;[apply star1; apply step_beta|asimpl]
     | [ |- sred (App _ _) _ ] =>
         eapply star_trans;[apply star1; apply step_app; step_simpl|asimpl]
     | [ |- sred _ _ ] => eauto
     end).

Ltac kam_simpl := try eapply star_trans; [eapply star1; solve[constructor; asimpl; eauto]|asimpl].
Ltac kam_solve := repeat progress (kam_simpl; eauto).

Example step_ex1 :
  sred (App (Lam (Var 0)) (Lam (Var 0))) (Lam (Var 0)).
Proof. step_solve. Qed.

Example kam_ex1 :
  kred (App (Lam (Var 0)) (Lam (Var 0)), nil, nil) (Lam (Var 0), nil, nil).
Proof. kam_solve. Qed.

Example step_ex2 :
  sred (App (App (Lam (Lam (Var 1))) (Lam (Var 0))) (Var 2)) (Lam (Var 0)).
Proof. step_solve. Qed.

Example kam_ex2 :
  kred (App (App (Lam (Lam (Var 1))) (Lam (Var 0))) (Var 2), nil, nil) (Lam (Var 0), nil, nil).
Proof. kam_solve. Qed.

Example step_ex3 :
  sred (App (Lam (Lam (Var 1))) (Lam (Var 0))) (Lam (Lam (Var 0))).
Proof. step_solve. Qed.

Example kam_ex3 :
  kred (App (Lam (Lam (Var 1))) (Lam (Var 0)), nil, nil)
       (Lam (Var 1), Clo (Lam (Var 0)) nil ::: nil, nil).
Proof. kam_solve. Qed.

Example step_ex4 :
  sred (App (Lam (Lam (App (Var 5) (Var 1)))) (Var 7)) (Lam (App (Var 4) (Var 8))).
Proof. step_solve. Qed.

Example kam_ex4 :
  kred (App (Lam (Lam (App (Var 5) (Var 1)))) (Var 7), nil, nil)
       (Lam (App (Var 5) (Var 1)), Clo (Var 7) [::] ::: [::], [::]).
Proof. kam_solve. Qed.

Inductive resolve_env : env -> (var -> term) -> Prop :=
| resolve_env_nil :
  resolve_env nil ids
| resolve_some n e e' σ σ' :
  resolve_env e σ ->
  resolve_env e' σ' ->
  resolve_env (Clo n e' ::: e) (n.[σ'] .: σ)
| resolve_none x e σ :
  resolve_env e σ ->
  resolve_env (None :: e) (x .: σ).

Inductive resolve_stack : term -> stack -> term -> Prop :=
| resolve_stack_nil m : resolve_stack m nil m
| resolve_cons m m' n e σ s :
  resolve_env e σ ->
  resolve_stack (App m n.[σ]) s m' ->
  resolve_stack m (Clo n e :: s) m'.

Inductive resolve : term -> env -> stack -> term -> Prop :=
| Resolve x y e s σ :
  resolve_env e σ ->
  resolve_stack x.[σ] s y ->
  resolve x e s y.

Inductive shift : term -> env -> term -> Prop :=
| shift_nil m e σ :
  resolve_env e σ ->
  shift m e m.[σ]
| shift_cons m m' n σ' e e' :
  resolve_env e' σ' ->
  shift (Lam m) e m' ->
  shift m (Clo n e' ::: e) (App m' n.[σ']).

Example res_ex1 :
  resolve (Lam (Var 1)) (Clo (Lam (Var 0)) nil ::: nil) nil (Lam (Lam (Var 0))).
Proof.
  econstructor.
  constructor.
  constructor.
  constructor.
  asimpl.
  constructor.
Qed.

Example res_ex2 :
  resolve (Lam (Lam (Var 1))) nil (Clo (Lam (Var 0)) nil :: nil) (App (Lam (Lam (Var 1))) (Lam (Var 0))).
Proof.
  econstructor.
  constructor.
  asimpl.
  replace (Lam (Var 0)) with (Lam (Var 0)).[ids] by autosubst.
  econstructor.
  constructor.
  constructor.
Qed.

Example res_ex3 :
  resolve (Lam (App (Var 5) (Var 1))) (Clo (Var 7) [::] ::: [::]) [::] (Lam (App (Var 4) (Var 8))).
Proof.
  econstructor.
  constructor.
  econstructor.
  econstructor.
  asimpl.
  constructor.
Qed.

Lemma resolve_refl m : resolve m nil nil m.
Proof.
  econstructor.
  constructor.
  asimpl.
  constructor.
Qed.

Lemma shift_resolve m m' e :
  shift m e m' -> exists x, resolve m e nil x /\ sred m' x.
Proof with eauto.
  elim=>{m e m'}.
  { move=>m e σ rs. exists m.[σ]. split...
    econstructor...
    constructor. }
  { move=>m m' n σ' e e' rs1 sh[x[rs2 rd]]. inv rs2.
    inv H0. asimpl in rd.
    exists (m.[up σ]).[n.[σ']/]. split.
    econstructor.
    constructor...
    asimpl. constructor.
    apply: star_trans.
    apply: (star_hom (App^~ n.[σ'])) rd=>x y.
    apply: step_app.
    apply: star1.
    apply: step_beta. }
Qed.

Lemma resolve_stack_shift m m' n e s :
  resolve_stack m' s n -> shift m e m' ->
  exists x, resolve m e s x /\ sred n x.
Proof with eauto.
  move=>rs/shift_resolve[x[rs' rd]]. inv rs'. inv H0.
  elim: rs m e σ rd H=>{m' s n}.
  { move=>m m0 e σ rd rs. exists m0.[σ]. split...
    econstructor...
    econstructor. }
  { move=>m m' n e σ s rs1 rs2 ih m0 e0 σ0 rd rs3.
    assert (sred (App m n.[σ]) (App m0.[σ0] n.[σ]).[ids]).
    { asimpl. apply: star_trans.
      apply: (star_hom (App^~ n.[σ])) rd=>x y.
      apply: step_app.
      eauto. }
    have[x[rs rdx]]:=ih _ _ _ H (resolve_env_nil).
    inv rs. inv H0. asimpl in H1.
    exists x. split...
    econstructor...
    econstructor... }
Qed.

Lemma resolve_stack_ok m n n' e e' σ σ' s :
  resolve_stack (App (Lam m.[up σ]) n'.[σ']) s n ->
  resolve_env e σ -> resolve_env e' σ' ->
  exists x, resolve m (Clo n' e' ::: e) s x /\ sred n x.
Proof with eauto.
  intros.
  apply: resolve_stack_shift...
  constructor...
  replace (Lam m.[up σ]) with (Lam m).[σ] by autosubst.
  constructor...
Qed.

Lemma resolve_env_ok e e' x m σ :
  resolve_env e σ ->
  nth None e x = Some (Clo m e') ->
  exists σ', resolve_env e' σ' /\ σ x = m.[σ'].
Proof with eauto.
  move=>rs. elim: rs e' x m=>{e σ}.
  { move=>e' [|x] m//=eq. }
  { move=>n e e' σ σ' rs1 ih1 rs2 ih2 e'0 [|x] m//=eq...
    inv eq. exists σ'. split... }
  { move=>x e σ rs ih e' [|n] m//=eq.
    have[σ'[rs' eq']]:=ih _ _ _ eq.
    exists σ'. split... }
Qed.

Lemma kam_step m m' n e e' s s' :
  kam (m, e, s) (m', e', s') -> resolve m e s n -> exists n', resolve m' e' s' n' /\ sred n n'.
Proof with eauto using resolve, step.
  move e1:(m, e, s)=>x.
  move e2:(m', e', s')=>y km.
  elim: km m m' n e e' s s' e1 e2=>{x y}.
  { move=>m e c s m0 m' n e0 e' s0 s'[e1 e2 e3][e4 e5 e6]rs; subst. inv rs.
    asimpl in H0. inv H0.
    apply: resolve_stack_ok... }
  { move=>m n e s m0 m' n0 e0 e' s0 s'[e1 e2 e3][e4 e5 e6]rs; subst. inv rs.
    asimpl in H0.
    exists n0. split...
    econstructor...
    econstructor... }
  { move=>x e e' m s eq m0 m' n e0 e'0 s0 s'[e1 e2 e3][e4 e5 e6]rs; subst. inv rs.
    asimpl in H0.
    have[σ'[rs' eq']]:=resolve_env_ok H eq.
    rewrite eq' in H0.
    exists n. split... }
Qed.
