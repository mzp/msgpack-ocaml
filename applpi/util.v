Require Import Omega.
Require Import JMeq.

Lemma compare_nats : forall x y : nat, x < y \/ y < x \/ x = y.
  intros; omega.
Qed.

(* axiom of choice *)

Lemma Choice_Type :
 forall (S' : Type) (R : nat -> S' -> Type),
 (forall x : nat, sigT (fun y : S' => R x y)) ->
 sigT (fun f : nat -> S' => forall z : nat, R z (f z)).
intros.
exists (fun x : nat => match X x with
                       | existT y _ => y
                       end).
intro.
generalize (X z); intro.
elim s.
auto.
Qed.

Lemma Choice_Prop :
 forall (S' : Type) (R : nat -> S' -> Prop),
 (forall x : nat, sigT (fun y : S' => R x y)) ->
 sigT (fun f : nat -> S' => forall z : nat, R z (f z)).
intros.
exists (fun x : nat => match X x with
                       | existT y _ => y
                       end).
intro.
generalize (X z); intro.
elim s.
auto.
Qed.

(*Fixpoint dchoice_type_funct [R:state->state->Type;seed:state;X0:(x:(state))(sigT state [y:(state)](R x y));x:nat] : state := Cases x of 
	 O => seed
	| (S n) => 
	   (Cases (X0 (dchoice_type_funct R seed X0 n)) of (existT y _) => y end)
	  end.

Lemma DChoice_Type : (R:(state->state->Type))
        (P,Q:state)(R P Q) ->   
        ((x:state)(sigT ? [y:state](R x y)))->
	(sigT ? [f:(nat->state)]((z:nat)(R (f z) (f (S z))))).
Intros.
Exists (dchoice_type_funct R P X0).
Intro.
Simpl.
Generalize (X0 (dchoice_type_funct R P X0 z)).
Intros.
Elim s.
Auto.
Qed.*)

Fixpoint dchoice_prop_funct (S' : Type) (R : S' -> S' -> Type) 
 (seed : S') (X0 : forall x : S', sigT (fun y : S' => R x y)) 
 (x : nat) {struct x} : S' :=
  match x with
  | O => seed
  | S n =>
      match X0 (dchoice_prop_funct S' R seed X0 n) with
      | existT y _ => y
      end
  end.

Lemma DChoice_Prop :
 forall (S' : Type) (R : S' -> S' -> Prop) (P Q : S'),
 R P Q ->
 (forall x : S', sigT (fun y : S' => R x y)) ->
 sigT (fun f : nat -> S' => forall z : nat, R (f z) (f (S z))).
intros.
exists (dchoice_prop_funct S' R P X).
intro.
simpl in |- *.
generalize (X (dchoice_prop_funct S' R P X z)).
intros.
elim s.
auto.
Qed.

Axiom Choice_Prop2 :
    forall (S' : Type) (R : nat -> S' -> S' -> Prop) (P Q : S'),
    R 0 P Q ->
    (forall (x : nat) (Q' : S'),
     sigT (fun P' : S' => R x P' Q') -> sigT (fun y : S' => R (S x) Q' y)) ->
    sigT (fun f : nat -> S' => forall z : nat, R z (f z) (f (S z))).

Axiom EXT_sigT :
  forall (U : Type) (P : U -> Prop),
    (exists u : U, P u) -> sigT (fun u : U => P u).


Notation "c %% d" := (JMeq c d) (at level 85).

Axiom jmeq_types : forall (A B : Set) (x : A) (y : B), x %% y -> A = B.
Implicit Arguments jmeq_types [A B x y].

Axiom extension :
  forall (A : Set) (U : Type) (f g : A -> U),
    (forall a : A, f a = g a) -> f = g.

Ltac or_false :=
  match goal with
  | id:(?X1 \/ ?X2) |- _ =>
      elim id; clear id; [ idtac | intro; or_false ]
  | id:False |- _ => contradiction
  | _ => idtac
  end.

Ltac EvalRewrite t :=
  let v := eval compute in t in
  (replace t with v; [ idtac | simpl in |- *; auto ]).

Inductive optionT (A : Type) : Type :=
  | SomeT : A -> optionT A
  | NoneT : optionT A.

