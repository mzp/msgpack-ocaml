 Inductive listT (A : Type) : Type :=
  | nilT : listT A
  | consT : A -> listT A -> listT A.

Fixpoint in_listT (A : Type) (P : A) (l : listT A) {struct l} : Prop :=
  match l with
  | nilT => False
  | consT hd tl => P = hd \/ in_listT A P tl
  end.