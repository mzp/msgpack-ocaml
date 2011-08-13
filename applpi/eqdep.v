 Section EQDEP.

Variable U : Type.
Variable V : Set.
Variable P : U -> V -> Set.

Inductive eqdep (p : U) (b : V) (x : P p b) :
forall (q : U) (c : V), P q c -> Prop :=
    eqdep_intro : eqdep p b x p b x.

(** symmetry and transitivity properties *)
Lemma eqdep_sym :
 forall (p q : U) (b c : V) (x : P p b) (y : P q c),
 eqdep p b x q c y -> eqdep q c y p b x.
intros.
induction H.
apply eqdep_intro.
Qed.

Lemma eqdep_trans :
 forall (p q r : U) (p' q' r' : V) (x : P p p') (y : P q q') (z : P r r'),
 eqdep _ _ x _ _ y -> eqdep _ _ y _ _ z -> eqdep _ _ x _ _ z.
intros.
induction H.
auto.
Qed.


End EQDEP.

Hint Immediate eqdep_intro: core. 

Hint Immediate eqdep_sym: core. 


