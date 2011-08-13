Require Import JMeq.
Require Import util.
Require Import chan.
Require Import applpi.

(** injection lemmas for labels *)

Set Implicit Arguments.

Lemma OutL_inj1 :
  forall A b (c : chan A b) v A' b' (c' : chan A' b') v',
    OutL c v = OutL c' v' -> A = A' /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma OutL_inj0 :
  forall A c' (c : chan A c') v A' d' (d : chan A' d') w,
    OutL c v = OutL d w -> (c %% d) /\ (v %% w).
intros.
split.
change match OutL d w with
       | OutL AA cc' cc v' => c %% cc
       | _ => c %% d
       end in |- *.
rewrite <- H.
auto.
change match OutL d w with
       | OutL AA cc' cc v' => v %% v'
       | _ => c %% d
       end in |- *.
rewrite <- H.
auto.
Qed.

Lemma OutL_inj :
  forall A b (c : chan A b) v (d : chan A b) w,
    OutL c v = OutL d w -> c = d /\ v = w.
intros.
generalize (OutL_inj0 H); intro.
decompose [and] H0; clear H0.
split.
apply (JMeq_eq H1).
apply (JMeq_eq H2).
Qed.

Lemma InL_inj1 :
  forall A b (c : chan A b) v A' b' (c' : chan A' b') v',
    InL c v = InL c' v' -> A = A' /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma InL_inj0 :
  forall A c' (c : chan A c') v A' d' (d : chan A' d') w,
    InL c v = InL d w -> (c %% d) /\ (v %% w).
intros.
split.
change match InL d w with
       | InL AA cc' cc v' => c %% cc
       | _ => c %% d
       end in |- *.
rewrite <- H.
auto.
change match InL d w with
       | InL AA cc' cc v' => v %% v'
       | _ => c %% d
       end in |- *.
rewrite <- H.
auto.
Qed.

Lemma InL_inj :
  forall A b (c : chan A b) v (d : chan A b) w,
    InL c v = InL d w -> c = d /\ v = w.
intros.
generalize (InL_inj0 H); intro.
decompose [and] H0; clear H0.
split.
apply (JMeq_eq H1).
apply (JMeq_eq H2).
Qed.

Lemma TauL_inj1 :
  forall A b (c : chan A b) A' b' (d : chan A' b'), 
    TauL c = TauL d -> A = A' /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma TauL_inj0 :
  forall A b (c : chan A b) A' b' (d : chan A' b'), 
    TauL c = TauL d -> c %% d.
intros.
change match TauL d with
       | TauL AA cc' cc => c %% cc
       | _ => c %% d
       end in |- *.
rewrite <- H.
auto.
Qed.

Lemma TauL_inj :
  forall A b (c d : chan A b), 
    TauL c = TauL d -> c = d.
intros.
generalize (TauL_inj0 H); intro.
apply (JMeq_eq H0).
Qed.

Lemma NewL_inj1 :
  forall A b (c : chan A b) A' b' (d : chan A' b'), 
    NewL c = NewL d -> A = A' /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma NewL_inj0 :
  forall A b (c : chan A b) A' b' (d : chan A' b'), 
    NewL c = NewL d -> c %% d.
intros.
change match NewL d with
       | NewL AA cc' cc => c %% cc
       | _ => c %% d
       end in |- *.
rewrite <- H.
auto.
Qed.

Lemma NewL_inj :
  forall A b (c d : chan A b), 
    NewL c = NewL d -> c = d.
intros.
generalize (NewL_inj0 H); intro.
apply (JMeq_eq H0).
Qed.

(** injection lemmas for processes *)

Lemma outP_inj1 :
    forall A b (c : chan A b) v C A' b' (c' : chan A' b') v' C', 
      c << v >> C = c' << v' >> C' -> A = A' /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma outP_inj0 :
  forall A b (c : chan A b) v C A' b' (c' : chan A' b') v' C',
    c << v >> C = c' << v' >> C' -> (c %% c') /\ (v %% v').
intros.
split.
change
  match c << v >> C with
  | outP A'' b'' c'' v'' C'' => c'' %% c'
  | _ => c %% c'
  end in |- *.
rewrite H.
auto.
change
  match c << v >> C with
  | outP A'' b'' c'' v'' C'' => v'' %% v'
  | _ => v %% v'
  end in |- *.
rewrite H.
auto.
Qed.

Lemma outP_inj_chan_val :
  forall A b (c : chan A b) v C (c' : chan A b) v' C',
    c << v >> C = c' << v' >> C' -> c = c' /\ v = v'.
intros.
generalize (outP_inj0 H); intro.
decompose [and] H0; clear H0.
split.
apply (JMeq_eq H1).
apply (JMeq_eq H2).
Qed.

Lemma outP_inj_cont :
  forall A b (c : chan A b) v C B b' (c' : chan B b') v' C', 
    c << v >> C = c' << v' >> C' -> C = C'.
intros.
generalize (outP_inj1  H); intro.
inversion_clear H0.
generalize c' v' H; clear c' v' H; rewrite <- H1; rewrite <- H2;
 clear H1 H2 B b'; intros.
generalize (outP_inj_chan_val H); intro.
inversion_clear H0.
rewrite <- H1 in H.
rewrite <- H2 in H.
injection H.
auto.
Qed.

Lemma inP_inj1 :
  forall A b (c : chan A b) C A' b' (c' : chan A' b') C',
    c ?? C = c' ?? C' -> A = A' /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma inP_inj0 :
  forall A b (c : chan A b) C A' b' (c' : chan A' b') C',
    c ?? C = c' ?? C' -> c %% c'.
intros.
change
  match c ?? C with
  | inP A'' b'' c'' C'' => c'' %% c'
  | _ => c %% c'
  end in |- *.
rewrite H.
auto.
Qed.

Lemma inP_inj_chan :
  forall A b (c : chan A b) C (c' : chan A b) C', 
    c ?? C = c' ?? C' -> c = c'.
intros.
generalize (inP_inj0 H); intro.
apply (JMeq_eq H0).
Qed.

Axiom inP_inj_cont :
  forall A b (c : chan A b) C C',
    c ?? C = c ?? C' -> C = C'.

Lemma rinP_inj1 :
  forall A b (c : chan A b) C A' b' (c' : chan A' b') C',
    c ??* C = c' ??* C' -> A = A' /\ b = b'.
intros.
injection H.
auto.
Qed.

Lemma rinP_inj0 :
  forall A b (c : chan A b) C A' b' (c' : chan A' b') C',
    c ??* C = c' ??* C' -> c %% c'.
intros.
change
  match c ??* C with
  | rinP A'' b'' c'' C'' => c'' %% c'
  | _ => c %% c'
  end in |- *.
rewrite H.
auto.
Qed.

Lemma rinP_inj_chan :
  forall A b (c : chan A b) C (c' : chan A b) C', 
    c ??* C = c' ??* C' -> c = c'.
intros.
generalize (rinP_inj0 H); intro.
apply (JMeq_eq H0).
Qed.

Axiom rinP_inj_cont :
  forall A b (c : chan A b) C C',
    c ??* C = c ??* C' -> C = C'.

Lemma nuP_inj1 :
  forall A (C : chan A false -> proc) A' (C' : chan A' false -> proc), 
    nuP C = nuP C' -> A = A'.
intros.
injection H.
auto.
Qed.

Axiom nuP_inj_cont :
  forall A (C C' : chan A false -> proc), 
    nuP C = nuP C' -> C = C'.

Lemma nuPl_inj1 :
  forall A (C : chan A true -> proc) A' (C' : chan A' true -> proc), 
    nuPl C = nuPl C' -> A = A'.
intros.
injection H.
auto.
Qed.

Axiom nuPl_inj_cont :
  forall A (C C' : chan A true -> proc), 
    nuPl C = nuPl C' -> C = C'.

Lemma parP_inj :
  forall P Q P' Q' : proc, 
    parP P Q = parP P' Q' -> P = P' /\ Q = Q'.
intros.
injection H.
auto.
Qed.

Unset Implicit Arguments.


