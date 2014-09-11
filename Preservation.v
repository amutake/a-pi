Require Import Names Sets Fun Config Trans Typing.

Module S := NameSets.
Module F := Fun.Fun.

Lemma nequal_f {A B : Type} : forall (f g : A -> B), (exists x, f x <> g x) -> f <> g.
Proof.
  unfold not.
  intros.
  inversion H.
  apply H1.
  rewrite H0; auto.
Qed.

Theorem Preservation : forall r f p p' a,
  r ; f |- p ->
  not_silent a ->
  p == a ==> p' ->
  exists r' f', r' ; f' |- p'.
Proof.
  intros.
  induction H1.
  - inversion H; subst.
    + inversion H4; subst.
      * exists S.empty.
        exists F.empty.
        auto.
      * simpl.
        exists S.empty.
        exists F.empty.
        auto.
      * exfalso.
        eapply F.ch_2_not_empty.
        apply H2.
      * exfalso.
        eapply F.ch_2_not_empty.
        apply H2.
      * apply F.fun_plus_empty_split in H2.
        inversion_clear H2; subst.
Admitted.
