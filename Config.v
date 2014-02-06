Require Import Coq.Logic.FunctionalExtensionality Coq.Arith.EqNat Coq.MSets.MSets Names Sets Fun.

Inductive config : Set :=
  | nil : config
  | create : name -> name -> config -> config
  | send : name -> name -> config
  | restrict : name -> config -> config
  | compose : config -> config -> config
  | caseof : name -> list (name * config) -> config.

Inductive ConfigName (x : name) : config -> Prop :=
  | send_name_1 : forall y, ConfigName x (send x y)
  | send_name_2 : forall y, ConfigName x (send y x)
  | create_name_1 : forall y p, ConfigName x (create x y p)
  | create_name_2 : forall y p, ConfigName x (create y x p)
  | create_name_p : forall y z p, ConfigName x p -> ConfigName x (create y z p)
  | compose_name_l : forall pl pr, ConfigName x pl -> ConfigName x (compose pl pr)
  | compose_name_r : forall pl pr, ConfigName x pr -> ConfigName x (compose pl pr)
  | restrict_name : forall p, ConfigName x (restrict x p)
  | restrict_name_p : forall y p, ConfigName x p -> ConfigName x (restrict y p)
  | caseof_name : forall l, ConfigName x (caseof x l)
  | caseof_name_h_fst : forall y c l, ConfigName x (caseof y ((x, c) :: l))
  | caseof_name_h_snd : forall y n c l, ConfigName x c -> ConfigName x (caseof y ((n, c) :: l))
  | caseof_name_t : forall y nc l, ConfigName x (caseof y l) -> ConfigName x (caseof y (nc :: l)).

Hint Constructors ConfigName.

Inductive ConfigBoundedName (x : name) : config -> Prop :=
  | create_bounded : forall y p, x <> y -> ConfigBoundedName x (create y x p)
  | create_bounded_p : forall y z p, ConfigBoundedName x p -> x <> y ->
                                     ConfigBoundedName x (create y z p)
  | compose_bounded_b : forall pl pr, ConfigBoundedName x pl ->
                                      ConfigBoundedName x pr ->
                                      ConfigBoundedName x (compose pl pr)
  | compose_bounded_l : forall pl pr, ConfigBoundedName x pl ->
                                      ~ ConfigName x pr ->
                                      ConfigBoundedName x (compose pl pr)
  | compose_bounded_r : forall pl pr, ConfigBoundedName x pr ->
                                      ~ ConfigName x pl ->
                                      ConfigBoundedName x (compose pl pr)
  | restrict_bounded : forall p, ConfigBoundedName x (restrict x p)
  | restrict_bounded_p : forall y p, ConfigBoundedName x p ->
                                     ConfigBoundedName x (restrict y p)
  | caseof_bounded_s : forall y n c l, ConfigBoundedName x c ->
                                       ~ ConfigName x (caseof y l) ->
                                       x <> n ->
                                       ConfigBoundedName x (caseof y ((n, c) :: l))
  | caseof_bounded_h : forall y n c l, ConfigBoundedName x c ->
                                       ConfigBoundedName x (caseof y l) ->
                                       x <> n ->
                                       ConfigBoundedName x (caseof y ((n, c) :: l))
  | caseof_bounded_t : forall y n c l, ConfigBoundedName x (caseof y l) ->
                                       ~ ConfigName x c ->
                                       x <> n ->
                                       ConfigBoundedName x (caseof y ((n, c) :: l)).

  (* | caseof_bounded_s : forall y n c, ConfigBoundedName x c -> *)
  (*                                    x <> y -> *)
  (*                                    x <> n -> *)
  (*                                    ConfigBoundedName x (caseof y ((n, c) :: List.nil)) *)
  (* | caseof_bounded_h : forall y n c l, ConfigBoundedName x c -> *)
  (*                                      ~ ConfigBoundedName x (caseof y l) -> *)
  (* | caseof_bounded_t : forall y n c l, ConfigBoundedName x (caseof y l) -> *)
  (*                                      x <> n -> *)
  (*                                      ConfigBoundedName x (caseof y ((n, c) :: l)) *)
  (* | caseof_bounded : forall y l, Forall (fun nc => ConfigBoundedName x (snd nc)) l -> *)
  (*                                ConfigBoundedName x (caseof y l). *)

Hint Constructors ConfigBoundedName.

Inductive ConfigFreeName (x : name) : config -> Prop :=
  | send_free_1 : forall y, ConfigFreeName x (send x y)
  | send_free_2 : forall y, ConfigFreeName x (send y x)
  | create_free : forall y p, ConfigFreeName x (create x y p)
  | create_free_p : forall y z p, ConfigFreeName x p -> x <> z -> ConfigFreeName x (create y z p)
  | compose_free_l : forall pl pr, ConfigFreeName x pl -> ConfigFreeName x (compose pl pr)
  | compose_free_r : forall pl pr, ConfigFreeName x pr -> ConfigFreeName x (compose pl pr)
  | restrict_free : forall r p, ConfigFreeName x p -> x <> r -> ConfigFreeName x (restrict r p)
  | caseof_free : forall l, ConfigFreeName x (caseof x l)
  | caseof_free_h_fst : forall y c l, ConfigFreeName x (caseof y ((x, c) :: l))
  | caseof_free_h_snd : forall y n c l, ConfigFreeName x c -> ConfigFreeName x (caseof y ((n, c) :: l))
  | caseof_free_t : forall y nc l, ConfigFreeName x (caseof y l) -> ConfigFreeName x (caseof y (nc :: l)).

Hint Constructors ConfigFreeName.

(* Lemma config_name_dec : forall x p, {ConfigName x p} + {~ ConfigName x p}. *)
(* Proof. *)
(*   intros. *)
(*   induction p. *)
(*     right; intro. *)
(*     inversion H. *)

(*     inversion IHp. *)
(*       left; auto. *)

(*       destruct (name_dec x n). *)
(*         rewrite e; left; auto. *)

(*         destruct (name_dec x n0). *)
(*           rewrite e; left; auto. *)

(*           right; intro. *)
(*           inversion H0; auto. *)

(*     destruct (name_dec x n). *)
(*       rewrite e; left; auto. *)

(*       destruct (name_dec x n0). *)
(*         rewrite e; left; auto. *)

(*         right; intro. *)
(*         inversion H; auto. *)

(*     destruct (name_dec x n). *)
(*       rewrite e; left; auto. *)

(*       inversion IHp. *)
(*         left; auto. *)

(*         right; intro. *)
(*         inversion H0; auto. *)

(*     inversion IHp1; inversion IHp2. *)
(*       left; auto. *)

(*       left; auto. *)

(*       left; auto. *)

(*       right; intro. *)
(*       inversion H1; auto. *)

(*     destruct (name_dec x n). *)
(*       rewrite e; left; auto. *)

(*       induction l. *)
(*         right; intro. *)
(*         inversion H. *)
(*           apply n0; auto. *)

(*         inversion IHl. *)
(*           left. *)
(*           inversion H; subst. *)
(*             auto. *)

(*             apply caseof_name_t; auto. *)

(*             apply caseof_name_t; auto. *)

(*             apply caseof_name_t; auto. *)

(*           destruct a. *)
(*           destruct (name_dec x n1). *)
(*             left; rewrite e; auto. *)

(*             destruct (config_name_dec x c). *)
(* Qed. *)

(* Lemma config_free_dec : forall x p, {ConfigFreeName x p} + {~ ConfigFreeName x p}. *)
(* Proof. *)
(*   intros. *)
(*   induction p. *)
(*     right; intro; inversion H. *)

(*     destruct (name_dec x n). *)
(*       rewrite e; left; auto. *)
(*       destruct (name_dec x n0). *)
(*         rewrite e; right; intro; inversion H; subst; auto. *)
(*         inversion IHp. *)
(*           left; auto. *)
(*           right; intro; inversion H0; subst; auto. *)

(*     destruct (name_dec x n); destruct (name_dec x n0). *)
(*       rewrite e; auto. *)
(*       rewrite e; auto. *)
(*       rewrite e; auto. *)
(*       right; intro; inversion H; subst; auto. *)

(*     destruct (name_dec x n). *)
(*       rewrite e; right; intro; inversion H; subst; auto. *)
(*       inversion IHp. *)
(*         left; auto. *)
(*         right; intro; inversion H0; subst; auto. *)

(*     inversion_clear IHp1; inversion_clear IHp2. *)
(*       left; auto. *)
(*       left; auto. *)
(*       left; auto. *)
(*       right; intro; inversion H1; subst; auto. *)
(* Qed. *)

(* Lemma config_bounded_prop : forall x p, ConfigBoundedName x p -> ConfigName x p. *)
(* Proof. *)
(*   intros. *)
(*   induction p; inversion H; subst; auto. *)
(* Qed. *)

(* Lemma config_free_prop : forall x p, ConfigFreeName x p -> ConfigName x p. *)
(* Proof. *)
(*   intros. *)
(*   induction p; inversion H; subst; auto. *)
(* Qed. *)

(* Lemma config_name_prop : forall x p, ConfigName x p -> *)
(*                                      (ConfigBoundedName x p <-> ~ ConfigFreeName x p) /\ *)
(*                                      (ConfigFreeName x p <-> ~ ConfigBoundedName x p). *)
(* Proof. *)
(*   intros. *)
(*   induction p. *)
(*     inversion H. *)

(*     inversion H; subst. *)
(*       split; split; intros; try intro. *)
(*         inversion H0; subst; auto. *)

(*         absurd (ConfigFreeName n (create n n0 p)); auto. *)

(*         inversion H1; subst; auto. *)

(*         auto. *)

(*       split; split; intros; try intro. *)
(*         inversion H0; subst; inversion H1; subst; auto. *)

(*         apply create_bounded. *)
(*         intro; subst; apply H0; auto. *)

(*         inversion H0; subst; inversion H1; subst; auto. *)

(*         assert (n <> n0 -> False). *)
(*           intro. *)
(*           apply H0. *)
(*           auto. *)
(*         apply eq_name_double_neg in H1. *)
(*         rewrite H1; auto. *)

(*       apply IHp in H1. *)
(*       inversion_clear H1. *)
(*       split; split; intros; try intro. *)
(*         inversion H1; subst; inversion H3; subst; auto. *)
(*         apply H0 in H6; auto. *)

(*         assert (x <> n). *)
(*           intro; apply H1. *)
(*           rewrite H3; auto. *)
(*         destruct (beq_name x n0) eqn:?. *)
(*           apply beq_name_true_iff in Heqb. *)
(*           rewrite <- Heqb. *)
(*           apply create_bounded; auto. *)

(*           apply beq_name_false_iff in Heqb. *)
(*           apply create_bounded_p. *)
(*             apply H0. *)
(*             intro. *)
(*             apply H1. *)
(*             apply create_free_p; auto. *)

(*             auto. *)

(*         inversion H1; subst; inversion H3; subst; auto. *)
(*         apply H0 in H6; auto. *)

(*         destruct (beq_name x n) eqn:?. *)
(*           apply beq_name_true_iff in Heqb. *)
(*           rewrite Heqb; auto. *)

(*           apply beq_name_false_iff in Heqb. *)
(*           assert (x <> n0). *)
(*             intro. *)
(*             rewrite <- H3 in H1. *)
(*             apply H1. *)
(*             auto. *)
(*           apply create_free_p; auto. *)
(*           apply H2. *)
(*           intro. *)
(*           apply H1. *)
(*           auto. *)

(*     inversion_clear H; subst. *)
(*       split; split; intros; try intro. *)
(*         inversion H. *)

(*         exfalso; apply H; auto. *)

(*         inversion H0. *)

(*         auto. *)
(*       split; split; intros; try intro. *)
(*         inversion H. *)

(*         exfalso; apply H; auto. *)

(*         inversion H0. *)

(*         auto. *)

(*     inversion_clear H; subst. *)
(*       split; split; intros; try intro. *)
(*         inversion H0; auto. *)

(*         auto. *)

(*         inversion H; auto. *)

(*         exfalso; apply H; auto. *)
(*       apply IHp in H0. *)
(*       clear IHp. *)
(*       inversion_clear H0. *)
(*       split; split; intros; try intro. *)
(*         inversion H0; subst; inversion H2; subst; auto. *)
(*         apply H in H4; auto. *)

(*         destruct (beq_name x n) eqn:?. *)
(*           apply beq_name_true_iff in Heqb. *)
(*           rewrite Heqb; auto. *)

(*           apply beq_name_false_iff in Heqb. *)
(*           apply restrict_bounded_p. *)
(*           apply H; intro. *)
(*           apply H0; apply restrict_free; auto. *)

(*         inversion H0; subst; inversion H2; subst; auto. *)
(*         apply H in H4; auto. *)

(*         destruct (beq_name x n) eqn:?. *)
(*           apply beq_name_true_iff in Heqb. *)
(*           rewrite Heqb in H0. *)
(*           exfalso; apply H0; auto. *)

(*           apply beq_name_false_iff in Heqb. *)
(*           apply restrict_free; auto. *)
(*           apply H1. *)
(*           intro. *)
(*           apply H0; auto. *)

(*     inversion_clear H; subst. *)
(*       assert (ConfigName x p1); auto. *)
(*       apply IHp1 in H0. *)
(*       inversion_clear H0. *)
(*       split; split; intros; try intro. *)
(*         inversion_clear H0; subst; inversion_clear H3; subst; auto. *)
(*           apply H1 in H4; auto. *)

(*           assert (ConfigBoundedName x p2); auto. *)
(*           apply config_bounded_prop in H3. *)
(*           apply IHp2 in H3. *)
(*           inversion_clear H3. *)
(*           apply H6 in H5; auto. *)

(*           apply H1 in H0; auto. *)

(*           apply config_free_prop in H0; auto. *)

(*         assert (~ ConfigFreeName x p1 /\ ~ ConfigFreeName x p2). *)
(*           split. *)
(*             intro; apply H0; auto. *)
(*             intro; apply H0; auto. *)
(*         inversion_clear H3. *)
(*         apply H1 in H4. *)
(*         destruct (config_name_dec x p2). *)
(*           apply IHp2 in c. *)
(*           inversion_clear c. *)
(*           apply H3 in H5. *)
(*           auto. *)

(*           auto. *)

(*         inversion H0; subst; inversion H3; subst; auto. *)
(*           apply H1 in H7; auto. *)

(*           apply H1 in H7; auto. *)

(*           assert (ConfigBoundedName x p2); auto. *)
(*           apply config_bounded_prop in H4; apply IHp2 in H4. *)
(*           inversion_clear H4. *)
(*           apply H6 in H8; auto. *)

(*           apply config_free_prop in H5; auto. *)

(*         destruct (config_name_dec x p2). *)
(*           apply IHp2 in c. *)
(*           inversion_clear c. *)
(*           destruct (config_free_dec x p1); auto. *)
(*           destruct (config_free_dec x p2); auto. *)
(*           apply H1 in n. *)
(*           apply H3 in n0. *)
(*           exfalso; apply H0; auto. *)

(*           apply compose_free_l. *)
(*           apply H2. *)
(*           intro. *)
(*           apply H0. *)
(*           auto. *)

(*       assert (ConfigName x p2); auto. *)
(*       apply IHp2 in H0. *)
(*       inversion_clear H0. *)
(*       clear IHp2. *)
(*       split; split; intros; try intro. *)
(*         inversion H0; subst; inversion H3; subst; auto. *)
(*           assert (ConfigBoundedName x p1); auto. *)
(*           apply config_bounded_prop in H4. *)
(*           apply IHp1 in H4. *)
(*           inversion_clear H4. *)
(*           apply H8 in H6; auto. *)

(*           apply H1 in H7; auto. *)

(*           apply config_free_prop in H5; auto. *)

(*           apply H1 in H5; auto. *)

(*         assert (~ ConfigFreeName x p1 /\ ~ ConfigFreeName x p2). *)
(*           split. *)
(*             intro; apply H0; auto. *)
(*             intro; apply H0; auto. *)
(*         inversion_clear H3. *)
(*         apply H1 in H5. *)
(*         destruct (config_name_dec x p1). *)
(*           apply IHp1 in c; inversion_clear c. *)
(*           apply H3 in H4. *)
(*           auto. *)

(*           auto. *)

(*         inversion H0; subst; inversion H3; subst; auto. *)
(*           assert (ConfigBoundedName x p1); auto. *)
(*           apply config_bounded_prop in H4; apply IHp1 in H4; inversion_clear H4. *)
(*           apply H6 in H7; auto. *)

(*           apply config_free_prop in H5; auto. *)

(*           apply H1 in H8; auto. *)

(*           apply H1 in H7; auto. *)

(*         destruct (config_free_dec x p1); auto. *)
(*         destruct (config_free_dec x p2); auto. *)
(*         destruct (config_name_dec x p1). *)
(*           apply IHp1 in c; inversion_clear c. *)
(*           apply H3 in n. *)
(*           apply H1 in n0. *)
(*           exfalso; apply H0; auto. *)

(*           apply compose_free_r. *)
(*           apply H2. *)
(*           intro. *)
(*           apply H0. *)
(*           auto. *)
(* Qed. *)
