Require Import Coq.Lists.List Coq.Logic.FunctionalExtensionality Names.

Inductive temp_name_mapping_fun : Type :=
| ch_0 : temp_name_mapping_fun
| ch_1 : name -> temp_name_mapping_fun
| ch_2 : forall x y : name, x <> y -> temp_name_mapping_fun
| fun_plus : temp_name_mapping_fun -> temp_name_mapping_fun -> temp_name_mapping_fun
| fun_remove : name -> temp_name_mapping_fun -> temp_name_mapping_fun.

Hint Constructors temp_name_mapping_fun.

Inductive in_domain (x : name) : temp_name_mapping_fun -> Prop :=
| in_domain_ch_1 : in_domain x (ch_1 x)
| in_domain_ch_2 : forall y p, in_domain x (ch_2 x y p)
| in_domain_ch_2' : forall y p, in_domain x (ch_2 y x p)
| in_domain_fun_plus_l : forall f g, in_domain x f -> in_domain x (fun_plus f g)
| in_domain_fun_plus_r : forall f g, in_domain x g -> in_domain x (fun_plus f g)
| in_domain_fun_remove : forall f y, in_domain x f -> x <> y -> in_domain x (fun_remove y f).

Hint Constructors in_domain.

Inductive is_hidden (x : name) : temp_name_mapping_fun -> Prop :=
| hidden_here : forall f, is_hidden x (fun_remove x f)
| hidden_there : forall f g, is_hidden x f -> is_hidden x (fun_plus f g).

Hint Constructors is_hidden.

Inductive in_range (x : name) : temp_name_mapping_fun -> Prop :=
| in_range_ch_2 : forall y p, in_range x (ch_2 y x p)
| in_range_fun_plus_l : forall f g, in_range x f -> in_range x (fun_plus f g)
| in_range_fun_plus_r : forall f g, in_range x g -> in_range x (fun_plus f g)
| in_range_fun_remove : forall f y, in_range x f -> x <> y -> in_range x (fun_remove y f).

Hint Constructors in_range.

Theorem in_range_in_domain : forall f x, in_range x f -> in_domain x f.
Proof.
  intros.
  induction f.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    auto.
  - inversion H.
    + apply IHf1 in H1.
      auto.
    + apply IHf2 in H1.
      auto.
  - inversion H.
    apply IHf in H2.
    auto.
Qed.

Definition exclusive f1 f2 := forall x,
  (in_domain f1 x -> ~ in_domain f2 x) /\ (in_domain f2 x -> ~ in_domain f1 x).

Inductive temp_name_mapping : temp_name_mapping_fun -> name -> star -> Prop :=
| map_ch_1 : forall n, temp_name_mapping (ch_1 n) n star_bottom
| map_ch_2_n : forall n m (neq : n <> m), temp_name_mapping (ch_2 n m neq) n (star_name m)
| map_ch_2_m : forall n m (neq : n <> m), temp_name_mapping (ch_2 n m neq) m star_bottom
| map_fun_plus_l : forall f1 f2 n s, temp_name_mapping f1 n s ->
                                     s <> star_bottom ->
                                     temp_name_mapping (fun_plus f1 f2) n s
| map_fun_plus_l' : forall f1 f2 n, temp_name_mapping f1 n star_bottom ->
                                    ~ in_domain n f2 ->
                                    temp_name_mapping (fun_plus f1 f2) n star_bottom
| map_fun_plus_r : forall f1 f2 n s, ~ in_domain n f1 ->
                                     temp_name_mapping f2 n s ->
                                     temp_name_mapping (fun_plus f1 f2) n s
| map_fun_plus_r' : forall f1 f2 n s, temp_name_mapping f1 n star_bottom ->
                                      temp_name_mapping f2 n s ->
                                      temp_name_mapping (fun_plus f1 f2) n s
| map_fun_remove : forall f n m s, temp_name_mapping f n s ->
                                   n <> m ->
                                   s <> star_name m ->
                                   temp_name_mapping (fun_remove m f) n s
| map_fun_remove' : forall f n m, temp_name_mapping f n (star_name m) ->
                                  temp_name_mapping (fun_remove m f) n star_star.

Hint Constructors temp_name_mapping.

Inductive temp_name_mapping' (f : temp_name_mapping_fun) : star -> star -> Prop :=
| map_name : forall n s, temp_name_mapping f n s ->
                         temp_name_mapping' f (star_name n) s
| map_bottom : temp_name_mapping' f star_bottom star_bottom
| map_star : temp_name_mapping' f star_star star_bottom.

Hint Constructors temp_name_mapping'.

Definition Fun_comm (f1 f2 : temp_name_mapping_fun) :=
  forall x s, temp_name_mapping (fun_plus f1 f2) x s <->
              temp_name_mapping (fun_plus f2 f1) x s.

Definition Fun_prop_1 (f : temp_name_mapping_fun) :=
  forall x, ~ temp_name_mapping f x (star_name x).

Definition Fun_prop_2 (f : temp_name_mapping_fun) :=
  forall x y n, temp_name_mapping f x (star_name n) ->
                temp_name_mapping f y (star_name n) ->
                x = y.

Definition Fun_prop_3 (f : temp_name_mapping_fun) :=
  forall x s s', temp_name_mapping f x s ->
                 temp_name_mapping' f s s' ->
                 s = star_bottom.

Definition Fun_prop (f : temp_name_mapping_fun) :=
  Fun_prop_1 f /\ Fun_prop_2 f /\ Fun_prop_3 f.

Record Compatible (f1 f2 : temp_name_mapping_fun) := Build_compatible {
  Compatible_comm : Fun_comm f1 f2;
  Compatible_prop : Fun_prop (fun_plus f1 f2)
}.

Fixpoint Mutually_compatible (fs : list temp_name_mapping_fun) :=
  match fs with
    | nil => True
    | f :: fs' => Forall (Compatible f) fs' /\ Mutually_compatible fs'
  end.

Theorem fun_prop_1 : forall f, Fun_prop_1 f.
Proof.
  repeat red.
  intros.
  induction f; inversion H; subst; auto.
Qed.

Hint Resolve fun_prop_1.

Lemma fun_prop_1' : forall f x n, temp_name_mapping f x (star_name n) -> x <> n.
Proof.
  intros.
  destruct (name_dec x n).
  - subst.
    apply fun_prop_1 in H.
    auto.
  - auto.
Qed.

Hint Resolve fun_prop_1'.

Lemma mapping_in_domain : forall f x s, temp_name_mapping f x s ->
                                        in_domain x f.
Proof.
  induction f; intros.
  - inversion H.
  - inversion H; auto.
  - inversion H; subst; auto.
  - inversion H; subst.
    + specialize IHf1 with x s; auto.
    + specialize IHf1 with x star_bottom; auto.
    + specialize IHf2 with x s; auto.
    + specialize IHf2 with x s; auto.
  - inversion H; subst.
    + specialize IHf with x s; auto.
    + apply in_domain_fun_remove.
      * apply IHf with (star_name n); auto.
      * apply fun_prop_1' in H4; auto.
Qed.

Hint Resolve mapping_in_domain.

Lemma compatible_split : forall f1 f2,
                           Compatible f1 f2 ->
                           Fun_prop f1 /\ Fun_prop f2.
Proof.
  intros.
  destruct H.
  inversion_clear Compatible_prop0.
  inversion_clear H0.
  repeat (red in H).
  repeat (red in H1).
  repeat (red in H2).
  repeat split.
  - repeat red.
    intros.
    apply H with x.
    apply map_fun_plus_l; auto.
    easy.
  - repeat red; intros.
    apply H1 with (n := n); apply map_fun_plus_l; auto; easy.
  - repeat red; intros.
    apply H2 with x s'.
    + destruct (star_dec s star_bottom).
      * subst.
        red in Compatible_comm0.
        inversion_clear Compatible_comm0.







Theorem fun_comm : forall f1 f2 x s, temp_name_mapping (fun_plus f1 f2) x s ->
                                     temp_name_mapping (fun_plus f2 f1) x s.
Proof.
  induction f1; intros.
  - inversion H; subst.
    + inversion H2.
    + inversion H2.
    + apply map_fun_plus_l'; auto.
    induction f2; auto.
    + inversion H; subst; auto.



Lemma in_domain_mapping_exists : forall f x, in_domain x f ->
                                             exists s, temp_name_mapping f x s.
Proof.
  intro f.
  induction f; intros.
  - inversion H.
  - inversion H.
    exists star_bottom; auto.
  - inversion H; subst.
    + exists (star_name y); auto.
    + exists star_bottom; auto.
  - inversion H; subst.
    + apply IHf1 in H1.
      inversion H1.
      exists x0.
      constructor.

Lemma mapping_in_range : forall f x n, temp_name_mapping f x (star_name n) ->
                                       in_range n f.
Proof.
  intros.
  induction f; inversion H; subst; auto.
  apply in_range_fun_remove; auto.
  intro.
  apply H6; rewrite H0; auto.
Qed.

Hint Resolve mapping_in_range.

Theorem Fun_prop_2 : forall f x y n,
                       temp_name_mapping f x (star_name n) ->
                       temp_name_mapping f y (star_name n) ->
                       x = y.
Proof.
  induction f; intros.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    inversion H0; subst.
    auto.
  - inversion H; inversion H0; subst.
    + apply (IHf1 x y n) in H3; auto.
    +
    apply IHf1 in H3; auto.
