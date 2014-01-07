Require Import Coq.Lists.List Coq.Logic.FunctionalExtensionality Names.

Module Fun.

  Definition temp_name_mapping := name -> option star.

  Definition temp_name_mapping_star := star -> option star.

  Definition empty : temp_name_mapping := fun _ => None.

  Definition domain (f : temp_name_mapping) (x : name) := f x <> None.

  Lemma domain_not_empty : forall f x, domain f x -> f <> empty.
  Proof.
    intros.
    intro.
    unfold domain in H.
    apply equal_f with x in H0.
    compute in H0.
    auto.
  Qed.

  Definition to_star_function (f : temp_name_mapping) : temp_name_mapping_star :=
    fun s : star =>
      match s with
        | star_name n => f n
        | _ => Some star_bottom
      end.

  Definition beq_option_star (o1 : option star) (o2 : option star) : bool :=
    match o1, o2 with
      | Some s1, Some s2 => beq_star s1 s2
      | _, _ => false
    end.

  Definition fun_plus (f1 : temp_name_mapping) (f2 : temp_name_mapping) : temp_name_mapping :=
    fun x : name =>
      match f1 x with
        | Some n => match n with
                      | star_bottom => match f2 x with
                                         | Some n' => Some n'
                                         | None => Some n
                                       end
                      | _ => Some n
                    end
        | None => f2 x
      end.

  Lemma fun_plus_empty_split : forall f1 f2, fun_plus f1 f2 = empty <-> f1 = empty /\ f2 = empty.
  Proof.
    unfold fun_plus.
    split.
      intro.
      split.
      apply functional_extensionality.
      intro.
      apply equal_f with x in H.
      destruct (f1 x).
        destruct s.
          auto.
          destruct (f2 x).
            discriminate.
            discriminate.
          discriminate.
        auto.

      apply functional_extensionality.
      intro.
      apply equal_f with x in H.
      destruct (f1 x).
        destruct s.
          discriminate.
          destruct (f2 x).
            discriminate.
            discriminate.
          discriminate.
        auto.

      intros.
      inversion_clear H.
      apply functional_extensionality.
      rewrite H0; rewrite H1.
      unfold empty.
      auto.
  Qed.

  Lemma fun_plus_domain : forall f1 f2 x, domain (fun_plus f1 f2) x <-> domain f1 x \/ domain f2 x.
  Proof.
    unfold domain.
    split.
      intro.
      unfold fun_plus in H.
      destruct (f1 x) eqn:?.
        induction s.
          left; auto.
          destruct (f2 x) eqn:?.
            right; auto.
            left; auto.
          left; auto.
          right; auto.
      intro.
      unfold fun_plus.
      inversion H.
        destruct (f1 x) eqn:?.
          induction s.
            auto.
            destruct (f2 x) eqn:?; intro; discriminate.
            auto.
          exfalso; apply H0; auto.
        destruct (f1 x).
          destruct s.
            intro; discriminate.
            destruct (f2 x).
              auto.
              auto.
            intro; discriminate.
          auto.
  Qed.

  Lemma fun_plus_not_domain : forall f1 f2 x, ~ domain (fun_plus f1 f2) x <-> ~ domain f1 x /\ ~ domain f2 x.
  Proof.
    unfold domain.
    split.
      intros.
      split.
      intro.
      apply H.
      intro.
      unfold fun_plus in H1.
      apply H0.
      destruct (f1 x) eqn:?.
        destruct s eqn:?.
          discriminate.
          destruct (f2 x) eqn:?.
            discriminate.
            discriminate.
          discriminate.
        auto.
      intro.
      apply H.
      intro.
      unfold fun_plus in H1.
      apply H0.
      destruct (f1 x) eqn:?.
        destruct s eqn:?.
          discriminate.
          destruct (f2 x) eqn:?.
            discriminate.
            discriminate.
          discriminate.
        auto.

      intros.
      inversion H.
      intro.
      unfold fun_plus in H2.
      apply H0.
      intro.
      rewrite H3 in H2.
      apply H1.
      auto.
  Qed.

  (* Lemma fun_plus_left. Lemma fun_plus_right. *)

  Definition fun_remove f x : temp_name_mapping :=
    fun y : name =>
      if beq_name y x
      then None
      else
        match f y with
          | Some (star_name n) =>
            if beq_name n x
            then Some star_star
            else Some (star_name n)
          | a => a
        end.

  Goal forall x y z f, x <> y -> y <> z -> z <> x ->
         f = (fun a =>
            if beq_name a x then Some (star_name y) else
              if beq_name a y then Some (star_name z) else
                if beq_name a z then Some star_bottom else None) ->
         fun_remove f z z = None /\
         fun_remove f z y = Some star_star /\
         fun_remove f z x = Some (star_name y).
  Proof.
    intros.
    split.
      unfold fun_remove.
      rewrite beq_name_refl.
      auto.

      split.
        unfold fun_remove.
        apply beq_name_false_iff in H0.
        rewrite H0.
        rewrite H2.
        apply beq_name_false_iff in H.
        rewrite beq_name_sym in H.
        rewrite H.
        rewrite beq_name_refl.
        rewrite beq_name_refl.
        auto.

        unfold fun_remove.
        rewrite H2.
        apply beq_name_false_iff in H1.
        rewrite beq_name_sym in H1.
        rewrite H1.
        rewrite beq_name_refl.
        apply beq_name_false_iff in H0.
        rewrite H0.
        auto.
  Qed.

  Lemma fun_remove_domain_1 : forall f x y, domain f x -> domain (fun_remove f y) x \/ x = y.
  Proof.
    unfold domain.
    unfold fun_remove.
    intros.
    destruct (beq_name x y) eqn:?.
      apply beq_name_true_iff in Heqb.
      right; auto.

      destruct (f x).
        destruct s.
          left.
          destruct (beq_name n y); easy.
          left; easy.
          left; easy.
          auto.
  Qed.

  Lemma fun_remove_domain_2 : forall f x y, domain (fun_remove f y) x -> x <> y /\ domain f x.
  Proof.
    unfold domain.
    unfold fun_remove.
    split.
      intro.
      apply beq_name_true_iff in H0.
      rewrite H0 in H.
      apply H; auto.

      intro.
      rewrite H0 in H.
      apply H.
      destruct (beq_name x y); auto.
  Qed.

  Lemma fun_remove_not_domain_1 : forall f x y, ~ domain f x -> ~ domain (fun_remove f y) x.
  Proof.
    unfold domain.
    intros.
    unfold fun_remove.
    intro.
    destruct (beq_name x y) eqn:?.
      apply H0; auto.
      apply H.
      intro.
      rewrite H1 in H0.
      apply H0; auto.
  Qed.

  Lemma fun_remove_not_domain_2 : forall f x y, ~ domain (fun_remove f y) x -> x = y \/ ~ domain f x.
  Proof.
    unfold domain.
    unfold fun_remove.
    intros.
    destruct (beq_name x y) eqn:?.
      apply beq_name_true_iff in Heqb.
      left; auto.

      right.
      intro.
      apply H.
      destruct (f x) eqn:?.
        destruct s eqn:?.
          destruct (beq_name n y) eqn:?.
            intro; discriminate.
            intro; discriminate.
          intro; discriminate.
          intro; discriminate.
        auto.
  Qed.

  Definition fun_join (f : temp_name_mapping) : temp_name_mapping :=
    fun x : name =>
      match f x with
        | Some n => (to_star_function f) n
        | None => None
      end.

  Definition Fun_comm (f1 : temp_name_mapping) (f2 : temp_name_mapping) :=
    forall (x : name), fun_plus f1 f2 x = fun_plus f2 f1 x.

  (* f(x) /= x *)
  Definition Fun_prop1 (f : temp_name_mapping) :=
    forall x : name, f x <> Some (star_name x).

  (* f(x) = f(y) and is not member of {_|_, *} -> x = y *)
  Definition Fun_prop2 (f : temp_name_mapping) :=
    forall (x y : name), domain f x -> domain f y ->
                         f x = f y ->
                         f x <> Some star_bottom ->
                         f x <> Some star_star ->
                         f y <> Some star_bottom ->
                         f y <> Some star_star ->
                         x = y.

  (* f*(f(x)) = _|_ *)
  Definition Fun_prop3 (f : temp_name_mapping) :=
    forall x, domain f x -> fun_join f x = Some star_bottom.

  Definition Fun_prop (f : temp_name_mapping) :=
    Fun_prop1 f /\ Fun_prop2 f /\ Fun_prop3 f.

  Record Compatible (f1 : temp_name_mapping) (f2 : temp_name_mapping) := Build_compatible {
    Compatible_comm : Fun_comm f1 f2;
    Compatible_prop : Fun_prop (fun_plus f1 f2)
  }.

  (* ch_empty *)

  Definition ch_empty := empty.

  Lemma ch_empty_prop_1 : Fun_prop1 ch_empty.
  Proof.
    unfold Fun_prop1.
    intro.
    intro.
    compute in H.
    discriminate.
  Qed.

  Lemma ch_empty_prop_2 : Fun_prop2 ch_empty.
  Proof.
    unfold Fun_prop2.
    intros.
    compute in H.
    exfalso; apply H; auto.
  Qed.

  Lemma ch_empty_prop_3 : Fun_prop3 ch_empty.
  Proof.
    unfold Fun_prop3.
    intros.
    compute in H.
    exfalso; apply H; auto.
  Qed.

  Theorem ch_empty_prop : Fun_prop ch_empty.
  Proof.
    unfold Fun_prop.
    split.
    apply ch_empty_prop_1.
    split.
    apply ch_empty_prop_2.
    apply ch_empty_prop_3.
  Qed.

  (* ch_singleton *)

  Definition ch_singleton (n : name) : temp_name_mapping :=
    fun x => if beq_name n x
             then Some star_bottom
             else None.

  Lemma ch_singleton_equal : forall x y, ch_singleton x = ch_singleton y <-> x = y.
  Proof.
    unfold ch_singleton.
    split; intros.
      apply equal_f with x in H.
      rewrite beq_name_refl in H.
      destruct (beq_name y x) eqn:?.
        apply beq_name_true_iff in Heqb.
        auto.

        discriminate.

      rewrite H.
      auto.
  Qed.

  Lemma ch_singleton_not_empty : forall x, ch_singleton x <> empty.
  Proof.
    intros.
    intro.
    apply equal_f with x in H.
    unfold ch_singleton in H.
    rewrite beq_name_refl in H.
    discriminate.
  Qed.

  Lemma ch_singleton_domain : forall x y, domain (ch_singleton x) y <-> x = y.
  Proof.
    unfold domain.
    unfold ch_singleton.
    intros.
    destruct (beq_name x y) eqn:?.
      apply beq_name_true_iff in Heqb.
      rewrite Heqb.
      split.
        intro; auto.
        intro; intro; discriminate.
      split.
        intro; exfalso.
        apply H; auto.
        intro; apply beq_name_false_iff in Heqb.
        contradiction.
  Qed.

  Lemma ch_singleton_not_domain : forall x y, ~ domain (ch_singleton x) y <-> x <> y.
  Proof.
    unfold domain.
    unfold ch_singleton.
    intros.
    destruct (beq_name x y) eqn:?.
      apply beq_name_true_iff in Heqb.
      rewrite Heqb.
      split.
        intro; intro.
        unfold not in H.
        apply H.
        intro.
        discriminate.

        intro.
        exfalso; apply H; auto.

      split.
        intro; intro.
        apply beq_name_false_iff in Heqb.
        auto.

        intro.
        intro.
        apply H0; auto.
  Qed.

  Lemma ch_singleton_not_name : forall x y z, ch_singleton x y <> Some (star_name z).
  Proof.
    unfold ch_singleton.
    intros.
    destruct (beq_name x y) eqn:?.
      intro.
      discriminate.

      intro.
      discriminate.
  Qed.

  Lemma ch_singleton_prop_1 : forall n, Fun_prop1 (ch_singleton n).
  Proof.
    unfold Fun_prop1.
    intros.
    unfold ch_singleton.
    destruct (beq_name n x); intro; discriminate.
  Qed.

  Lemma ch_singleton_prop_2 : forall n, Fun_prop2 (ch_singleton n).
  Proof.
    unfold Fun_prop2.
    unfold domain.
    unfold ch_singleton.
    intros.
    destruct (beq_name n x) eqn:?.
      apply beq_name_true_iff in Heqb.
      destruct (beq_name n y) eqn:?.
        apply beq_name_true_iff in Heqb0.
        rewrite <- Heqb.
        rewrite Heqb0.
        auto.

        discriminate.
      exfalso.
      apply H.
      auto.
  Qed.

  Lemma ch_singleton_prop_3 : forall n, Fun_prop3 (ch_singleton n).
  Proof.
    unfold Fun_prop3.
    unfold domain.
    unfold ch_singleton.
    unfold fun_join.
    intros.
    destruct (beq_name n x) eqn:?.
      apply beq_name_true_iff in Heqb.
      rewrite Heqb.
      compute.
      auto.

      exfalso.
      apply H.
      auto.
  Qed.

  Theorem ch_singleton_prop : forall n, Fun_prop (ch_singleton n).
  Proof.
    unfold Fun_prop.
    split.
    apply ch_singleton_prop_1.
    split.
    apply ch_singleton_prop_2.
    apply ch_singleton_prop_3.
  Qed.

  (* ch_two *)

  Definition ch_two (n m : name) : temp_name_mapping :=
    fun x =>
      if beq_name n x
      then Some (star_name m)
      else if beq_name m x
           then Some star_bottom
           else None.

  Lemma ch_two_not_empty : forall x y, ch_two x y <> empty.
  Proof.
    intros.
    intro.
    apply equal_f with x in H.
    unfold ch_two in H.
    rewrite beq_name_refl in H.
    compute in H.
    discriminate.
  Qed.

  Theorem ch_two_domain : forall x y z, domain (ch_two x y) z <-> x = z \/ y = z.
  Proof.
    split.
    intros.

    unfold domain in H.
    unfold ch_two in H.
    destruct (beq_name x z) eqn:?.
      apply beq_name_true_iff in Heqb.
      left; auto.

      destruct (beq_name y z) eqn:?.
        apply beq_name_true_iff in Heqb0.
        right; auto.

        exfalso; apply H; auto.
    intro.
    unfold domain.
    unfold ch_two.
    inversion H.
      rewrite <- H0.
      rewrite beq_name_refl.
      intro; discriminate.

      rewrite H0.
      destruct (beq_name x z) eqn:?.
        intro; discriminate.
        rewrite beq_name_refl.
        intro; discriminate.
  Qed.

  Lemma ch_two_not_domain : forall x y z, ~ domain (ch_two x y) z <-> x <> z /\ y <> z.
  Proof.
    unfold domain.
    unfold ch_two.
    intros.
    destruct (beq_name x z) eqn:?.
      apply beq_name_true_iff in Heqb.
      rewrite Heqb.
      split; try split.
        exfalso; apply H.
        intro; discriminate.

        exfalso; apply H; intro; discriminate.

        intro.
        inversion H.
        exfalso; apply H0; auto.
      split; try split.
        destruct (beq_name y z) eqn:?.
          apply beq_name_true_iff in Heqb0.
          intro.
          rewrite H0 in Heqb.
          rewrite beq_name_refl in Heqb.
          discriminate.

          intro.
          rewrite H0 in Heqb.
          rewrite beq_name_refl in Heqb.
          discriminate.

        intro.
        rewrite H0 in H.
        rewrite beq_name_refl in H.
        apply H; intro.
        discriminate.

        intros.
        inversion H.
        intro.
        destruct (beq_name y z) eqn:?.
        apply beq_name_true_iff in Heqb0.
        auto.
        apply H2; auto.
  Qed.

  Lemma ch_two_prop_1 : forall n m, n <> m -> Fun_prop1 (ch_two n m).
  Proof.
    unfold Fun_prop1.
    unfold ch_two.
    intros.
    destruct (beq_name n x) eqn:?.
      apply beq_name_true_iff in Heqb.
      rewrite <- Heqb.
      intro.
      inversion H0.
      auto.

      destruct (beq_name m x) eqn:?.
        intro.
        discriminate.
        intro.
        discriminate.
  Qed.

  Lemma ch_two_prop_2 : forall n m, Fun_prop2 (ch_two n m).
  Proof.
    unfold Fun_prop2.
    unfold domain.
    unfold ch_two.
    intros.
    destruct (beq_name n x) eqn:?.
      apply beq_name_true_iff in Heqb.
      destruct (beq_name n y) eqn:?.
        apply beq_name_true_iff in Heqb0.
        rewrite <- Heqb.
        rewrite Heqb0.
        auto.

        destruct (beq_name m y) eqn:?.
          discriminate.
          discriminate.
      destruct (beq_name m x) eqn:?.
        apply beq_name_true_iff in Heqb0.
        destruct (beq_name n y) eqn:?.
          discriminate.
          destruct (beq_name m y) eqn:?.
            apply beq_name_true_iff in Heqb2.
            rewrite <- Heqb0.
            apply Heqb2.

            discriminate.
        exfalso; apply H0; auto.
  Qed.

  Lemma ch_two_prop_3 : forall n m, n <> m -> Fun_prop3(ch_two n m).
  Proof.
    unfold Fun_prop3.
    unfold domain.
    unfold ch_two.
    unfold fun_join.
    unfold to_star_function.
    intros.
    destruct (beq_name n x) eqn:?.
      apply beq_name_true_iff in Heqb.
      rewrite Heqb.
      rewrite beq_name_refl.
      destruct (beq_name x m) eqn:?.
        apply beq_name_true_iff in Heqb0.
        rewrite Heqb0 in Heqb.
        contradiction.

        auto.
      destruct (beq_name m x) eqn:?.
        auto.
        exfalso; apply H0; auto.
  Qed.

  Theorem ch_two_prop : forall n m, n <> m -> Fun_prop (ch_two n m).
  Proof.
    split.
    apply ch_two_prop_1; auto.
    split.
    apply ch_two_prop_2.
    apply ch_two_prop_3; auto.
  Qed.
End Fun.
