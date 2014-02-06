Require Import Coq.Lists.List Coq.Logic.FunctionalExtensionality Names.

Module Fun.

  Definition temp_name_mapping := name -> option star.

  Definition temp_name_mapping_star := star -> option star.

  Definition empty : temp_name_mapping := fun _ => None.

  Definition in_domain (f : temp_name_mapping) (x : name) := f x <> None.

  Definition in_range f x := exists y : name, f y = Some (star_name x).

  Definition in_range_in_domain f := forall x, in_range f x -> in_domain f x.

  Lemma in_domain_not_empty : forall f x, in_domain f x -> f <> empty.
  Proof.
    intros.
    intro.
    unfold in_domain in H.
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

  Lemma fun_plus_assoc : forall f1 f2 f3, fun_plus f1 (fun_plus f2 f3) = fun_plus (fun_plus f1 f2) f3.
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    unfold fun_plus.
    destruct (f1 x); auto.
    destruct s; auto.
    destruct (f2 x); auto.
    destruct s; auto.
    destruct (f3 x); auto.
  Qed.

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

  Lemma fun_plus_in_domain : forall f1 f2 x, in_domain (fun_plus f1 f2) x <-> in_domain f1 x \/ in_domain f2 x.
  Proof.
    unfold in_domain.
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

  Lemma fun_plus_not_in_domain : forall f1 f2 x, ~ in_domain (fun_plus f1 f2) x <-> ~ in_domain f1 x /\ ~ in_domain f2 x.
  Proof.
    unfold in_domain.
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

  Lemma fun_plus_in_range_in_domain : forall f1 f2,
                                  in_range_in_domain f1 ->
                                  in_range_in_domain f2 ->
                                  in_range_in_domain (fun_plus f1 f2).
  Proof.
    unfold in_range_in_domain.
    unfold in_range.
    unfold in_domain.
    unfold fun_plus.
    intros.
    destruct (f1 x) eqn:?.
      destruct s; try (intro; discriminate).
      destruct (f2 x) eqn:?; try (intro; discriminate).

      destruct (f2 x) eqn:?; try (intro; discriminate).
      inversion_clear H1.
      destruct (f1 x0) eqn:?.
        destruct s.
          specialize (H x).
          rewrite Heqo in H.
          apply H.
          exists x0.
          rewrite Heqo1; auto.

          destruct (f2 x0) eqn:?.
            inversion H2; subst.
            specialize (H0 x).
            rewrite Heqo0 in H0.
            apply H0.
            exists x0.
            auto.

            discriminate.
          discriminate.
        specialize (H0 x).
        rewrite Heqo0 in H0.
        apply H0.
        exists x0.
        auto.
  Qed.

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

  Lemma fun_remove_in_domain_1 : forall f x y, in_domain f x -> in_domain (fun_remove f y) x \/ x = y.
  Proof.
    unfold in_domain.
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

  Lemma fun_remove_in_domain_2 : forall f x y, in_domain (fun_remove f y) x -> x <> y /\ in_domain f x.
  Proof.
    unfold in_domain.
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

  Lemma fun_remove_not_in_domain_1 : forall f x y, ~ in_domain f x -> ~ in_domain (fun_remove f y) x.
  Proof.
    unfold in_domain.
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

  Lemma fun_remove_not_in_domain_2 : forall f x y, ~ in_domain (fun_remove f y) x -> x = y \/ ~ in_domain f x.
  Proof.
    unfold in_domain.
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

  Lemma fun_remove_in_range_in_domain : forall f x, in_range_in_domain f -> in_range_in_domain (fun_remove f x).
  Proof.
    unfold in_range_in_domain.
    unfold in_range, in_domain, fun_remove.
    intros.
    inversion_clear H0.
    destruct (beq_name x0 x) eqn:?.
      destruct (beq_name x1 x).
        discriminate.

        destruct (f x1) eqn:?.
          destruct s.
            destruct (beq_name n x) eqn:?.
              discriminate.

              inversion H1.
              subst.
              rewrite Heqb in Heqb0.
              discriminate.

            discriminate.

            discriminate.

          discriminate.

      destruct (f x0) eqn:?.
        destruct s.
          destruct (beq_name n x); intro; discriminate.

          intro; discriminate.

          intro; discriminate.

        destruct (beq_name x1 x) eqn:?.
          discriminate.

          destruct (f x1) eqn:?.
            destruct s.
              destruct (beq_name n x) eqn:?.
                discriminate.

                inversion H1; subst.
                specialize (H x0).
                rewrite Heqo in H.
                apply H.
                exists x1; auto.

              discriminate.

              discriminate.

            discriminate.
  Qed.

  Definition fun_join (f : temp_name_mapping) : temp_name_mapping :=
    fun x : name =>
      match f x with
        | Some n => (to_star_function f) n
        | None => None
      end.

  Definition Fun_comm (f1 : temp_name_mapping) (f2 : temp_name_mapping) :=
    fun_plus f1 f2 = fun_plus f2 f1.

  (* f(x) /= x *)
  Definition Fun_prop_1 (f : temp_name_mapping) :=
    forall x : name, f x <> Some (star_name x).

  (* f(x) = f(y) and is not member of {_|_, *} -> x = y *)
  Definition Fun_prop_2 (f : temp_name_mapping) :=
    forall (x y : name), (exists n, f x = Some (star_name n)) ->
                         (exists n, f y = Some (star_name n)) ->
                         f x = f y ->
                         x = y.

  (* f*(f(x)) = _|_ *)
  Definition Fun_prop_3 (f : temp_name_mapping) :=
    forall x, in_domain f x -> fun_join f x = Some star_bottom.

  Definition Fun_prop (f : temp_name_mapping) :=
    Fun_prop_1 f /\ Fun_prop_2 f /\ Fun_prop_3 f.

  Record Compatible (f1 : temp_name_mapping) (f2 : temp_name_mapping) := Build_compatible {
    Compatible_comm : Fun_comm f1 f2;
    Compatible_prop : Fun_prop (fun_plus f1 f2)
  }.

  Fixpoint Mutually_compatible (fs : list temp_name_mapping) :=
    match fs with
      | nil => True
      | f :: fs' => Forall (Compatible f) fs' /\ Mutually_compatible fs'
    end.

  (* ch_empty *)

  Definition ch_empty := empty.

  Lemma ch_empty_in_range_in_domain : in_range_in_domain ch_empty.
  Proof.
    unfold in_range_in_domain.
    unfold in_range, in_domain.
    intros.
      inversion H.
      compute in H0; discriminate.
  Qed.

  Lemma ch_empty_prop_1 : Fun_prop_1 ch_empty.
  Proof.
    unfold Fun_prop_1.
    intro.
    intro.
    compute in H.
    discriminate.
  Qed.

  Lemma ch_empty_prop_2 : Fun_prop_2 ch_empty.
  Proof.
    unfold Fun_prop_2.
    intros.
    compute in H.
    inversion H.
    discriminate.
  Qed.

  Lemma ch_empty_prop_3 : Fun_prop_3 ch_empty.
  Proof.
    unfold Fun_prop_3.
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

  Lemma ch_singleton_in_domain : forall x y, in_domain (ch_singleton x) y <-> x = y.
  Proof.
    unfold in_domain.
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

  Lemma ch_singleton_not_in_domain : forall x y, ~ in_domain (ch_singleton x) y <-> x <> y.
  Proof.
    unfold in_domain.
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

  Lemma ch_singleton_in_range_in_domain : forall x, in_range_in_domain (ch_singleton x).
  Proof.
    unfold in_range_in_domain.
    unfold in_range, in_domain.
    unfold ch_singleton.
    intros.
    inversion H.
    destruct (beq_name x x1) eqn:?; discriminate.
  Qed.

  Lemma ch_singleton_prop_1 : forall n, Fun_prop_1 (ch_singleton n).
  Proof.
    unfold Fun_prop_1.
    intros.
    unfold ch_singleton.
    destruct (beq_name n x); intro; discriminate.
  Qed.

  Lemma ch_singleton_prop_2 : forall n, Fun_prop_2 (ch_singleton n).
  Proof.
    unfold Fun_prop_2.
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
      inversion H.
      discriminate.
  Qed.

  Lemma ch_singleton_prop_3 : forall n, Fun_prop_3 (ch_singleton n).
  Proof.
    unfold Fun_prop_3.
    unfold in_domain.
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

  Theorem ch_two_in_domain : forall x y z, in_domain (ch_two x y) z <-> x = z \/ y = z.
  Proof.
    split.
    intros.

    unfold in_domain in H.
    unfold ch_two in H.
    destruct (beq_name x z) eqn:?.
      apply beq_name_true_iff in Heqb.
      left; auto.

      destruct (beq_name y z) eqn:?.
        apply beq_name_true_iff in Heqb0.
        right; auto.

        exfalso; apply H; auto.
    intro.
    unfold in_domain.
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

  Lemma ch_two_not_in_domain : forall x y z, ~ in_domain (ch_two x y) z <-> x <> z /\ y <> z.
  Proof.
    unfold in_domain.
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

  Lemma ch_two_in_range_in_domain : forall x y, x <> y -> in_range_in_domain (ch_two x y).
  Proof.
    unfold in_range_in_domain.
    unfold in_range, in_domain, ch_two.
    intros.
    inversion_clear H0.
    destruct (beq_name x x1) eqn:?.
      inversion H1.
      destruct (beq_name x x0) eqn:?.
        intro; discriminate.

        rewrite beq_name_refl.
        intro; discriminate.

      destruct (beq_name x x0) eqn:?.
        intro; discriminate.

        destruct (beq_name y x0) eqn:?.
          intro; discriminate.

          destruct (beq_name y x1); discriminate.
  Qed.

  Lemma ch_two_prop_1 : forall n m, n <> m -> Fun_prop_1 (ch_two n m).
  Proof.
    unfold Fun_prop_1.
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

  Lemma ch_two_prop_2 : forall n m, Fun_prop_2 (ch_two n m).
  Proof.
    unfold Fun_prop_2.
    unfold in_domain.
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
        inversion H; discriminate.
  Qed.

  Lemma ch_two_prop_3 : forall n m, n <> m -> Fun_prop_3(ch_two n m).
  Proof.
    unfold Fun_prop_3.
    unfold in_domain.
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

  Lemma fun_plus_prop_1 : forall f1 f2,
                            Fun_prop_1 f1 ->
                            Fun_prop_1 f2 ->
                            Fun_prop_1 (fun_plus f1 f2).
  Proof.
    unfold Fun_prop_1.
    unfold fun_plus.
    intros.
    destruct (f1 x) eqn:?.
      destruct s.
        rewrite <- Heqo.
        apply H.

        destruct (f2 x) eqn:?.
          rewrite <- Heqo0.
          apply H0.

          intro; discriminate.

        intro; discriminate.
      apply H0.
  Qed.

  Lemma fun_plus_prop_2 : forall f1 f2,
                            in_range_in_domain f1 ->
                            in_range_in_domain f2 ->
                            (forall x,
                               (in_domain f1 x -> ~ in_domain f2 x) /\
                               (in_domain f2 x -> ~ in_domain f1 x)) ->
                            Fun_prop_2 f1 ->
                            Fun_prop_2 f2 ->
                            Fun_prop_2 (fun_plus f1 f2).
  Proof.
    unfold Fun_prop_2.
    unfold in_domain.
    unfold fun_plus.
    intros.
    destruct (f1 x) eqn:?.
      destruct (f1 y) eqn:?.
        induction s.
          induction s0.
            apply H2.
              exists n; auto.
              exists n0; auto.
              rewrite Heqo; rewrite Heqo0; auto.
            destruct (f2 y) eqn:?.
              specialize (H1 y).
              inversion H1.
              rewrite Heqo0 in H7.
              rewrite Heqo1 in H7.
              assert (Some star_bottom <> None).
                intro; discriminate.
              apply H7 in H9.
              exfalso; apply H9; intro; discriminate.

              discriminate.
            discriminate.
          induction s0.
            destruct (f2 x) eqn:?.
              specialize (H1 x).
              inversion H1.
              rewrite Heqo in H7.
              rewrite Heqo1 in H7.
              assert (Some star_bottom <> None).
                intro; discriminate.
              apply H7 in H9.
              exfalso; apply H9; intro; discriminate.

              discriminate.
            destruct (f2 x) eqn:?.
              specialize (H1 x).
              inversion H1.
              rewrite Heqo in H7.
              rewrite Heqo1 in H7.
              assert (Some star_bottom <> None).
                intro; discriminate.
              apply H7 in H9.
              exfalso; apply H9; intro; discriminate.

              inversion H4; discriminate.
            inversion H5; discriminate.
          inversion H4; discriminate.

        induction s.
          symmetry in H6.
          unfold in_range_in_domain, in_range, in_domain in H.
          unfold in_range_in_domain, in_range, in_domain in H0.
          specialize (H n).
          specialize (H0 n).
          specialize (H1 n).
          inversion H1.
          assert (exists y : name, f1 y = Some (star_name n)).
            exists x; auto.
          assert (exists y : name, f2 y = Some (star_name n)).
            exists y; auto.
          apply H in H9.
          apply H0 in H10.
          apply H7 in H9.
          exfalso; apply H9; auto.

          destruct (f2 x) eqn:?.
            apply H3.
              rewrite Heqo1; auto.

              auto.

              rewrite Heqo1; auto.
            inversion H4; discriminate.

          inversion H4; discriminate.
      inversion H4; subst.
      rewrite H7 in H6.
      destruct (f1 y) eqn:?.
        destruct s.
          inversion H6; subst.
          unfold in_range_in_domain, in_range, in_domain in H.
          unfold in_range_in_domain, in_range, in_domain in H0.
          specialize (H n).
          specialize (H0 n).
          assert (exists y, f1 y = Some (star_name n)).
            exists y; auto.
          assert (exists y, f2 y = Some (star_name n)).
            exists x; auto.
          apply H in H8.
          apply H0 in H9.
          specialize (H1 n).
          inversion H1.
          apply H10 in H8.
          exfalso; apply H8; auto.

          destruct (f2 y) eqn:?.
            specialize (H1 y).
            inversion H1.
            assert (f1 y <> None).
              rewrite Heqo0; intro; discriminate.
            apply H8 in H10.
            exfalso; apply H10.
            rewrite Heqo1; intro; discriminate.

          discriminate.
        discriminate.

        apply H3.
          exists x0; auto.

          exists x0; rewrite H6; auto.

          rewrite H7; auto.
  Qed.

  Lemma fun_plus_prop_3 : forall f1 f2,
                            (forall x,
                               (in_domain f1 x -> ~ in_domain f2 x) /\
                               (in_domain f2 x -> ~ in_domain f1 x)) ->
                            Fun_prop_3 f1 ->
                            Fun_prop_3 f2 ->
                            Fun_prop_3 (fun_plus f1 f2).
  Proof.
    unfold Fun_prop_3.
    unfold fun_join.
    unfold to_star_function.
    unfold fun_plus.
    unfold in_domain.
    intros.
    destruct (f1 x) eqn:?.
      destruct s.
        destruct (f1 n) eqn:?.
          specialize (H0 x).
          assert (f1 x <> None).
            rewrite Heqo.
            intro; discriminate.
          apply H0 in H3.
          rewrite Heqo in H3.
          rewrite Heqo0 in H3.
          inversion H3.
          destruct (f2 n) eqn:?.
            specialize (H n).
            inversion H.
            assert (f1 n <> None).
              rewrite Heqo0; intro; discriminate.
            apply H4 in H7.
            exfalso; apply H7; intro.
            rewrite Heqo1 in H8; discriminate.

            auto.

          specialize (H0 x).
          assert (f1 x <> None).
            rewrite Heqo; intro; discriminate.
          apply H0 in H3.
          rewrite Heqo in H3.
          rewrite Heqo0 in H3; discriminate.

        destruct (f2 x) eqn:?.
          specialize (H x).
          inversion H.
          assert (f1 x <> None).
            rewrite Heqo; intro; discriminate.
          apply H3 in H5.
          exfalso; apply H5; intro.
          rewrite Heqo0 in H6; discriminate.

          auto.
        auto.
      destruct (f2 x) eqn:?.
        destruct s.
          destruct (f1 n) eqn:?.
            specialize (H1 x).
            assert (f2 x <> None).
              rewrite Heqo0; intro; discriminate.
            apply H1 in H3.
            rewrite Heqo0 in H3.
            specialize (H n).
            inversion H.
            assert (f1 n <> None).
              rewrite Heqo1; intro; discriminate.
            apply H4 in H6.
            exfalso; apply H6; intro.
            rewrite H3 in H7; discriminate.

            assert (f2 x <> None).
              rewrite Heqo0; intro; discriminate.
            apply H1 in H3.
            rewrite Heqo0 in H3.
            auto.
          auto.
          auto.
        exfalso; apply H2; auto.
  Qed.

  Theorem fun_plus_prop : forall f1 f2,
                            in_range_in_domain f1 ->
                            in_range_in_domain f2 ->
                            (forall x,
                               (in_domain f1 x -> ~ in_domain f2 x) /\
                               (in_domain f2 x -> ~ in_domain f1 x)) ->
                            Fun_prop f1 ->
                            Fun_prop f2 ->
                            Fun_prop (fun_plus f1 f2).
  Proof.
    intros.
    inversion_clear H2.
    inversion_clear H5.
    inversion_clear H3.
    inversion_clear H7.
    unfold Fun_prop.
    split; try split.
    apply fun_plus_prop_1; auto.
    apply fun_plus_prop_2; auto.
    apply fun_plus_prop_3; auto.
  Qed.

  Lemma fun_prop_plus_fst : forall f1 f2,
                              Fun_prop (fun_plus f1 f2) ->
                              in_range_in_domain f1 ->
                              Fun_prop f1.
  Proof.
    intros f1 f2 H rd.
    inversion_clear H.
    inversion_clear H1.

    unfold Fun_prop.
    unfold Fun_prop_1 in H0.
    unfold Fun_prop_2 in H.
    unfold Fun_prop_3 in H2.

    split; try split.
      unfold Fun_prop_1.
      intros.
      intro.
      apply H0 with x.
      unfold fun_plus.
      rewrite H1; auto.

      unfold Fun_prop_2; intros.
      apply H.
        inversion_clear H1.
        exists x0.
        unfold fun_plus.
        rewrite H5; auto.

        inversion_clear H3.
        exists x0.
        unfold fun_plus.
        rewrite H5; auto.

        unfold fun_plus.
        destruct (f1 x); auto.
          destruct s; auto.
            destruct (f1 y); auto.
              destruct s; auto.
              inversion H4.
            inversion H4.
          destruct (f1 y); auto.
            destruct s; auto.
              discriminate.
              inversion H1; discriminate.
              inversion H1; discriminate.
            discriminate.
          inversion H1; discriminate.
          inversion H1; discriminate.

      unfold Fun_prop_3; intros.
      unfold fun_join.
      unfold to_star_function.

      unfold in_range_in_domain in rd.
      unfold in_range in rd.

      unfold fun_join in H2.
      unfold in_domain in H2, H1, rd.
      unfold to_star_function in H2.
      unfold fun_plus in H2.
      specialize H2 with x.
      destruct (f1 x) eqn:?; auto.
        destruct s; auto.
        destruct (f1 n) eqn:?; auto.
          destruct s; auto.
          specialize rd with n.
          assert (exists y, f1 y = Some (star_name n)).
            exists x; auto.
          apply rd in H3.
          easy.

          exfalso; apply H1; auto.
  Qed.

  Lemma compatible_split : forall f1 f2,
                             Compatible f1 f2 ->
                             in_range_in_domain f1 ->
                             in_range_in_domain f2 ->
                             Fun_prop f1 /\ Fun_prop f2.
  Proof.
    assert (forall f1 f2, Fun_prop (fun_plus f1 f2) -> in_range_in_domain f1 -> Fun_prop f1).
    intros f1 f2 H rd.
    inversion_clear H.
    inversion_clear H1.

    unfold Fun_prop.
    unfold Fun_prop_1 in H0.
    unfold Fun_prop_2 in H.
    unfold Fun_prop_3 in H2.

    split; try split.
      unfold Fun_prop_1.
      intros.
      intro.
      apply H0 with x.
      unfold fun_plus.
      rewrite H1; auto.

      unfold Fun_prop_2; intros.
      apply H.
        inversion_clear H1.
        exists x0.
        unfold fun_plus.
        rewrite H5; auto.

        inversion_clear H3.
        exists x0.
        unfold fun_plus.
        rewrite H5; auto.

        unfold fun_plus.
        destruct (f1 x); auto.
          destruct s; auto.
            destruct (f1 y); auto.
              destruct s; auto.
              inversion H4.
            inversion H4.
          destruct (f1 y); auto.
            destruct s; auto.
              discriminate.
              inversion H1; discriminate.
              inversion H1; discriminate.
            discriminate.
          inversion H1; discriminate.
          inversion H1; discriminate.

      unfold Fun_prop_3; intros.
      unfold fun_join.
      unfold to_star_function.

      unfold in_range_in_domain in rd.
      unfold in_range in rd.

      unfold fun_join in H2.
      unfold in_domain in H2, H1, rd.
      unfold to_star_function in H2.
      unfold fun_plus in H2.
      specialize H2 with x.
      destruct (f1 x) eqn:?; auto.
        destruct s; auto.
        destruct (f1 n) eqn:?; auto.
          destruct s; auto.
          specialize rd with n.
          assert (exists y, f1 y = Some (star_name n)).
            exists x; auto.
          apply rd in H3.
          easy.

          exfalso; apply H1; auto.

  intros.
  inversion H0 as [c p].
  split.
    apply H with f2; auto.
    unfold Fun_comm in c.
    rewrite c in p.
    apply H with f1; auto.
Qed.

  Theorem fun_plus_compatible : forall f f1 f2,
                                  in_range_in_domain f ->
                                  in_range_in_domain f1 ->
                                  in_range_in_domain f2 ->
                                  Compatible f (fun_plus f1 f2) ->
                                  Compatible f1 f2 ->
                                  Mutually_compatible (f :: f1 :: f2 :: nil).
  Proof.
    intros.
    simpl.
    inversion_clear H2 as [c0 p0].
    inversion_clear H3 as [c1 p1].
    unfold Fun_comm in c0.
    unfold Fun_comm in c1.
    subst.
    assert (Fun_comm f f1).
      unfold Fun_comm.
      apply functional_extensionality; intros.
      apply equal_f with x in c1.
      apply equal_f with x in c0.
      unfold fun_plus.
      unfold fun_plus in c1, c0.
      destruct (f x); auto.
        destruct s; auto; destruct (f1 x); auto; destruct s; auto.
        destruct (f1 x); auto; destruct s; auto.
    assert (Fun_comm f f2).
      rewrite c1 in c0.
      symmetry in c1.
      unfold Fun_comm.
      apply functional_extensionality; intros.
      apply equal_f with x in c1.
      apply equal_f with x in c0.
      unfold fun_plus.
      unfold fun_plus in c1, c0.
      destruct (f x); auto.
        destruct s; auto; destruct (f2 x); auto; destruct s; auto.
        destruct (f2 x); auto; destruct s; auto.
    split; try (split; try (split; try (split; try split))).
      apply Forall_cons; auto.
        apply Build_compatible; auto.
        rewrite fun_plus_assoc in p0.
        apply fun_prop_plus_fst in p0; auto.
        apply fun_plus_in_range_in_domain; auto.

        apply Forall_cons; auto.
        apply Build_compatible; auto.
        rewrite c1 in p0.
        rewrite fun_plus_assoc in p0.
        apply fun_prop_plus_fst in p0; auto.
        apply fun_plus_in_range_in_domain; auto.
      apply Forall_cons; auto.
      apply Build_compatible; auto.

      auto.
  Qed.

  Lemma fun_remove_prop_1 : forall f x,
                              Fun_prop_1 f ->
                              Fun_prop_1 (fun_remove f x).
  Proof.
    unfold Fun_prop_1.
    unfold fun_remove.
    intros.
    destruct (beq_name x0 x) eqn:?.
      intro; discriminate.

      apply beq_name_false_iff in Heqb.
      destruct (f x0) eqn:?.
        destruct s.
          destruct (beq_name n x) eqn:?.
            intro; discriminate.

            specialize (H x0).
            rewrite Heqo in H.
            auto.
          intro; discriminate.
          intro; discriminate.
        intro; discriminate.
  Qed.

  Lemma fun_remove_prop_2 : forall f n,
                              Fun_prop_2 f ->
                              Fun_prop_2 (fun_remove f n).
  Proof.
    unfold Fun_prop_2.
    unfold fun_remove.
    intros.
    destruct (beq_name x n) eqn:?.
      inversion H0; discriminate.

      destruct (beq_name y n) eqn:?.
        inversion H1; discriminate.

        destruct (f x) eqn:?.
          destruct s.
            destruct (beq_name n0 n) eqn:?.
              inversion H0; discriminate.

              destruct (f y) eqn:?.
                destruct s.
                  destruct (beq_name n1 n) eqn:?.
                    inversion H1; discriminate.

                    inversion H2.
                    apply H.
                      exists n0; auto.

                      exists n1; auto.

                      rewrite Heqo.
                      rewrite Heqo0.
                      rewrite H4; auto.
                  discriminate.

                  discriminate.
                discriminate.
            inversion H0; discriminate.

            inversion H0; discriminate.
          inversion H0; discriminate.
  Qed.

  Lemma fun_remove_prop_3 : forall f n,
                              Fun_prop_3 f ->
                              Fun_prop_3 (fun_remove f n).
  Proof.
    unfold Fun_prop_3.
    unfold fun_remove, fun_join, in_domain, to_star_function.
    intros.
    assert (forall o, (exists (x : Type), o = Some x) -> o <> None).
      intros.
      inversion H1.
      rewrite H2; intro; discriminate.
    destruct (beq_name x n) eqn:?.
      contradict H0; auto.

      destruct (f x) eqn:?.
        destruct s.
          destruct (beq_name n0 n) eqn:?.
            auto.

            rewrite Heqb0.
            rewrite <- Heqo in H0.
            apply H in H0.
            rewrite Heqo in H0.
            rewrite H0.
            auto.
          auto.
          auto.
        contradiction H0; auto.
  Qed.
End Fun.
