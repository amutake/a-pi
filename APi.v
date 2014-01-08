Require Import Coq.Logic.FunctionalExtensionality Coq.Arith.EqNat Coq.MSets.MSets Names Sets Fun.

Inductive config : Set :=
  | nil : config
  | create : name -> name -> config -> config
  | send : name -> name -> config
  | restrict : name -> config -> config
  | compose : config -> config -> config.

Reserved Notation "ns ';' f '|-' p" (at level 40).

Inductive typing : NameSets.t -> Fun.temp_name_mapping -> config -> Prop :=
  | NIL : NameSets.empty ; Fun.empty |- nil
  | MSG : forall x y, NameSets.empty ; Fun.empty |- send x y
  | ACT_empty : forall p x y, (* x /= y? *)
                  NameSets.empty ; Fun.empty |- p ->
                  NameSets.singleton x ; Fun.ch_singleton x |- create x y p
  | ACT_x : forall p x y,
              NameSets.singleton x ; Fun.ch_singleton x |- p ->
              x <> y ->
              NameSets.singleton x ; Fun.ch_singleton x |- create x y p
  | ACT_z : forall p x y z,
              NameSets.singleton z ; Fun.ch_singleton z |- p ->
              x <> z ->
              y <> z ->
              NameSets.add x (NameSets.singleton z) ; Fun.ch_two x z |- create x y p
  | ACT_xz : forall p x y z,
               NameSets.add x (NameSets.singleton z) ; Fun.ch_two x z |- p ->
               x <> z ->
               x <> y ->
               y <> z ->
               NameSets.add x (NameSets.singleton z) ; Fun.ch_two x z |- create x y p
  | COMP : forall ns1 ns2 f1 f2 p1 p2,
             ns1 ; f1 |- p1 ->
             ns2 ; f2 |- p2 ->
             NameSets.Empty (NameSets.inter ns1 ns2) ->
             NameSets.union ns1 ns2 ; Fun.fun_plus f1 f2 |- compose p1 p2
  | RES : forall ns f p x,
            ns ; f |- p ->
            NameSets.remove x ns ; Fun.fun_remove f x |- restrict x p
  where "ns ';' f '|-' p" := (typing ns f p).

Hint Constructors typing.

Goal exists (ns : NameSets.t) (f : Fun.temp_name_mapping), ns ; f |- create (name_cons 0) (name_cons 1) nil.
Proof.
  exists (NameSets.singleton (name_cons 0)).
  exists (fun x => match x with
                     | name_cons 0 => Some star_bottom
                     | _ => None
                   end).

  replace (fun x : name => match x with
                             | name_cons 0 => Some star_bottom
                             | name_cons (S _) => None
                           end)
          with (Fun.ch_singleton (name_cons 0)).
  eapply ACT_empty.
  apply NIL.
  apply functional_extensionality.
  intro.
  unfold Fun.ch_singleton.
  compute.
  destruct x.
  induction n.
    auto.
    auto.
Qed.

Goal forall (ns : NameSets.t) (f : Fun.temp_name_mapping),
       ~ ns ; f |- compose (create (name_cons 0) (name_cons 1) nil) (create (name_cons 0) (name_cons 2) nil).
Proof.
  unfold not.
  intros.
  assert (forall x, ~ NameSets.Empty (NameSets.singleton x)).
    unfold NameSets.Empty, not; intros.
    apply H0 with x.
    apply NameSets.F.singleton_2; auto.
    destruct x; auto.
  inversion H; subst.
  inversion H3; subst.
    inversion H6; subst.
      apply inter_not_empty in H7; auto.

      apply inter_not_empty in H7; auto.

      inversion H10.

      inversion H8.
      symmetry in H4; apply Fun.ch_two_not_empty in H4; auto.
    inversion H6; subst.
      apply inter_not_empty in H7; auto.

      apply inter_not_empty in H7; auto.

      inversion H11.

      inversion H5.
      symmetry in H4; apply Fun.ch_two_not_empty in H4; auto.
    inversion H6; subst.
      inversion H9.

      inversion H9.

      inversion H9.

      inversion H9.
    inversion H6; subst.
      inversion H5.
      symmetry in H4; apply Fun.ch_two_not_empty in H4; auto.

      inversion H5.
      symmetry in H4; apply Fun.ch_two_not_empty in H4; auto.

      inversion H5.
      symmetry in H4; apply Fun.ch_two_not_empty in H4; auto.

      inversion H5.
      symmetry in H4; apply Fun.ch_two_not_empty in H4; auto.
Qed.

Lemma typing_domain_1 : forall ns f p (ty : ns ; f |- p) x,
                        Fun.domain f x ->
                        NameSets.mem x ns = true.
Proof.
  intros.
  induction ty.
    unfold Fun.domain in H.
    compute in H.
    auto.

    unfold Fun.domain in H.
    compute in H.
    auto.

    apply Fun.ch_singleton_domain in H.
    rewrite H.
    apply NameSets.EP.singleton_mem_1.

    apply Fun.ch_singleton_domain in H.
    rewrite H.
    apply NameSets.EP.singleton_mem_1.

    apply Fun.ch_two_domain in H.
    inversion H.
      rewrite H2.
      apply NameSets.EP.add_mem_1.

      rewrite <- H2.
      erewrite NameSets.EP.add_mem_2.
        apply NameSets.EP.singleton_mem_1.
        destruct x0, z.
        intro.
        apply H0.
        rewrite H3; auto.

    apply Fun.ch_two_domain in H.
    inversion H.
      rewrite H3.
      apply NameSets.EP.add_mem_1.
      rewrite <- H3.
      erewrite NameSets.EP.add_mem_2.
        apply NameSets.EP.singleton_mem_1.
        destruct x0, z.
        intro.
        apply H0.
        rewrite H4; auto.

    apply Fun.fun_plus_domain in H.
    apply NameSets.F.mem_iff.
    apply mem_union.
    inversion H.
      apply IHty1 in H1.
      apply NameSets.F.mem_iff in H1.
      left; apply H1.

      apply IHty2 in H1.
      apply NameSets.F.mem_iff in H1.
      right; apply H1.

    apply Fun.fun_remove_domain_2 in H.
    inversion_clear H.
    apply IHty in H1.
    rewrite NameSets.EP.remove_mem_2.
      auto.
      destruct x0, x.
      intro.
      apply H0.
      rewrite H.
      auto.
Qed.

Lemma typing_domain_2 : forall ns f p (ty : ns ; f |- p) x,
                        NameSets.mem x ns = true ->
                        Fun.domain f x.
Proof.
  intros.

  assert (forall P : Prop, P -> ~~P).
    intro.
    intro.
    intro.
    apply H1.
    auto.

  unfold Fun.domain.
  intro.
  induction ty.
    rewrite NameSets.EP.empty_mem in H.
    discriminate.

    rewrite NameSets.EP.empty_mem in H.
    discriminate.

    unfold Fun.ch_singleton in H1.
    destruct (beq_name x0 x) eqn:?.
      discriminate.
      apply beq_name_false_iff in Heqb.
      apply Heqb.
      apply NameSets.EP.singleton_mem_3 in H.
      destruct x0, x.
      auto.

    unfold Fun.ch_singleton in H1.
    destruct (beq_name x0 x) eqn:?.
      discriminate.
      apply beq_name_false_iff in Heqb.
      apply Heqb.
      apply NameSets.EP.singleton_mem_3 in H.
      destruct x0, x.
      auto.

    unfold Fun.ch_two in H1.
    destruct (beq_name x0 x) eqn:?.
      discriminate.
      destruct (beq_name z x) eqn:?.
        discriminate.
        apply beq_name_false_iff in Heqb.
        apply beq_name_false_iff in Heqb0.
        rewrite NameSets.EP.add_mem_2 in H.
          apply NameSets.EP.singleton_mem_3 in H.
          destruct z, x, x0.
          rewrite H in Heqb0.
          auto.

          destruct x, x0.
          intro.
          rewrite H4 in Heqb.
          auto.

    unfold Fun.ch_two in H1.
    destruct (beq_name x0 x) eqn:?.
      discriminate.
      destruct (beq_name z x) eqn:?.
        discriminate.
        apply beq_name_false_iff in Heqb.
        apply beq_name_false_iff in Heqb0.
        rewrite NameSets.EP.add_mem_2 in H.
          apply NameSets.EP.singleton_mem_3 in H.
          destruct z, x, x0.
          rewrite H in Heqb0.
          auto.

          destruct x, x0.
          intro.
          rewrite H5 in Heqb.
          auto.

    rewrite NameSets.EP.union_mem in H.
    apply orb_true_iff in H.
    inversion H.
      apply IHty1 in H3.
        auto.
        apply H0 in H1.
        apply Fun.fun_plus_not_domain in H1.
        inversion H1.
        unfold Fun.domain in H4.
        destruct (f1 x).
          exfalso; apply H4; intro; discriminate.
          auto.
      apply IHty2 in H3.
        auto.
        apply H0 in H1.
        apply Fun.fun_plus_not_domain in H1.
        inversion H1.
        unfold Fun.domain in H5.
        destruct (f2 x).
          exfalso; apply H5; intro; discriminate.
          auto.

    apply H0 in H1.
    apply Fun.fun_remove_not_domain_2 in H1.
    inversion H1.
    rewrite <- H2 in H.
    rewrite NameSets.EP.remove_mem_1 in H.
    discriminate.
    apply NameSets.EP.remove_mem_3 in H.
    apply IHty in H.
      auto.
      unfold Fun.domain in H2.
      destruct (f x).
        exfalso; apply H2; intro; discriminate.
        auto.
Qed.

Lemma typing_range_domain : forall ns f p (ty : ns ; f |- p), Fun.range_domain f.
Proof.
  intros.
  induction ty.
    apply Fun.ch_empty_range_domain.

    apply Fun.ch_empty_range_domain.

    apply Fun.ch_singleton_range_domain.

    apply Fun.ch_singleton_range_domain.

    apply Fun.ch_two_range_domain; auto.

    apply Fun.ch_two_range_domain; auto.

    apply Fun.fun_plus_range_domain; auto.

    apply Fun.fun_remove_range_domain; auto.
Qed.

Inductive ConfigName (x : name) : config -> Prop :=
  | send_name_1 : forall y, ConfigName x (send x y)
  | send_name_2 : forall y, ConfigName x (send y x)
  | create_name_1 : forall y p, ConfigName x (create x y p)
  | create_name_2 : forall y p, ConfigName x (create y x p)
  | create_name_p : forall y z p, ConfigName x p -> ConfigName x (create y z p)
  | compose_name_l : forall pl pr, ConfigName x pl -> ConfigName x (compose pl pr)
  | compose_name_r : forall pl pr, ConfigName x pr -> ConfigName x (compose pl pr)
  | restrict_name : forall p, ConfigName x (restrict x p)
  | restrict_name_p : forall y p, ConfigName x p -> ConfigName x (restrict y p).

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
                                     ConfigBoundedName x (restrict y p).

Hint Constructors ConfigBoundedName.

Inductive ConfigFreeName (x : name) : config -> Prop :=
  | send_free_1 : forall y, ConfigFreeName x (send x y)
  | send_free_2 : forall y, ConfigFreeName x (send y x)
  | create_free : forall y p, ConfigFreeName x (create x y p)
  | create_free_p : forall y z p, ConfigFreeName x p -> x <> z -> ConfigFreeName x (create y z p)
  | compose_free_l : forall pl pr, ConfigFreeName x pl -> ConfigFreeName x (compose pl pr)
  | compose_free_r : forall pl pr, ConfigFreeName x pr -> ConfigFreeName x (compose pl pr)
  | restrict_free : forall r p, ConfigFreeName x p -> x <> r -> ConfigFreeName x (restrict r p).

Hint Constructors ConfigFreeName.

Lemma config_name_dec : forall x p, {ConfigName x p} + {~ ConfigName x p}.
Proof.
  intros.
  induction p.
    right; intro.
    inversion H.

    inversion IHp.
      left; auto.

      destruct (name_dec x n).
        rewrite e; left; auto.

        destruct (name_dec x n0).
          rewrite e; left; auto.

          right; intro.
          inversion H0; auto.

    destruct (name_dec x n).
      rewrite e; left; auto.

      destruct (name_dec x n0).
        rewrite e; left; auto.

        right; intro.
        inversion H; auto.

    destruct (name_dec x n).
      rewrite e; left; auto.

      inversion IHp.
        left; auto.

        right; intro.
        inversion H0; auto.

    inversion IHp1; inversion IHp2.
      left; auto.

      left; auto.

      left; auto.

      right; intro.
      inversion H1; auto.
Qed.

Lemma config_free_dec : forall x p, {ConfigFreeName x p} + {~ ConfigFreeName x p}.
Proof.
  intros.
  induction p.
    right; intro; inversion H.

    destruct (name_dec x n).
      rewrite e; left; auto.
      destruct (name_dec x n0).
        rewrite e; right; intro; inversion H; subst; auto.
        inversion IHp.
          left; auto.
          right; intro; inversion H0; subst; auto.

    destruct (name_dec x n); destruct (name_dec x n0).
      rewrite e; auto.
      rewrite e; auto.
      rewrite e; auto.
      right; intro; inversion H; subst; auto.

    destruct (name_dec x n).
      rewrite e; right; intro; inversion H; subst; auto.
      inversion IHp.
        left; auto.
        right; intro; inversion H0; subst; auto.

    inversion_clear IHp1; inversion_clear IHp2.
      left; auto.
      left; auto.
      left; auto.
      right; intro; inversion H1; subst; auto.
Qed.

Lemma config_bounded_prop : forall x p, ConfigBoundedName x p -> ConfigName x p.
Proof.
  intros.
  induction p; inversion H; subst; auto.
Qed.

Lemma config_free_prop : forall x p, ConfigFreeName x p -> ConfigName x p.
Proof.
  intros.
  induction p; inversion H; subst; auto.
Qed.

Lemma config_name_prop : forall x p, ConfigName x p ->
                                     (ConfigBoundedName x p <-> ~ ConfigFreeName x p) /\
                                     (ConfigFreeName x p <-> ~ ConfigBoundedName x p).
Proof.
  intros.
  induction p.
    inversion H.

    inversion H; subst.
      split; split; intros; try intro.
        inversion H0; subst; auto.

        absurd (ConfigFreeName n (create n n0 p)); auto.

        inversion H1; subst; auto.

        auto.

      split; split; intros; try intro.
        inversion H0; subst; inversion H1; subst; auto.

        apply create_bounded.
        intro; subst; apply H0; auto.

        inversion H0; subst; inversion H1; subst; auto.

        assert (n <> n0 -> False).
          intro.
          apply H0.
          auto.
        apply eq_name_double_neg in H1.
        rewrite H1; auto.

      apply IHp in H1.
      inversion_clear H1.
      split; split; intros; try intro.
        inversion H1; subst; inversion H3; subst; auto.
        apply H0 in H6; auto.

        assert (x <> n).
          intro; apply H1.
          rewrite H3; auto.
        destruct (beq_name x n0) eqn:?.
          apply beq_name_true_iff in Heqb.
          rewrite <- Heqb.
          apply create_bounded; auto.

          apply beq_name_false_iff in Heqb.
          apply create_bounded_p.
            apply H0.
            intro.
            apply H1.
            apply create_free_p; auto.

            auto.

        inversion H1; subst; inversion H3; subst; auto.
        apply H0 in H6; auto.

        destruct (beq_name x n) eqn:?.
          apply beq_name_true_iff in Heqb.
          rewrite Heqb; auto.

          apply beq_name_false_iff in Heqb.
          assert (x <> n0).
            intro.
            rewrite <- H3 in H1.
            apply H1.
            auto.
          apply create_free_p; auto.
          apply H2.
          intro.
          apply H1.
          auto.

    inversion_clear H; subst.
      split; split; intros; try intro.
        inversion H.

        exfalso; apply H; auto.

        inversion H0.

        auto.
      split; split; intros; try intro.
        inversion H.

        exfalso; apply H; auto.

        inversion H0.

        auto.

    inversion_clear H; subst.
      split; split; intros; try intro.
        inversion H0; auto.

        auto.

        inversion H; auto.

        exfalso; apply H; auto.
      apply IHp in H0.
      clear IHp.
      inversion_clear H0.
      split; split; intros; try intro.
        inversion H0; subst; inversion H2; subst; auto.
        apply H in H4; auto.

        destruct (beq_name x n) eqn:?.
          apply beq_name_true_iff in Heqb.
          rewrite Heqb; auto.

          apply beq_name_false_iff in Heqb.
          apply restrict_bounded_p.
          apply H; intro.
          apply H0; apply restrict_free; auto.

        inversion H0; subst; inversion H2; subst; auto.
        apply H in H4; auto.

        destruct (beq_name x n) eqn:?.
          apply beq_name_true_iff in Heqb.
          rewrite Heqb in H0.
          exfalso; apply H0; auto.

          apply beq_name_false_iff in Heqb.
          apply restrict_free; auto.
          apply H1.
          intro.
          apply H0; auto.

    inversion_clear H; subst.
      assert (ConfigName x p1); auto.
      apply IHp1 in H0.
      inversion_clear H0.
      split; split; intros; try intro.
        inversion_clear H0; subst; inversion_clear H3; subst; auto.
          apply H1 in H4; auto.

          assert (ConfigBoundedName x p2); auto.
          apply config_bounded_prop in H3.
          apply IHp2 in H3.
          inversion_clear H3.
          apply H6 in H5; auto.

          apply H1 in H0; auto.

          apply config_free_prop in H0; auto.

        assert (~ ConfigFreeName x p1 /\ ~ ConfigFreeName x p2).
          split.
            intro; apply H0; auto.
            intro; apply H0; auto.
        inversion_clear H3.
        apply H1 in H4.
        destruct (config_name_dec x p2).
          apply IHp2 in c.
          inversion_clear c.
          apply H3 in H5.
          auto.

          auto.

        inversion H0; subst; inversion H3; subst; auto.
          apply H1 in H7; auto.

          apply H1 in H7; auto.

          assert (ConfigBoundedName x p2); auto.
          apply config_bounded_prop in H4; apply IHp2 in H4.
          inversion_clear H4.
          apply H6 in H8; auto.

          apply config_free_prop in H5; auto.

        destruct (config_name_dec x p2).
          apply IHp2 in c.
          inversion_clear c.
          destruct (config_free_dec x p1); auto.
          destruct (config_free_dec x p2); auto.
          apply H1 in n.
          apply H3 in n0.
          exfalso; apply H0; auto.

          apply compose_free_l.
          apply H2.
          intro.
          apply H0.
          auto.

      assert (ConfigName x p2); auto.
      apply IHp2 in H0.
      inversion_clear H0.
      clear IHp2.
      split; split; intros; try intro.
        inversion H0; subst; inversion H3; subst; auto.
          assert (ConfigBoundedName x p1); auto.
          apply config_bounded_prop in H4.
          apply IHp1 in H4.
          inversion_clear H4.
          apply H8 in H6; auto.

          apply H1 in H7; auto.

          apply config_free_prop in H5; auto.

          apply H1 in H5; auto.

        assert (~ ConfigFreeName x p1 /\ ~ ConfigFreeName x p2).
          split.
            intro; apply H0; auto.
            intro; apply H0; auto.
        inversion_clear H3.
        apply H1 in H5.
        destruct (config_name_dec x p1).
          apply IHp1 in c; inversion_clear c.
          apply H3 in H4.
          auto.

          auto.

        inversion H0; subst; inversion H3; subst; auto.
          assert (ConfigBoundedName x p1); auto.
          apply config_bounded_prop in H4; apply IHp1 in H4; inversion_clear H4.
          apply H6 in H7; auto.

          apply config_free_prop in H5; auto.

          apply H1 in H8; auto.

          apply H1 in H7; auto.

        destruct (config_free_dec x p1); auto.
        destruct (config_free_dec x p2); auto.
        destruct (config_name_dec x p1).
          apply IHp1 in c; inversion_clear c.
          apply H3 in n.
          apply H1 in n0.
          exfalso; apply H0; auto.

          apply compose_free_r.
          apply H2.
          intro.
          apply H0.
          auto.
Qed.

Definition ConfigSubset {ns} {f} {p} (ty : ns ; f |- p) : Prop :=
  NameSets.For_all (fun x => ConfigFreeName x p) ns.

Lemma config_subset : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), ConfigSubset ty.
Proof.
  intros.
  unfold ConfigSubset.
  unfold NameSets.For_all.
  induction ty; intros.
    apply NameSets.F.empty_iff in H; easy.

    apply NameSets.F.empty_iff in H; easy.

    apply NameSets.P.singleton_equal_add in H.
    apply add_in in H.
    inversion H.
      rewrite H0; auto.

      apply NameSets.F.empty_iff in H0; easy.

    apply NameSets.P.singleton_equal_add in H0.
    apply add_in in H0.
    inversion H0.
      rewrite H1; auto.

      apply NameSets.F.empty_iff in H1; easy.

    apply add_in in H1.
    inversion H1.
      rewrite H2; auto.

      assert (x0 = z).
        apply NameSets.P.singleton_equal_add in H2.
        apply add_in in H2.
        inversion H2.
          auto.
          apply NameSets.F.empty_iff in H3; easy.
      apply IHty in H2.
      apply create_free_p.
        auto.

        rewrite H3.
        intro.
        rewrite H4 in H0; auto.

    assert (ConfigFreeName x0 p).
      apply (IHty x0 H2).
    apply add_in in H2.
    inversion_clear H2.
      rewrite H4; auto.

      assert (x0 = z).
        apply NameSets.P.singleton_equal_add in H4.
        apply add_in in H4.
        inversion H4.
          auto.
          apply NameSets.F.empty_iff in H2; easy.
      apply create_free_p.
      auto.
      intro.
      rewrite <- H2 in H1.
      rewrite <- H5 in H1.
      apply H1; auto.

    apply NameSets.F.union_1 in H0.
    inversion_clear H0.
      apply compose_free_l.
      apply IHty1.
      auto.

      apply compose_free_r.
      apply IHty2.
      auto.

    apply remove_in in H.
    inversion H.
    apply restrict_free.
      apply IHty in H1.
      auto.
      auto.
Qed.

Definition FunctionProperty {ns : NameSets.t} {f : Fun.temp_name_mapping} {p : config} (ty : ns ; f |- p) : Prop :=
  Fun.Fun_prop f.

Lemma function_property_1 : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), Fun.Fun_prop_1 f.
Proof.
  intros.
  induction ty.
    apply Fun.ch_empty_prop_1.

    apply Fun.ch_empty_prop_1.

    apply Fun.ch_singleton_prop_1.

    apply Fun.ch_singleton_prop_1.

    apply Fun.ch_two_prop_1; auto.

    apply Fun.ch_two_prop_1; auto.

    apply Fun.fun_plus_prop_1; auto.

    apply Fun.fun_remove_prop_1; auto.
Qed.

Lemma fun_exclusive : forall ns1 ns2 f1 f2 p1 p2
                             (ty1 : ns1 ; f1 |- p1) (ty2 : ns2 ; f2 |- p2),
                        NameSets.Empty (NameSets.inter ns1 ns2) ->
                        (forall x,
                           (Fun.domain f1 x -> ~ Fun.domain f2 x) /\
                           (Fun.domain f2 x -> ~ Fun.domain f1 x)).
Proof.
  intros.
  eapply inter_empty in H.
  inversion_clear H.
  split; intros; intro.
    apply typing_domain_1 with (x := x) in ty1.
      apply NameSets.F.mem_iff in ty1.
      apply typing_domain_1 with (x := x) in ty2.
        apply NameSets.F.mem_iff in ty2.
        apply H0 in ty1.
        apply ty1; auto.

        auto.
      auto.
    apply typing_domain_1 with (x := x) in ty1.
      apply NameSets.F.mem_iff in ty1.
      apply typing_domain_1 with (x := x) in ty2.
        apply NameSets.F.mem_iff in ty2.
        apply H0 in ty1.
        apply ty1; auto.

        auto.
      auto.
Qed.

Lemma function_property_2 : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), Fun.Fun_prop_2 f.
Proof.
  intros.
  induction ty.
    apply Fun.ch_empty_prop_2.

    apply Fun.ch_empty_prop_2.

    apply Fun.ch_singleton_prop_2.

    apply Fun.ch_singleton_prop_2.

    apply Fun.ch_two_prop_2.

    apply Fun.ch_two_prop_2.

    apply Fun.fun_plus_prop_2; auto.
      eapply typing_range_domain; apply ty1.
      eapply typing_range_domain; apply ty2.
      intros.
      eapply fun_exclusive with
      (ns1 := ns1) (ns2 := ns2) (f1 := f1) (f2 := f2) (p1 := p1) (p2 := p2) (x := x)
        in H; auto.

    apply Fun.fun_remove_prop_2; auto.
Qed.

Lemma function_property_3 : forall ns f p (ty : ns ; f |- p), Fun.Fun_prop_3 f.
Proof.
  intros.
  induction ty.
    apply Fun.ch_empty_prop_3.

    apply Fun.ch_empty_prop_3.

    apply Fun.ch_singleton_prop_3.

    apply Fun.ch_singleton_prop_3.

    apply Fun.ch_two_prop_3; auto.

    apply Fun.ch_two_prop_3; auto.

    apply Fun.fun_plus_prop_3; auto.
      intros.
      eapply fun_exclusive with (x := x) in H.
        apply H.
        apply ty1.
        apply ty2.

    apply Fun.fun_remove_prop_3; auto.
Qed.

Lemma function_property : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), FunctionProperty ty.
Proof.
  unfold FunctionProperty.
  unfold Fun.Fun_prop.
  intros.
  split; try split.
  eapply function_property_1.
  apply ty.
  eapply function_property_2.
  apply ty.
  eapply function_property_3.
  apply ty.
Qed.

Definition Uniqueness {ns} {f} {p} (ty : ns ; f |- p) : Prop :=
  forall (ns' : NameSets.t) (f' : Fun.temp_name_mapping),
    ns' ; f' |- p -> NameSets.Equal ns ns' /\ f = f'.

Lemma uniqueness : forall ns f p (ty : ns ; f |- p), Uniqueness ty.
Proof.
  unfold Uniqueness.
  intros.
  split.
  (* Equal ns ns' *)
  generalize dependent ns'.
  generalize dependent f'.
  induction ty; intros.
    inversion H; auto.

    inversion H; auto.

    inversion H; subst; auto.
      apply IHty in H5.
      setoid_rewrite <- H5.
      setoid_rewrite <- NameSets.P.singleton_equal_add.
      auto.

      apply IHty in H3.
      symmetry in H3.
      apply NameSets.P.empty_is_empty_2 in H3.
      apply add_not_empty in H3.
      easy.

    inversion H0; subst; auto.
      apply IHty in H6.
      setoid_rewrite <- H6.
      setoid_rewrite NameSets.P.singleton_equal_add.
      setoid_rewrite add_join.
      auto.

      apply IHty in H4.
      auto.

    inversion H1; subst.
      apply IHty in H5.
      setoid_rewrite H5.
      setoid_rewrite NameSets.P.singleton_equal_add.
      auto.

      apply IHty in H6.
      setoid_rewrite H6.
      setoid_rewrite NameSets.P.singleton_equal_add.
      setoid_rewrite add_join.
      auto.

      apply IHty in H7.
      setoid_rewrite H7.
      auto.

      apply IHty in H5.
      setoid_rewrite H5.
      setoid_rewrite add_join.
      auto.

    inversion H2; subst; auto.
      apply IHty in H6.
      apply NameSets.P.empty_is_empty_2 in H6.
      apply add_not_empty in H6.
      easy.

      apply IHty in H7.
      setoid_rewrite H7.
      auto.

      apply IHty in H8.
      setoid_rewrite <- H8.
      setoid_rewrite add_join.
      auto.

      apply IHty in H6.
      setoid_rewrite H6.
      auto.

    inversion H0; subst; auto.
      apply IHty1 in H3.
      apply IHty2 in H6.
      setoid_rewrite H3.
      setoid_rewrite H6.
      auto.

    inversion H; subst; auto.
      apply IHty in H3.
      setoid_rewrite H3.
      auto.

  (* f = f' *)
  generalize dependent ns'.
  generalize dependent f'.
  induction ty; intros.
    inversion H; auto.

    inversion H; auto.

    inversion H; subst; auto.
      apply IHty in H5.
      symmetry in H5.
      apply Fun.ch_singleton_not_empty in H5.
      easy.

      apply IHty in H3.
      symmetry in H3.
      apply Fun.ch_two_not_empty in H3.
      easy.

    inversion H0; subst; auto.
      apply IHty in H6.
      apply Fun.ch_singleton_equal in H6.
      easy.

      apply IHty in H4.
      auto.

    inversion H1; subst; auto.
      apply IHty in H5.
      apply Fun.ch_singleton_not_empty in H5.
      easy.

      apply IHty in H6.
      apply Fun.ch_singleton_equal in H6.
      rewrite H6 in H.
      exfalso; apply H; auto.

      apply IHty in H7.
      apply Fun.ch_singleton_equal in H7.
      rewrite H7.
      auto.

      apply IHty in H5.
      apply equal_f with x in H5.
      unfold Fun.ch_singleton in H5.
      unfold Fun.ch_two in H5.
      rewrite beq_name_refl in H5.
      apply beq_name_false_iff in H.
      rewrite beq_name_sym in H.
      rewrite H in H5.
      discriminate.

    inversion H2; subst; auto.
      apply IHty in H6.
      apply Fun.ch_two_not_empty in H6; easy.

      apply IHty in H7.
      auto.

      apply IHty in H8.
      apply equal_f with x in H8.
      unfold Fun.ch_singleton in H8.
      unfold Fun.ch_two in H8.
      rewrite beq_name_refl in H8.
      apply beq_name_false_iff in H9.
      rewrite beq_name_sym in H9.
      rewrite H9 in H8.
      discriminate.

      apply IHty in H6.
      auto.

    inversion H0; subst; auto.
      apply IHty1 in H3.
      apply IHty2 in H6.
      rewrite H3.
      rewrite H6.
      auto.

    inversion H; subst; auto.
      apply IHty in H3.
      rewrite H3.
      auto.
Qed.

Theorem Soundness : forall ns f p (ty : ns ; f |- p),
                      ConfigSubset ty /\ FunctionProperty ty /\ Uniqueness ty.
Proof.
  intros.
  split.
  apply config_subset.
  split.
  apply function_property.
  apply uniqueness.
Qed.
