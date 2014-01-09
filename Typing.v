Require Import Coq.Logic.FunctionalExtensionality Coq.Arith.EqNat Coq.MSets.MSets Coq.Vectors.Vector Names Sets Fun Config.

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
