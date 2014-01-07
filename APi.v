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
  | MSG : forall x y : name, NameSets.empty ; Fun.empty |- send x y
  | ACT_empty : forall (p : config) (x y : name), (* x /= y? *)
                  NameSets.empty ; Fun.empty |- p ->
                  NameSets.singleton x ; Fun.ch_singleton x |- create x y p
  | ACT_x : forall (f : Fun.temp_name_mapping) (p : config) (x y : name),
              NameSets.singleton x ; Fun.ch_singleton x |- p ->
              x <> y ->
              NameSets.singleton x ; Fun.ch_singleton x |- create x y p
  | ACT_z : forall (f : Fun.temp_name_mapping) (p : config) (x y z : name),
              NameSets.singleton z ; Fun.ch_singleton z |- p ->
              x <> z ->
              y <> z ->
              NameSets.add x (NameSets.singleton z) ; Fun.ch_two x z |- create x y p
  | ACT_xz : forall (f : Fun.temp_name_mapping) (p : config) (x y z : name),
               NameSets.add x (NameSets.singleton z) ; Fun.ch_two x z |- p ->
               x <> z ->
               x <> y ->
               y <> z ->
               NameSets.add x (NameSets.singleton z) ; Fun.ch_two x z |- create x y p
  | COMP : forall (ns1 ns2 : NameSets.t) (f1 : Fun.temp_name_mapping) (f2 : Fun.temp_name_mapping) (p1 p2 : config),
             ns1 ; f1 |- p1 ->
             ns2 ; f2 |- p2 ->
             NameSets.Empty (NameSets.inter ns1 ns2) ->
             NameSets.union ns1 ns2 ; Fun.fun_plus f1 f2 |- compose p1 p2
  | RES : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (x : name),
            ns ; f |- p ->
            NameSets.remove x ns ; Fun.fun_remove f x |- restrict x p
  where "ns ';' f '|-' p" := (typing ns f p).

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
  inversion H; subst.
  inversion H2; subst.
    inversion H5; subst.
      apply NameSets.F.is_empty_iff in H6.
      compute in H6; discriminate.
      apply NameSets.F.is_empty_iff in H6.
      compute in H6; discriminate.
      destruct z; induction n; apply NameSets.F.is_empty_iff in H6; compute in H6; discriminate.
      destruct z; induction n; apply NameSets.F.is_empty_iff in H6; compute in H6; discriminate.
    inversion H5; subst.
      apply NameSets.F.is_empty_iff in H6.
      compute in H6; discriminate.
      apply NameSets.F.is_empty_iff in H6.
      compute in H6; discriminate.
      destruct z; induction n; apply NameSets.F.is_empty_iff in H6; compute in H6; discriminate.
      destruct z; induction n; apply NameSets.F.is_empty_iff in H6; compute in H6; discriminate.
    inversion H5; subst; inversion H8; subst.
    inversion H5; subst; inversion H4; apply equal_f with (name_cons 0) in H3; compute in H3; discriminate.
Qed.

Goal exists (ns : NameSets.t) (f : Fun.temp_name_mapping), ns ; f |- compose (create (name_cons 0) (name_cons 1) nil) (create (name_cons 2) (name_cons 3) nil).
Proof.
  exists (NameSets.add (name_cons 0) (NameSets.singleton (name_cons 2))).
  exists (fun x : name => match x with
                            | name_cons 0 => Some star_bottom
                            | name_cons 2 => Some star_bottom
                            | _ => None
                          end).
  replace (NameSets.add (name_cons 0) (NameSets.singleton (name_cons 2)))
  with (NameSets.union (NameSets.singleton (name_cons 0)) (NameSets.singleton (name_cons 2))).

  replace (fun x : name =>
             match x with
               | name_cons 0 => Some star_bottom
               | name_cons 1 => None
               | name_cons 2 => Some star_bottom
               | name_cons (S (S (S _))) => None
             end)
  with (Fun.fun_plus (fun x => match x with
                                 | name_cons 0 => Some star_bottom
                                 | _ => None
                               end)
                     (fun x => match x with
                                 | name_cons 2 => Some star_bottom
                                 | _ => None
                               end)).

  eapply COMP.
    replace (fun x => match x with
                      | name_cons 0 => Some star_bottom
                      | _ => None
                    end)
    with (Fun.ch_singleton (name_cons 0)).
    eapply ACT_empty.
    apply NIL.

    unfold Fun.ch_singleton.
    apply functional_extensionality.
    destruct x.
    destruct (beq_name (name_cons 0) (name_cons n)) eqn:?.
      apply beq_name_true_iff in Heqb.
      apply name_cons_prop in Heqb.
      rewrite <- Heqb.
      auto.

      destruct n eqn:?.
        simpl in Heqb.
        discriminate.

        auto.

    replace (fun x => match x with
                        | name_cons 0 => None
                        | name_cons 1 => None
                        | name_cons 2 => Some star_bottom
                        | _ => None
                      end)
    with (Fun.ch_singleton (name_cons 2)).
    eapply ACT_empty.
    apply NIL.

    unfold Fun.ch_singleton.
    apply functional_extensionality.
    destruct x.
    destruct (beq_name (name_cons 2) (name_cons n)) eqn:?.
      apply beq_name_true_iff in Heqb.
      apply name_cons_prop in Heqb.
      rewrite <- Heqb.
      auto.

      apply beq_name_false_iff in Heqb.
      destruct n.
        auto.
        destruct n.
          auto.
          destruct n.
          exfalso; apply Heqb; auto.
          auto.
  apply NameSets.F.is_empty_iff.
  compute.
  auto.

  unfold Fun.fun_plus.
  apply functional_extensionality.
  intro.
  destruct x.
  destruct n.
    auto.
    auto.

  (* setoid_rewrite NameSets.P.add_union_singleton. TODO *)
Admitted.

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

Fixpoint config_names (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create n1 n2 c' => NameSets.add n1 (NameSets.add n2 (config_names c'))
    | send n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | restrict n c' => NameSets.add n (config_names c')
    | compose c1 c2 => NameSets.union (config_names c1) (config_names c2)
  end.

Fixpoint config_bounded_names (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create _ n c' => NameSets.add n (config_bounded_names c')
    | send _ _ => NameSets.empty
    | restrict n c' => NameSets.add n (config_bounded_names c')
    | compose c1 c2 => NameSets.union (config_bounded_names c1) (config_bounded_names c2)
  end.

Definition config_free_names (c : config) : NameSets.t :=
  NameSets.diff (config_names c) (config_bounded_names c).

Goal forall x y : name, NameSets.Equal (config_free_names (send x y)) (NameSets.add x (NameSets.singleton y)).
Proof.
  intros.
  unfold config_free_names.
  simpl.
  setoid_rewrite NameSets.P.empty_diff_2.
  apply NameSets.P.equal_refl.
  apply NameSets.P.empty_is_empty_2.
  apply NameSets.P.equal_refl.
Qed.

Goal forall (p : config) (x y : name), ~ NameDecidableType.eq x y ->
       NameSets.Equal (config_free_names (create x y p))
                      (NameSets.add x (config_free_names p)).
Proof.
  intros.
  unfold config_free_names.
  induction p.
    simpl.
    setoid_replace (NameSets.diff NameSets.empty NameSets.empty)
    with (NameSets.empty).
    setoid_rewrite <- NameSets.P.singleton_equal_add.
    setoid_rewrite <- NameSets.P.remove_diff_singleton.


    (* compute. *)
    (* auto. *)

    (* unfold config_free_names. *)
    (* simpl. *)
    (* destruct (NameSets.mem n (NameSets.add y NameSets.empty)) eqn:?. *)

    (* unfold config_free_names in IHp. *)
    (* setoid_rewrite <- NameSets.P.singleton_equal_add in Heqb. *)
    (* apply NameSets.EP.singleton_mem_3 in Heqb. *)
    (* destruct y, n. *)
    (* rewrite <- Heqb. *)
    (* simpl in IHp. *)
Admitted.

Inductive FreeName (x : name) : config -> Prop :=
  | send_free_1 : forall y, FreeName x (send x y)
  | send_free_2 : forall y, FreeName x (send y x)
  | create_free : forall y p, FreeName x (create x y p)
  | create_free_p : forall y z p, FreeName x p -> x <> z -> FreeName x (create y z p)
  | compose_free_l : forall pl pr, FreeName x pl -> FreeName x (compose pl pr)
  | compose_free_r : forall pl pr, FreeName x pr -> FreeName x (compose pl pr)
  | restrict_free : forall r p, FreeName x p -> x <> r -> FreeName x (restrict r p).

(* 広い可能性がある これが free name の述語になっていることを証明しないといけない どうやって? *)

Hint Constructors FreeName.

Definition ConfigSubset {ns} {f} {p} (ty : ns ; f |- p) : Prop :=
  NameSets.For_all (fun x => FreeName x p) ns.

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

    assert (FreeName x0 p).
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

Inductive action : Set :=
  | silent : action
  | free_out : name -> name -> action
  | bound_out : name -> name -> action
  | free_inp : name -> name -> action
  | bound_inp : name -> name -> action.

Inductive not_silent : action -> Prop :=
  | not_silent_free_out : forall x y, not_silent (free_out x y)
  | not_silent_bound_out : forall x y, not_silent (bound_out x y)
  | not_silent_free_inp : forall x y, not_silent (free_inp x y)
  | not_silent_bound_inp : forall x y, not_silent (bound_inp x y).

Fixpoint action_names (a : action) : NameSets.t :=
  match a with
    | silent => NameSets.empty
    | free_out n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | bound_out n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | free_inp n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | bound_inp n1 n2 => NameSets.add n1 (NameSets.singleton n2)
  end.

Fixpoint action_bound_names (a : action) : NameSets.t. Admitted.


Definition replace (x y z : name) : name :=
  match NameOrderedType.compare x z with
    | Eq => y
    | _ => z
  end.

Fixpoint replace_names (x y : name) (c : config) : config :=
  match c with
    | nil => nil
    | create n1 n2 c' => create (replace x y n1) (replace x y n2) (replace_names x y c')
    | send n1 n2 => send (replace x y n1) (replace x y n2)
    | restrict n c' => restrict (replace x y n) (replace_names x y c')
    | compose c1 c2 => compose (replace_names x y c1) (replace_names x y c2)
  end.

Reserved Notation "a '/' p '==>' q" (at level 40).

Inductive trans : action -> config -> config -> Prop :=
  | INP : forall (x y z : name) (p : config),
            free_inp x z / create x y p ==> replace_names y z p
  | OUT : forall x y : name,
            free_out x y / send x y ==> nil
  | BINP : forall (x y : name) (p p' : config),
             free_inp x y / p ==> p' ->
             NameSets.mem y (config_free_names p) = false ->
             bound_inp x y / p ==> p'
  | RES : forall (y : name) (p p' : config) (a : action),
            not_silent a ->
            a / p ==> p' ->
            NameSets.mem y (action_names a) = false ->
            a / restrict y p ==> restrict y p'
  | OPEN : forall (x y : name) (p p' : config),
             free_out x y / p ==> p' ->
             x <> y ->
             bound_out x y / restrict y p ==> p'
  | PAR : forall (a : action) (p1 p1' p2 : config),
            a / p1 ==> p1' ->
            NameSets.is_empty (NameSets.inter (action_bound_names a) (config_free_names p2)) = true ->
            a / compose p1 p2 ==> compose p1' p2
  | COM : forall (x y : name) (p1 p1' p2 p2' : config),
            free_out x y / p1 ==> p1' ->
            free_inp x y / p2 ==> p2' ->
            silent / compose p1 p2 ==> compose p1' p2'
  | CLOSE : forall (x y : name) (p1 p1' p2 p2' : config),
              bound_out x y / p1 ==> p2 ->
              free_inp x y / p2 ==> p2' ->
              NameSets.mem y (config_free_names p2) = false ->
              silent / compose p1 p2 ==> restrict y (compose p1' p2')
  where "a '/' p '==>' q" := (trans a p q).
