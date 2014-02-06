Require Import Coq.Logic.FunctionalExtensionality Coq.Arith.EqNat Coq.MSets.MSets Names Sets Fun Config Typing.

Definition ConfigSubset {ns} {f} {p} (ty : ns ; f |- p) : Prop :=
  NameSets.For_all (fun x => ConfigFreeName x p) ns.

Lemma config_subset : forall ns f p (ty : ns ; f |- p), ConfigSubset ty.
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

    inversion H.

    apply NameSets.F.union_1 in H0.
    inversion_clear H0.
      apply IHty1 in H1.
      apply caseof_free_h_snd.
      auto.

      apply IHty2 in H1.
      apply caseof_free_t.
      auto.

    apply NameSets.P.singleton_equal_add in H.
    apply add_in in H.
    inversion H.
      rewrite H0; auto.

      apply NameSets.F.empty_iff in H0; easy.

    apply add_in in H0.
    inversion H0.
      rewrite H1; auto.

      assert (x = x2).
        apply NameSets.P.singleton_equal_add in H1.
        apply add_in in H1.
        inversion H1.
          auto.
          apply NameSets.F.empty_iff in H2; easy.
      rewrite H2; auto.
Qed.

Definition FunctionProperty {ns} {f} {p} (ty : ns ; f |- p) : Prop :=
  Fun.Fun_prop f.

Lemma function_property_1 : forall ns f p (ty : ns ; f |- p), Fun.Fun_prop_1 f.
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

    apply Fun.ch_empty_prop_1.

    apply Fun.fun_plus_prop_1; auto.

    apply Fun.ch_singleton_prop_1.

    apply Fun.ch_two_prop_1; auto.
Qed.

Lemma fun_exclusive : forall ns1 ns2 f1 f2 p1 p2
                             (ty1 : ns1 ; f1 |- p1) (ty2 : ns2 ; f2 |- p2),
                        NameSets.Empty (NameSets.inter ns1 ns2) ->
                        (forall x,
                           (Fun.in_domain f1 x -> ~ Fun.in_domain f2 x) /\
                           (Fun.in_domain f2 x -> ~ Fun.in_domain f1 x)).
Proof.
  intros.
  eapply inter_empty in H.
  inversion_clear H.
  split; intros; intro.
    apply typing_in_domain_1 with (x := x) in ty1.
      apply NameSets.F.mem_iff in ty1.
      apply typing_in_domain_1 with (x := x) in ty2.
        apply NameSets.F.mem_iff in ty2.
        apply H0 in ty1.
        apply ty1; auto.

        auto.
      auto.
    apply typing_in_domain_1 with (x := x) in ty1.
      apply NameSets.F.mem_iff in ty1.
      apply typing_in_domain_1 with (x := x) in ty2.
        apply NameSets.F.mem_iff in ty2.
        apply H0 in ty1.
        apply ty1; auto.

        auto.
      auto.
Qed.

Lemma function_property_2 : forall ns f p (ty : ns ; f |- p), Fun.Fun_prop_2 f.
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
      eapply typing_in_range_in_domain; apply ty1.
      eapply typing_in_range_in_domain; apply ty2.
      intros.
      eapply fun_exclusive with
      (ns1 := ns1) (ns2 := ns2) (f1 := f1) (f2 := f2) (p1 := p1) (p2 := p2) (x := x)
        in H; auto.

    apply Fun.fun_remove_prop_2; auto.

    apply Fun.ch_empty_prop_2.

    inversion H.
    inversion Compatible_prop.
    inversion H1.
    auto.

    apply Fun.ch_singleton_prop_2.

    apply Fun.ch_two_prop_2.
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

    apply Fun.ch_empty_prop_3.

    inversion H.
    inversion Compatible_prop.
    inversion H1; auto.

    apply Fun.ch_singleton_prop_3.

    apply Fun.ch_two_prop_3; auto.
Qed.

Lemma function_property : forall ns f p (ty : ns ; f |- p), FunctionProperty ty.
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

    inversion H; subst; auto.

    inversion H0; subst; auto.
    apply IHty1 in H6.
    apply IHty2 in H8.
    setoid_rewrite H6.
    setoid_rewrite H8.
    auto.

    inversion H; subst; auto.

    inversion H0; subst; auto.

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

    inversion H; auto.

    inversion H0; subst; auto.
    apply IHty1 in H6.
    apply IHty2 in H8.
    rewrite H6.
    rewrite H8.
    auto.

    inversion H; subst; auto.

    inversion H0; subst; auto.
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
