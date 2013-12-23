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

Fixpoint config_names (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create n1 n2 c' => NameSets.add n1 (NameSets.add n2 (config_names c'))
    | send n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | restrict n c' => NameSets.add n (config_names c')
    | compose c1 c2 => NameSets.union (config_names c1) (config_names c2)
  end.

Fixpoint config_free_names' (bounded : NameSets.t) (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create n1 n2 c' => if NameSets.mem n1 bounded
                         then (config_free_names' (NameSets.add n2 bounded) c')
                         else NameSets.add n1 (config_free_names' (NameSets.add n2 bounded) c')
    | send n1 n2 => if NameSets.mem n1 bounded
                    then NameSets.empty
                    else NameSets.singleton n1
    | restrict n c' => config_free_names' (NameSets.add n bounded) c'
    | compose c1 c2 => NameSets.union (config_free_names' bounded c1) (config_free_names' bounded c2)
  end.

Definition config_free_names (c : config) : NameSets.t := config_free_names' NameSets.empty c.

Goal forall x y : name, config_free_names (send x y) = NameSets.singleton x.
Proof.
  intros.
  unfold config_free_names.
  auto.
Qed.

Lemma config_free_names_create : forall (p : config) (x y : name),
                                   config_free_names (create x y p) = NameSets.add x (config_free_names p).
Proof.
  intros.
  induction p.
    compute.
    auto.

    unfold config_free_names.
    simpl.
    destruct (NameSets.mem n (NameSets.add y NameSets.empty)) eqn:?.

    unfold config_free_names in IHp.
    setoid_rewrite <- NameSets.P.singleton_equal_add in Heqb.
    apply NameSets.EP.singleton_mem_3 in Heqb.
    destruct y, n.
    rewrite <- Heqb.
    simpl in IHp.
Admitted.

Fixpoint config_bound_names (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create _ n c' => NameSets.add n (config_bound_names c')
    | send _ _ => NameSets.empty
    | restrict n c' => NameSets.add n (config_bound_names c')
    | compose c1 c2 => NameSets.union (config_bound_names c1) (config_bound_names c2)
  end.

Definition ConfigSubset {ns : NameSets.t} {f : Fun.temp_name_mapping} {p : config} (ty : ns ; f |- p) : Prop :=
  NameSets.subset ns (config_free_names p) = true.

Lemma config_subset : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), ConfigSubset ty.
Proof.
  intros.
  unfold ConfigSubset.
  induction ty.
    auto.

    auto.

    inversion ty.
      assert (config_free_names (create x y nil) = NameSets.singleton x).
        compute.
        auto.
      rewrite H.



Admitted.

Definition FunctionProperty {ns : NameSets.t} {f : Fun.temp_name_mapping} {p : config} (ty : ns ; f |- p) : Prop :=
  Fun.Fun_prop f.

Lemma function_property1 : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), Fun.Fun_prop1 f.
Proof.
  unfold Fun.Fun_prop1.
  unfold not.
  intros.
  induction ty.
    compute in H; discriminate.
    compute in H; discriminate.
    apply Tuple.ch_singleton_not_name with x0 x x; auto.
    apply Tuple.ch_singleton_not_name with x0 x x; auto.
    destruct (NameDecidableType.eq_dec x x0).
      destruct (NameDecidableType.eq_dec x z).
        destruct x, x0, z.
        simpl in e.
        simpl in e0.
        apply H0.
        apply name_cons_prop.
        rewrite <- e; auto.

        destruct x, x0, z.
        simpl in e, n.
        rewrite e in H.
        assert (Tuple.ch (Tuple.add (name_cons n1) (Tuple.singleton (name_cons n2))) (name_cons n1) = Some (star_name (name_cons n2))).
          induction n1.
            compute; auto.
            compute.
            rewrite <- beq_nat_refl; auto.
        rewrite H in H3.
        inversion H3.
        rewrite H5 in e.
        auto.
      destruct (NameDecidableType.eq_dec x z).
        destruct x, x0, z.
        simpl in n, e.
        rewrite e in H.
        rewrite e in n.
        assert (forall x y, x <> y -> Tuple.ch (Tuple.add x (Tuple.singleton y)) y = Some star_bottom).
          destruct x, y0.
          generalize dependent n4.
          induction n3, n4.
            intro; exfalso; auto.
            intro.
            compute.
            rewrite <- beq_nat_refl.
            auto.
            intro.
            compute.
            auto.
            intro.
            rewrite name_cons_prop in H3.
            compute.
            rewrite <- beq_nat_refl.
Admitted.

Lemma function_property2 : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), Fun.Fun_prop2 f.
Proof.
  unfold Fun.Fun_prop2.
  intros ns f p ty.
  induction ty.
    intros; exfalso; apply H; auto.
    intros; exfalso; apply H; auto.

    intros.
    apply Tuple.ch_singleton_domain in H.
    apply Tuple.ch_singleton_domain in H0.
    rewrite <- H0; auto.

    intros.
    apply Tuple.ch_singleton_domain in H1.
    apply Tuple.ch_singleton_domain in H2.
    rewrite <- H1; auto.

    intros.
    apply Tuple.ch_domain in H2.
    apply Tuple.ch_domain in H3.
    inversion_clear H2.
      inversion_clear H3.
        rewrite <- H9; rewrite <- H2; auto.
        apply Tuple.ch_domain in H2.
        inversion_clear H2.
          rewrite <- H9 in H4.
          rewrite <- H3 in H4.
          simpl in H4.
          rewrite beq_name_refl in H4.
          apply beq_name_false_iff in H.
          rewrite beq_name_sym in H.
          rewrite H in H4.
          rewrite beq_name_refl in H4.
          discriminate.
          apply Tuple.ch_domain_empty in H3.
          contradiction.
      inversion_clear H3.
        apply Tuple.ch_domain in H9.
        inversion_clear H9.
          rewrite <- H2 in H4.
          rewrite <- H3 in H4.
          simpl in H4.
          apply beq_name_false_iff in H.
          rewrite H in H4.
          rewrite beq_name_sym in H.
          rewrite H in H4.
          rewrite beq_name_refl in H4.
          symmetry in H4.
          rewrite beq_name_refl in H4.
          discriminate.

          apply Tuple.ch_domain_empty in H3.
          contradiction.
        apply Tuple.ch_domain in H9.
        apply Tuple.ch_domain in H2.
        inversion_clear H9.
          inversion_clear H2.
            rewrite <- H3; rewrite <- H9; auto.
            apply Tuple.ch_domain_empty in H9; contradiction.
          inversion_clear H2.
            apply Tuple.ch_domain_empty in H3; contradiction.
            apply Tuple.ch_domain_empty in H3; contradiction.
    intros.
    subst.
    apply Tuple.ch_domain in H3.
    apply Tuple.ch_domain in H4.
    inversion_clear H3.
      inversion_clear H4.
        rewrite <- H2; rewrite <- H3; auto.
        apply Tuple.ch_singleton_domain in H3.
        rewrite <- H2 in H5.
        rewrite <- H3 in H5.
        simpl in H5.
        apply beq_name_false_iff in H.
        rewrite H in H5.
        rewrite beq_name_sym in H.
        rewrite H in H5.
        rewrite beq_name_refl in H5.
        symmetry in H5.
        rewrite beq_name_refl in H5.
        discriminate.

      inversion_clear H4.
        apply Tuple.ch_singleton_domain in H2.
        rewrite <- H2 in H5.
        rewrite <- H3 in H5.
        simpl in H5.
        apply beq_name_false_iff in H.
        rewrite H in H5.
        rewrite beq_name_sym in H.
        rewrite H in H5.
        rewrite beq_name_refl in H5.
        symmetry in H5.
        rewrite beq_name_refl in H5.
        discriminate.

        apply Tuple.ch_singleton_domain in H2.
        apply Tuple.ch_singleton_domain in H3.
        rewrite <- H2.
        rewrite <- H3.
        auto.

    intros; subst.
    apply Fun.fun_plus_domain in H0.
    apply Fun.fun_plus_domain in H1.
    inversion_clear H0.
      inversion_clear H1.
        apply IHty1.
          auto.
          auto.

          unfold Fun.fun_plus in H2.
          unfold Fun.fun_plus in H3.
          unfold Fun.fun_plus in H4.
          unfold Fun.fun_plus in H5.
          unfold Fun.fun_plus in H6.
          unfold Fun.domain in H7.
          unfold Fun.domain in H0.
          destruct (f1 x) eqn:?.
            induction s.
              destruct (f1 y) eqn:?.
                induction s.
                  auto.
                  destruct (f2 y) eqn:?.
                    induction s.



          apply typing_domain_1 with (ns := ns1) (p := p1) in H7.
          apply typing_domain_1 with (ns := ns2) (p := p2) in H0.





Lemma function_property : forall (ns : NameSets.t) (f : Fun.temp_name_mapping) (p : config) (ty : ns ; f |- p), FunctionProperty ty.
Proof.
  unfold FunctionProperty.
  unfold Fun.Fun_prop.
  intros.

Admitted.


Definition Uniqueness {ns : NameSets.t} {f : function ns} {p : config} (ty : ns ; f |- p) : Prop :=
  forall (ns' : NameSets.t) (f' : function ns'),
    ns' ; f' |- p -> ns = ns' /\ f = f'.

Lemma uniqueness : forall (ns : NameSets.t) (f : function ns) (p : config) (ty : ns ; f |- p), Uniqueness ty.
Proof.
  unfold Uniqueness.
  intros.
  remember p.
  split.
  induction ty.
    inversion H.
    induction H.
      auto.
      auto.


      rewrite <- IHtyping in H0.
      rewrite <- IHtyping in H1.

      assert (Option.to_set z = NameSets.empty).
      compute in H0.
      unfold NameSets.empty.
      rewrite

Theorem Soundness : forall (ns : NameSets.t) (f : function ns) (p : config) (ty : ns ; f |- p),
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
