Require Import Coq.Logic.FunctionalExtensionality Coq.Arith.EqNat Coq.MSets.MSets Names Sets Fun Tuples.

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
                  NameSets.singleton x ; Tuple.ch (Tuple.singleton x) |- create x y p
  | ACT_x : forall (f : Fun.temp_name_mapping) (p : config) (x y : name),
              NameSets.singleton x ; Tuple.ch (Tuple.singleton x) |- p ->
              x <> y ->
              NameSets.singleton x ; Tuple.ch (Tuple.singleton x) |- create x y p
  | ACT_z : forall (f : Fun.temp_name_mapping) (p : config) (x y z : name),
              NameSets.singleton z ; Tuple.ch (Tuple.singleton z) |- p ->
              x <> z ->
              y <> z ->
              NameSets.add x (NameSets.singleton z) ; Tuple.ch (Tuple.cons x (Tuple.singleton z)) |- create x y p
  | ACT_xz : forall (f : Fun.temp_name_mapping) (p : config) (x y z : name),
               NameSets.add x (NameSets.singleton z) ; Tuple.ch (Tuple.cons x (Tuple.singleton z)) |- p ->
               x <> z ->
               x <> y ->
               y <> z ->
               NameSets.add x (NameSets.singleton z) ; Tuple.ch (Tuple.cons x (Tuple.singleton z)) |- create x y p
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
          with (Tuple.ch (Tuple.singleton (name_cons 0))).
  eapply ACT_empty.
  apply NIL.
  auto.
  apply functional_extensionality.
  intro.
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
    inversion H5; subst.
      apply NameSets.F.is_empty_iff in H6.
      compute in H6.

  inversion H4.
  inversion H4.
  inversion H4.
  inversion H5; subst.
  destruct z; induction n; compute in H6; discriminate.
  destruct z; induction n; compute in H6; discriminate.
  destruct z; induction n; inversion H4.
(*   destruct z; induction n; inversion H4. *)
(* Qed. *)
Admitted.

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
  with (Tuple.ch (Tuple.singleton (name_cons 0))).
  eapply ACT_empty.
  apply NIL.
  auto.
  apply functional_extensionality.
  intro.
  destruct x; induction n.
    auto.
    auto.
  replace (fun x => match x with
                      | name_cons 2 => Some star_bottom
                      | _ => None
                    end)
  with (Tuple.ch (Tuple.singleton (name_cons 2))).
  eapply ACT_empty.
  apply NIL.
  auto.

  apply functional_extensionality.
  intro.
  destruct x; induction n.
    auto.
    induction n.
      auto.
(*       rewrite <- Tuple.ch_S. *)
(*       rewrite <- Tuple.ch_S. *)
(*       induction n. *)
(*       auto. *)
(*       apply Tuple.ch_singleton_None. *)
(*       unfold not. *)
(*       intro. *)
(*       inversion H. *)

(*   auto. *)
(*   unfold Fun.fun_plus. *)
(*   apply functional_extensionality. *)
(*   intros. *)
(*   destruct x; induction n. *)
(*     auto. *)
(*     auto. *)
(*   auto. *)
(* Qed. *)
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

      apply Tuple.ch_domain_singleton in H.
      rewrite H.
      destruct x.
      simpl.
      destruct (Peano_dec.eq_nat_dec n n); auto.

      apply Tuple.ch_singleton_domain in H.
      rewrite H.
      destruct x.
      simpl.
      destruct (Peano_dec.eq_nat_dec n n); auto.

      apply Tuple.ch_domain in H.
      inversion H.
        rewrite H3.
        simpl.
        destruct (NameDecidableType.eq_dec x z) eqn:?.
          rewrite H3 in H0.
          destruct x, z.
          simpl in e.
          rewrite name_cons_prop in H0.
          auto.

          simpl.
          rewrite Heqs.
          destruct (NameDecidableType.eq_dec x x) eqn:?.
            auto.
            destruct x.
            unfold NameDecidableType.eq in n0.
            auto.
            apply Tuple.tuple_domain_mem in H3.
            simpl in H3.
            destruct (NameDecidableType.eq_dec x z).
              destruct x, z.
              simpl in e.
              rewrite e.
              simpl.
              destruct (NameDecidableType.eq_dec x0 (name_cons n0)).
                simpl.
                destruct (Peano_dec.eq_nat_dec n0 n0); auto.
                destruct x0.
                simpl.
                destruct (Peano_dec.eq_nat_dec n0 n0); auto.
          discriminate.
          apply IHty.
          auto.
          apply mem_union.
          apply Fun.fun_plus_domain in H.
          inversion H.
          apply IHty1 in H1.
          left; auto.
          apply IHty2 in H1.
          right; auto.

      apply Fun.fun_remove_domain_2 in H.
      inversion H.
      apply IHty in H1.
      apply Sets.mem_remove with (y := x0) in H1.
      inversion H1; auto.
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
    (*   apply H0 in H. *)
    (*   auto. *)

    (* unfold Fun.domain. *)
    (* intro; intro. *)
    (* induction ty. *)
    (*   simpl in H. *)
    (*   discriminate. *)

    (*   simpl in H; discriminate. *)

    (*   apply Tuple.ch_singleton_None_rev in H1. *)
    (*   destruct x, x0. *)
    (*   simpl in H0. *)
    (*   destruct (Peano_dec.eq_nat_dec n n0). *)
    (*     apply H1; f_equal; auto. *)
    (*     discriminate. *)

    (*   apply Tuple.ch_singleton_None_rev in H1. *)
    (*   destruct x, x0. *)
    (*   simpl in H0. *)
    (*   destruct (Peano_dec.eq_nat_dec n n0). *)
    (*     apply H1; f_equal; auto. *)
    (*     discriminate. *)

    (*   apply H in H1. *)
    (*   apply Tuple.ch_not_domain in H1. *)
    (*   destruct x, x0, y, z. *)
    (*   inversion_clear H1. *)
    (*   inversion_clear H0. *)
    (*   apply Tuple.ch_not_domain in H6. *)
    (*   inversion_clear H6. *)
    (*   subst. *)
    (*   simpl in IHty. *)
    (*   destruct (Peano_dec.eq_nat_dec n n2). *)
    (*     rewrite e in H0. *)
    (*     apply H0; auto. *)
    (*     destruct (beq_nat n n2) eqn:?. *)
    (*       apply beq_nat_true_iff in Heqb. *)
    (*       contradiction. *)
    (*       apply beq_nat_false_iff in Heqb. *)
    (*       inversion_clear ty; subst. *)
    (*         inversion_clear H4; subst. *)
Admitted.

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
