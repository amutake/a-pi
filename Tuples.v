Require Import Coq.Arith.EqNat Coq.Vectors.Vector Coq.Logic.Decidable Names Sets Fun.

Module Tuple.

  Definition t := Vector.t name.

  Definition empty := Vector.nil name.

  Definition cons {p : nat} n (v : t p) := Vector.cons name n p v.

  Definition singleton (n : name) : t 1 := cons n empty.

  Definition append {p q : nat} (vp : t p) (vq : t q) := Vector.append vp vq.

  Fixpoint to_set {n : nat} (ntup : t n) : NameSets.t :=
    match ntup with
      | nil => NameSets.empty
      | Vector.cons n _ t => NameSets.add n (to_set t)
    end.

  Fixpoint ch {n : nat} (tup : t n) : Fun.temp_name_mapping :=
    fun x : name =>
      match tup with
        | nil => None
        | Vector.cons y _ tup' =>
          if beq_name x y
          then match tup' with
                 | nil => Some star_bottom
                 | Vector.cons z _ _ => Some (star_name z)
               end
          else ch tup' x
      end.

  Goal forall (x : name), ch (nil name) x = None.
  Proof. auto. Qed.

  Goal forall (x : name), ch (Tuple.singleton x) x = Some star_bottom.
  Proof.
    intros.
    destruct x.
    simpl.
    rewrite <- beq_nat_refl.
    auto.
  Qed.

  Goal forall (x y z : name), ch (cons x (cons y (cons z empty))) x = Some (star_name y).
  Proof.
    destruct x, y, z.
    simpl.
    rewrite <- beq_nat_refl.
    auto.
  Qed.

  Lemma ch_empty : ch empty = Fun.empty.
  Proof. auto. Qed.

  Lemma ch_domain : forall (n : nat) (tup : t n) (x y : name),
                      Fun.domain (ch (cons x tup)) y <-> x = y \/ Fun.domain (ch tup) y.
  Proof.
    split.
      intros.
      destruct (beq_name x y) eqn:?.
        apply beq_name_true_iff in Heqb.
        left; auto.
        right.
        unfold Fun.domain in H.
        simpl in H.
        destruct tup.
          unfold Fun.domain.
          simpl.
          intro.
          rewrite beq_name_sym in H.
          rewrite Heqb in H.
          apply beq_name_false_iff in Heqb.
          auto.

          rewrite beq_name_sym in H.
          rewrite Heqb in H.
          unfold Fun.domain.
          auto.
    intros.
    inversion H.
      unfold Fun.domain.
      rewrite H0.
      simpl.
      destruct tup.
        destruct y; simpl.
        rewrite <- beq_nat_refl.
        intro; discriminate.

        destruct y; simpl.
        rewrite <- beq_nat_refl.
        intro; discriminate.
    unfold Fun.domain.
    unfold Fun.domain in H0.
    simpl.
    intro.
    destruct tup.
      simpl in H0; apply H0; auto.
      destruct (beq_name y x) eqn:?.
        discriminate.
        auto.
  Qed.

  Lemma ch_not_domain : forall (n : nat) (tup : t n) (x y : name),
                          ~ Fun.domain (ch (cons x tup)) y <-> x <> y /\ ~ Fun.domain (ch tup) y.
  Proof.
    split.
      split.
        intro.
        rewrite H0 in H.
        unfold Fun.domain in H.
        destruct y.
        simpl in H.
        rewrite <- beq_nat_refl in H.
        apply H.
        intro.
        destruct tup.
          discriminate.
          discriminate.

      intro.
      unfold Fun.domain in H, H0.
      simpl in H.
      destruct tup.
        simpl in H0; apply H0; auto.
        destruct (beq_name y x).
         apply H.
         intro; discriminate.
         auto.

    intros.
    inversion_clear H.
    intro.
    unfold Fun.domain in H, H1.
    simpl in H.
    destruct tup.
      destruct (beq_name y x) eqn:?.
        apply beq_name_true_iff in Heqb.
        auto.
        auto.

      destruct (beq_name y x) eqn:?.
        apply beq_name_true_iff in Heqb.
        auto.
        auto.
  Qed.

  Lemma ch_singleton_S : forall x y, ch (singleton (name_cons x)) (name_cons y) =
                           ch (singleton (name_cons (S x))) (name_cons (S y)).
  Proof. auto. Qed.

  (* the singleton version of ch_domain *)
  Lemma ch_domain_singleton : forall x y, Fun.domain (ch (singleton x)) y <-> x = y.
  Proof.
    split.
      intros.
      apply ch_domain in H.
      inversion H.
        auto.
        compute in H0; exfalso; apply H0; auto.
      intros.
      rewrite H.
      unfold Fun.domain.
      simpl.
      rewrite beq_name_refl.
      intro.
      discriminate.
  Qed.

  Lemma ch_domain_cons : forall (n : nat) (tup : t n) (x y : name),
                          Fun.domain (ch (cons x tup)) y ->
                          ~ Fun.domain (ch tup) y ->
                          x = y.
  Proof.
    intros.
    apply ch_domain in H.
    inversion H; auto.
    contradiction.
  Qed.

  Fixpoint tuple_ch_domain_prop {n : nat} (tup : t n) (x : name) : Prop :=
    match tup with
      | nil => False
      | Vector.cons y _ tup' => y = x \/ tuple_ch_domain_prop tup' x
    end.

  Lemma ch_0_tuple_domain : forall (tup : t 0) x, ~ Fun.domain (ch tup) x.
  Proof.
    intros.
    intro.
    unfold Fun.domain in H.
    apply H.
    dependent inversion tup.
    auto.
  Qed.

  Lemma ch_1_tuple_domain : forall (tup : t 1) (x : name), Fun.domain (ch tup) x -> tuple_ch_domain_prop tup x.
  Proof.
    intro.
    dependent inversion tup.
    dependent inversion t0.
    left.
    apply ch_domain_singleton in H.
    auto.
  Qed.

  Lemma ch_n_tuple_domain : forall (n : nat) (tup : t n) (x : name), Fun.domain (ch tup) x -> tuple_ch_domain_prop tup x.
  Proof.
    intros.
    induction tup.
      simpl.
      apply H.
      simpl.
      auto.

      apply ch_domain in H.
      inversion H.
        rewrite H0.
        simpl.
        left.
        auto.

        simpl.
        right.
        apply IHtup.
        auto.
  Qed.

  Lemma ch_singleton_None : forall (x y : name), x <> y <-> ch (singleton x) y = None.
  Proof.
    split.
      unfold not.
      generalize dependent y.
      destruct x; induction n.
        intros.
        destruct y; induction n.
          exfalso.
          auto.
          compute.
          auto.
        intros.
        destruct y; induction n0.
          compute.
          auto.
          rewrite <- ch_singleton_S.
          apply IHn.
          intro.
          apply H.
          apply name_S.
          auto.

      intros.
      destruct x, y.
      unfold ch in H.
      simpl in H.
      destruct (beq_nat n0 n) eqn:?.
        discriminate.
        apply beq_nat_false_iff in Heqb.
        intro.
        apply name_cons_prop in H0.
        auto.
  Qed.

  Lemma ch_singleton_not_name : forall (x y z : name), ch (singleton x) y = Some (star_name z) -> False.
  Proof.
    destruct x, y.
    generalize dependent n0.
    induction n, n0; try (intros; compute in H; discriminate).
    intros.
    apply IHn with (z := z) (n0 := n0).
    rewrite ch_singleton_S.
    auto.
  Qed.

  Lemma ch_singleton_Fun_prop1 : forall (n : name), Fun.Fun_prop1 (ch (singleton n)).
  Proof.
    unfold Fun.Fun_prop1.
    unfold not.
    intros.
    destruct n, x.
    induction n, n0; try (compute in H; discriminate).
      eapply ch_singleton_not_name.
      apply H.
  Qed.

  Lemma ch_singleton_Fun_prop2 : forall (n : name), Fun.Fun_prop2 (ch (singleton n)).
  Proof.
    unfold Fun.Fun_prop2.
    unfold not.
    intros.
    destruct (ch (singleton n) x).
      induction s.
        exfalso.
        eapply ch_singleton_not_name.
        symmetry.
        apply H1.

        rewrite H1 in H4.
        exfalso; apply H4.
        auto.

        rewrite H1 in H5.
        exfalso; apply H5.
        auto.

      unfold Fun.domain in H0.
      exfalso; apply H0.
      auto.
  Qed.

  Lemma ch_singleton_Fun_prop3 : forall (n : name), Fun.Fun_prop3 (ch (singleton n)).
  Proof.
    unfold Fun.Fun_prop3.
    unfold Fun.fun_join.
    unfold Fun.to_star_function.
    destruct n; induction n.
      destruct x; induction n.
        auto.
        intros.
        exfalso; apply H; auto.

      destruct x; induction n0.
        intros; exfalso; apply H; auto.
        intros.
        rewrite <- ch_singleton_S.
        destruct (ch (singleton (name_cons n)) (name_cons n0)) eqn:?.
          induction s; auto.
            exfalso; eapply ch_singleton_not_name.
            apply Heqo.
          exfalso.
          apply H.
          rewrite <- Heqo.
          rewrite <- ch_singleton_S.
          auto.
  Qed.

  Lemma ch_singleton_Fun_prop : forall (n : name), Fun.Fun_prop (ch (singleton n)).
  Proof.
    unfold Fun.Fun_prop.
    split.
    apply ch_singleton_Fun_prop1.
    split.
    apply ch_singleton_Fun_prop2.
    apply ch_singleton_Fun_prop3.
  Qed.

  Lemma tuple_domain_mem : forall n (tup : t n) x,
                             Fun.domain (ch tup) x <-> NameSets.In x (to_set tup).
  Proof.
    split.
      intros.
      induction tup.
        unfold Fun.domain in H.
        simpl in H.
        exfalso; apply H; auto.

        apply ch_domain in H.
        inversion H.
          rewrite H0.
          simpl.
          apply mem_head.
          simpl.
          apply mem_tail_1.
          apply IHtup.
          auto.
      intros.
      unfold Fun.domain.
      induction tup.
        simpl.
        assert (to_set (nil name) = NameSets.empty).
          auto.
        rewrite H0 in H.
        apply NameSets.F.mem_iff in H.
        rewrite NameSets.EP.empty_mem in H.
        discriminate.

        simpl.
        destruct (beq_name x h) eqn:?.
          intro.
          destruct tup; discriminate.
          apply IHtup.
          apply beq_name_false_iff in Heqb.
          simpl in H.
          apply mem_tail_2 with h.
          auto.
          auto.
  Qed.
End Tuple.

Module Option.

  Definition t := option name.

  Definition to_set (t' : t) : NameSets.t :=
    match t' with
      | None => NameSets.empty
      | Some n => NameSets.singleton n
    end.

  Definition length (t' : t) : nat :=
    match t' with
      | None => O
      | Some _ => 1
    end.

  Definition to_tuple (t' : t) : Tuple.t (length t') :=
    match t' with
      | None => nil name
      | Some n => cons name n 0 (nil name)
    end.

  Definition append {p : nat} (v : Tuple.t p) (t' : t) : Tuple.t (p + length t') :=
    Tuple.append v (to_tuple t').

End Option.
