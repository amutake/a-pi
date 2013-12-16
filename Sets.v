Require Import Coq.MSets.MSets Coq.Arith.Peano_dec Coq.Arith.EqNat Names.

Module NameSets := MSetWeakList.MakeRaw(NameDecidableType).
Module StarSets := MSetWeakList.MakeRaw(StarDecidableType).

Lemma mem_head : forall x s, NameSets.mem x (NameSets.add x s) = true.
Proof.
  intros.
  destruct x.
  induction s.
    simpl.
    destruct (eq_nat_dec n n); auto.

    destruct a.
    simpl.
    destruct (eq_nat_dec n n0).
      rewrite <- e.
      simpl.
      destruct (eq_nat_dec n n); auto.
      simpl.
      destruct (eq_nat_dec n n0); auto.
Qed.

Lemma mem_tail : forall x y s, NameSets.mem x s = true -> NameSets.mem x (NameSets.add y s) = true.
Proof.
  intros.
  destruct x, y.
  induction s.
    simpl in H; discriminate.
    destruct a.
    simpl.
    destruct (eq_nat_dec n0 n1).
      auto.
      simpl.
      destruct (eq_nat_dec n n1).
        auto.
        apply IHs.
        simpl in H.
        destruct (eq_nat_dec n n1).
          contradiction.
          auto.
Qed.

Lemma mem_tail_2 : forall x y s, NameSets.mem x (NameSets.add y s) = true ->
                                 x <> y ->
                                 NameSets.mem x s = true.
Proof.
  intros.
  induction s.
  simpl in H.
  destruct (NameDecidableType.eq_dec x y).
    destruct x, y.
    simpl in e.
    rewrite name_cons_prop in H0.
    easy.

    auto.
  destruct x, y, a.
  simpl.
  destruct (eq_nat_dec n n1).
    auto.
    apply IHs.
    simpl in H.
    destruct (eq_nat_dec n0 n1).
      simpl in H.
      destruct (eq_nat_dec n n1).
        contradiction.
        apply mem_tail.
        auto.
      rewrite name_cons_prop in H0.
      simpl in H.
      destruct (eq_nat_dec n n1).
        contradiction.
        auto.
Qed.

Lemma union_add : forall x ns1 ns2, NameSets.union (NameSets.add x ns1) ns2 =
                                    NameSets.add x (NameSets.union ns1 ns2).
Proof.

  destruct x.
  induction ns1; induction ns2.
    compute.
    auto.

    destruct a.
    simpl.
    destruct (eq_nat_dec n n0).
      rewrite e.
Admitted.

Lemma union_ns_nil : forall ns, NameSets.union ns nil = ns.
Proof.
  intros.
  induction ns.
    auto.
Admitted.

Lemma mem_union : forall ns1 ns2 x,
                    NameSets.mem x (NameSets.union ns1 ns2) = true <->
                    NameSets.mem x ns1 = true \/ NameSets.mem x ns2 = true.
Proof.
  intros.
  split.
    intro.
    generalize dependent ns2.
    induction ns1; induction ns2.
      intro.
      simpl in H; auto.
      intro.
      destruct x, a.
      simpl in H.
      destruct (eq_nat_dec n n0).
        right.
        rewrite e.
        simpl.
        destruct (eq_nat_dec n0 n0).
          auto.
          auto.
        right.
        simpl.
        destruct (eq_nat_dec n n0).
          auto.
          auto.

      intro.
      left.
Admitted.

Lemma mem_remove : forall x y ns, NameSets.mem x ns = true ->
                                  NameSets.mem x (NameSets.remove y ns) = true \/ x = y.
Proof.
  destruct x, y.
  induction ns.
    simpl; intro; discriminate.
    intros.
    destruct a.
    simpl in H.
    destruct (eq_nat_dec n n1).
      rewrite <- e.
      simpl.
      destruct (eq_nat_dec n0 n).
        rewrite e0.
        right; auto.

        left.
        simpl.
        destruct (eq_nat_dec n n); auto.
      simpl.
      destruct (eq_nat_dec n0 n1).
        left; auto.
        simpl.
        destruct (eq_nat_dec n n1).
          left; auto.
          destruct (eq_nat_dec n n0).
            right; rewrite e; auto.
            left.
            apply IHns in H.
            inversion H.
              auto.
              inversion H0.
              contradiction.
Qed.

Lemma inter_empty_not_mem : forall ns1 ns2 x y,
                              NameSets.inter ns1 ns2 = NameSets.empty ->
                              NameSets.mem x ns1 = true ->
                              NameSets.mem y ns2 = true ->
                              x <> y.
Proof.
  induction ns1, ns2; destruct x, y; intros.
    simpl in H0; discriminate.
    simpl in H0; discriminate.
    simpl in H1; discriminate.
    destruct a, e.
    simpl in H0.
    simpl in H1.
    apply IHns1 with ns2.
    unfold NameSets.inter in H.
    simpl in H.

    destruct (eq_nat_dec n n1) eqn:?.
      destruct (eq_nat_dec n0 n2) eqn:?.
Admitted.
