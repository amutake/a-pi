Require Import
        Coq.MSets.MSets Coq.Arith.Peano_dec Coq.Arith.Compare_dec Coq.Arith.EqNat Names.

Module StarDecidableType <: DecidableType.

  Definition t := star.
  Definition eq (s1 s2 : star) :=
    match s1, s2 with
      | star_name n1, star_name n2 => NameDecidableType.eq n1 n2
      | _, _ => s1 = s2
    end.
  Lemma star_refl : Reflexive eq.
  Proof.
    unfold Reflexive.
    intros.
    destruct x; simpl; auto.
    apply NameDecidableType.name_refl.
  Qed.
  Lemma star_sym : Symmetric eq.
    unfold Symmetric.
    intros.
    destruct x, y; simpl; auto.
    apply NameDecidableType.name_sym.
    simpl in H.
    auto.
  Qed.
  Lemma star_trans : Transitive eq.
  Proof.
    unfold Transitive.
    intros.
    destruct x, y, z; simpl; auto; try inversion H; try inversion H0.
    simpl in H, H0.
    generalize n, n0, n1, H, H0.
    fold (Transitive NameDecidableType.eq).
    apply NameDecidableType.name_trans.
  Qed.
  Definition eq_equiv :=
    Build_Equivalence t eq star_refl star_sym star_trans.
  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros.
    destruct x, y; simpl; try solve [ left; auto | right; intro H; inversion H ].
    apply NameDecidableType.eq_dec.
  Qed.
End StarDecidableType.


Module NameOrderedType <: OrderedType.
  Definition t := name.
  Definition eq :=
    fun name1 name2 =>
      match name1, name2 with
        | name_cons n1, name_cons n2 => n1 = n2
      end.
  Lemma name_refl : Reflexive eq.
  Proof.
    unfold Reflexive.
    intros.
    destruct x.
    simpl.
    auto.
  Qed.
  Lemma name_sym : Symmetric eq.
  Proof.
    unfold Symmetric.
    intros.
    destruct x, y.
    simpl; simpl in H.
    auto.
  Qed.
  Lemma name_trans : Transitive eq.
  Proof.
    unfold Transitive.
    intros.
    destruct x, y, z.
    simpl; simpl in H, H0.
    omega.
  Qed.
  Definition eq_equiv :=
    Build_Equivalence t eq name_refl name_sym name_trans.
  Definition lt :=
    fun name1 name2 =>
      match name1, name2 with
        | name_cons n1, name_cons n2 => lt n1 n2
      end.
  Lemma name_irrefl : Irreflexive lt.
  Proof.
    unfold Irreflexive.
    unfold Reflexive, complement.
    intros.
    destruct x.
    simpl in H.
    omega.
  Qed.
  Lemma name_trans_lt : Transitive lt.
  Proof.
    unfold Transitive.
    intros.
    destruct x, y, z.
    simpl; simpl in H, H0.
    omega.
  Qed.
  Definition lt_strorder :=
    Build_StrictOrder t lt name_irrefl name_trans_lt.
  Theorem lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful, iff.
    intros.
    destruct x, y, x0, y0.
    simpl; simpl in H, H0.
    omega.
  Qed.
  Definition compare :=
    fun name1 name2 =>
      match name1, name2 with
        | name_cons n1, name_cons n2 => nat_compare n1 n2
      end.
  Theorem compare_spec : forall x y : t,
    CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y.
    simpl.
    remember (nat_compare n n0).
    destruct c.
      apply CompEq.
      apply nat_compare_eq.
      auto.

      apply CompLt.
      apply nat_compare_lt.
      auto.

      apply CompGt.
      apply nat_compare_gt.
      auto.
  Qed.
  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    destruct x, y.
    simpl.
    apply eq_nat_dec.
  Qed.
End NameOrderedType.

(* Module NameSets := MSetWeakList.MakeRaw(NameDecidableType). *)
(* Module StarSets := MSetWeakList.MakeRaw(StarDecidableType). *)

Module StarSets := MSetWeakList.Make(StarDecidableType).

Module NameSets.
  Module M := MSetWeakList.Make(NameDecidableType).
  Module P := WPropertiesOn(NameDecidableType)(M).
  Module F := WFactsOn(NameDecidableType)(M).
  Include M.
End NameSets.

Lemma mem_head : forall x s, NameSets.In x (NameSets.add x s). (* NameSets.mem x (NameSets.add x s) = true. *)
Proof.
  intros.
  destruct x.
  destruct s.
  induction this.
    compute.
    destruct (eq_nat_dec n n); auto.

    destruct a.
    apply IHthis.
    compute.
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

Lemma union_add : forall In

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







Lemma union_ns_nil : forall ns, NameSets.union ns nil = ns.
Proof.
  intros.
  induction ns.
    auto.
    rewrite union_add.



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
