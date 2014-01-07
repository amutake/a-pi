Require Import Coq.MSets.MSets Coq.Arith.Peano_dec Coq.Arith.EqNat Coq.Classes.Morphisms Names.

Module StarSets.
  Module M := MSetWeakList.Make(StarDecidableType).
  Module P := WPropertiesOn(StarDecidableType)(M).
  Module EP := WEqPropertiesOn(StarDecidableType)(M).
  Module F := WFactsOn(StarDecidableType)(M).
  Include M.
End StarSets.
Module NameSets.
  Module M := MSetWeakList.Make(NameDecidableType).
  Module P := WPropertiesOn(NameDecidableType)(M).
  Module EP := WEqPropertiesOn(NameDecidableType)(M).
  Module F := WFactsOn(NameDecidableType)(M).
  Include M.
End NameSets.

Hint Resolve NameSets.P.equal_refl.

Lemma mem_head : forall x s, NameSets.In x (NameSets.add x s).
Proof.
  intros.
  apply NameSets.F.mem_iff.
  apply NameSets.EP.add_mem_1.
Qed.

Lemma mem_tail_1 : forall x y s, NameSets.In x s -> NameSets.In x (NameSets.add y s).
Proof.
  intros.
  apply NameSets.F.mem_iff.
  apply NameSets.EP.add_mem_3.
  apply NameSets.F.mem_iff.
  auto.
Qed.

Lemma mem_tail_2 : forall x y s, NameSets.In x (NameSets.add y s) ->
                                 x <> y ->
                                 NameSets.In x s.
Proof.
  intros.
  assert (y <> x).
    intro.
    apply H0; auto.
  apply name_neq_iff in H1.
  apply NameSets.EP.add_mem_2 with (s := s) in H1.
  apply NameSets.F.mem_iff.
  apply NameSets.F.mem_iff in H.
  rewrite <- H.
  symmetry.
  auto.
Qed.

Lemma mem_union : forall ns1 ns2 x,
                    NameSets.In x (NameSets.union ns1 ns2) <->
                    NameSets.In x ns1 \/ NameSets.In x ns2.
Proof.
  intros.
  split.
    intro.
    apply NameSets.F.mem_iff in H.
    rewrite NameSets.EP.union_mem in H.
    apply orb_true_iff in H.
    inversion H.
    left.
    apply NameSets.F.mem_iff; auto.
    right; apply NameSets.F.mem_iff; auto.

    intros.
    apply NameSets.F.mem_iff.
    rewrite NameSets.EP.union_mem.
    apply orb_true_iff.
    inversion H.
    left; apply NameSets.F.mem_iff; auto.
    right; apply NameSets.F.mem_iff; auto.
Qed.

Lemma mem_remove : forall x y ns,
                     NameSets.In x ns ->
                     NameSets.In x (NameSets.remove y ns) \/ x = y.
Proof.
  intros.
  apply NameSets.F.mem_iff in H.
  destruct (NameDecidableType.eq_dec x y).
    right; apply name_eq_iff in e; auto.
    left.
    apply NameSets.F.mem_iff.
    rewrite <- H.
    apply NameSets.EP.remove_mem_2.
    unfold NameDecidableType.eq in n.
    destruct x, y.
    auto.
Qed.

Lemma inter_empty_not_mem' : forall ns1 ns2 x y,
                              NameSets.inter ns1 ns2 = NameSets.empty ->
                              NameSets.mem x ns1 = true ->
                              NameSets.mem y ns2 = true ->
                              x <> y.
Proof.
Admitted.

Lemma inter_empty_1 : forall ns1 ns2 x,
                        NameSets.inter (NameSets.add x ns1) ns2 = NameSets.empty ->
                        NameSets.inter ns1 ns2 = NameSets.empty.
Proof.
  (* induction ns1, ns2; destruct x; intros. *)
  (*   compute; auto. *)
  (*   simpl; unfold NameSets.empty; auto. *)
  (*   compute. *)
  (*   compute in H. *)
  (*   auto. *)
  (*   destruct a, e. *)
  (*   unfold NameSets.inter in H. *)
  (*   unfold NameSets.inter. *)
  (*   simpl in H. *)
  (*   simpl. *)

  (*   compute. *)
  (*   compute in H. *)
Admitted.

Lemma empty_mem_false : forall ns,
                          NameSets.Empty ns ->
                          forall x, ~ NameSets.In x ns.
Proof.
  intros.
  intro.
  apply NameSets.F.is_empty_iff in H.
  apply NameSets.F.mem_iff in H0.
  rewrite NameSets.EP.is_empty_equal_empty in H.
  apply NameSets.F.equal_iff in H.
  setoid_rewrite H in H0.
  compute in H0.
  discriminate.
Qed.

Lemma inter_empty_not_mem : forall ns1 ns2 x,
                                NameSets.Empty (NameSets.inter ns1 ns2)->
                                NameSets.In x ns1 ->
                                ~ NameSets.In x ns2.
Proof.
  intros.
  intro.
  apply NameSets.F.mem_iff in H0.
  apply NameSets.F.mem_iff in H1.
  assert (NameSets.mem x (NameSets.inter ns1 ns2) = true).
    rewrite NameSets.EP.inter_mem.
    rewrite andb_true_iff.
    split; auto.
    apply NameSets.P.empty_is_empty_1 in H.
    setoid_rewrite H in H2.
    compute in H2.
    discriminate.
Qed.

Lemma inter_head : forall ns1 ns2 x, NameSets.Equal (NameSets.inter (NameSets.add x ns1) (NameSets.add x ns2)) (NameSets.add x (NameSets.inter ns1 ns2)).
Proof.
  intros.
  destruct (NameSets.P.In_dec x ns2).
  rewrite (NameSets.P.add_equal i).
  apply NameSets.P.inter_add_1.
  auto.
  setoid_rewrite NameSets.P.inter_sym.
  destruct (NameSets.P.In_dec x ns1).
  rewrite (NameSets.P.add_equal i).
  apply NameSets.P.inter_add_1.
  auto.
  setoid_rewrite NameSets.P.inter_sym.
  elim ns1 using NameSets.P.set_induction.
    intros.
    apply NameSets.P.empty_is_empty_1 in H.
    setoid_rewrite H.
    elim ns2 using NameSets.P.set_induction.
      intros.
      apply NameSets.P.empty_is_empty_1 in H0.
      setoid_rewrite H0.
      (* setoid_rewrite NameSets.EP. *)





Admitted.

Lemma add_not_empty : forall x ns, ~ NameSets.Empty (NameSets.add x ns).
Proof.
  intros.
  intro.
  elim ns using NameSets.P.set_induction.
  intros.
Admitted.


Lemma inter_head_not_empty :
  forall ns1 ns2 x, ~ NameSets.Empty (NameSets.inter (NameSets.add x ns1) (NameSets.add x ns2)).
Proof.
  intros.
  intro.
  setoid_rewrite inter_head in H.


  assert (forall ns, NameSets.Equal (NameSets.inter ns ns) ns).
    intro.
    apply NameSets.P.inter_subset_equal.
    apply NameSets.P.subset_refl.
Admitted.

Lemma union_add_singleton :
  forall x y, NameSets.Equal (NameSets.union (NameSets.singleton x) (NameSets.singleton y))
                    (NameSets.add x (NameSets.singleton y)).
Admitted.

Lemma add_join : forall x s, NameSets.Equal
                               (NameSets.add x (NameSets.add x s))
                               (NameSets.add x s).
Proof.
  intros.
  assert (NameSets.In x (NameSets.add x s)).
    apply NameSets.F.add_1.
    destruct x; auto.
  setoid_rewrite (NameSets.P.add_equal H).
  apply NameSets.P.equal_refl.
Qed.

Lemma add_in : forall x y s, NameSets.In x (NameSets.add y s) ->
                             x = y \/
                             NameSets.In x s.
Proof.
  intros.
  destruct (NameDecidableType.eq_dec y x).
    apply NameDecidableType.name_sym in e.
    unfold NameDecidableType.eq in e.
    destruct x, y.
    left; rewrite e; auto.

    right.
    apply NameSets.F.add_3 with (s := s) in n.
      auto.
      auto.
Qed.

Lemma remove_in : forall x y s, NameSets.In x (NameSets.remove y s) ->
                                x <> y /\
                                NameSets.In x s.
Proof.
  intros.
  split.
  intro.
  assert (NameDecidableType.eq y x).
    rewrite H0.
    apply NameDecidableType.name_refl.
  eapply NameSets.F.remove_1 in H1.
  apply H1.
  apply H.
  apply NameSets.F.remove_3 in H.
  auto.
Qed.

Lemma inter_empty : forall s1 s2,
                      NameSets.Empty (NameSets.inter s1 s2) ->
                      forall x,
                        (NameSets.In x s1 -> ~ NameSets.In x s2) /\
                        (NameSets.In x s2 -> ~ NameSets.In x s1).
Proof.
  intros.
  unfold NameSets.Empty in H.
  specialize (H x).
  split; intro; intro.
    apply H.
    eapply NameSets.F.inter_3; auto.

    apply H.
    eapply NameSets.F.inter_3; auto.
Qed.
