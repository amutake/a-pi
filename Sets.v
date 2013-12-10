Require Import
        Coq.MSets.MSets Coq.Arith.Peano_dec Coq.Arith.Compare_dec Coq.Arith.EqNat.

Inductive name :=
  | name_cons : nat -> name.

Definition beq_name (n1 n2 : name) : bool :=
  match n1, n2 with
    | name_cons n1', name_cons n2' => beq_nat n1' n2'
  end.

Inductive star :=
  | star_name : name -> star
  | star_bottom : star
  | star_star : star.

Definition beq_star (s1 s2 : star) : bool :=
  match s1, s2 with
    | star_name n1, star_name n2 => beq_name n1 n2
    | star_bottom, star_bottom => true
    | star_star, star_star => true
    | _, _ => false
  end.

Module NameDecidableType <: DecidableType.

  Definition t := name.
  Definition eq (name1 name2 : name) :=
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
    rewrite H; rewrite H0; auto.
  Qed.
  Definition eq_equiv :=
    Build_Equivalence t eq name_refl name_sym name_trans.
  Definition eq_dec (x y : t) : {eq x y} + {~ eq x y} :=
    match x, y with
      | name_cons x', name_cons y' => eq_nat_dec x' y'
    end.
End NameDecidableType.

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

Module NameSets := MSetWeakList.MakeRaw(NameDecidableType).
Module StarSets := MSetWeakList.MakeRaw(StarDecidableType).
