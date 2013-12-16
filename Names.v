Require Import Coq.Arith.EqNat Coq.MSets.MSets Coq.Arith.Peano_dec.

Inductive name :=
  | name_cons : nat -> name.

Lemma name_S : forall x y, name_cons (S x) = name_cons (S y) <-> name_cons x = name_cons y.
Proof.
  induction x; induction y; split; intros; auto; try discriminate; try (inversion H; auto).
Qed.

Lemma name_cons_prop : forall n m, name_cons n = name_cons m <-> n = m.
Proof.
  split; induction n, m; intros; auto; try discriminate; try (inversion H; auto).
Qed.

Definition beq_name (n1 n2 : name) : bool :=
  match n1, n2 with
    | name_cons n1', name_cons n2' => beq_nat n1' n2'
  end.

Lemma beq_name_refl : forall x, beq_name x x = true.
Proof.
  destruct x.
  simpl.
  rewrite <- beq_nat_refl.
  auto.
Qed.

Lemma beq_name_true_iff : forall x y, beq_name x y = true <-> x = y.
Proof.
  destruct x, y.
  simpl.
  split.
    intro.
    apply beq_nat_true in H.
    rewrite H.
    auto.

    intro.
    apply beq_nat_true_iff.
    apply name_cons_prop in H.
    auto.
Qed.

Lemma beq_name_false_iff : forall x y, beq_name x y = false <-> x <> y.
Proof.
  destruct x, y.
  simpl.
  split.
    intro.
    apply beq_nat_false_iff in H.
    intro.
    apply name_cons_prop in H0.
    auto.

    intro.
    apply beq_nat_false_iff.
    intro.
    rewrite H0 in H.
    apply H.
    auto.
Qed.

Lemma beq_name_sym : forall x y, beq_name x y = beq_name y x.
Proof.
  intros.
  destruct (beq_name x y) eqn:?.
  symmetry.
  apply beq_name_true_iff.
  apply beq_name_true_iff in Heqb.
  auto.

  symmetry.
  apply beq_name_false_iff.
  apply beq_name_false_iff in Heqb.
  intro.
  rewrite H in Heqb.
  auto.
Qed.

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

  (* Definition eq (name1 name2 : name) := name1 = name2. *)
  (*   (* match name1, name2 with *) *)
  (*   (*   | name_cons n1, name_cons n2 => n1 = n2 *) *)
  (*   (* end. *) *)
  (* Lemma name_refl : Reflexive eq. *)
  (* Proof. *)
  (*   unfold Reflexive. *)
  (*   unfold eq. *)
  (*   auto. *)
  (* Qed. *)
  (* Lemma name_sym : Symmetric eq. *)
  (* Proof. *)
  (*   unfold Symmetric. *)
  (*   unfold eq. *)
  (*   auto. *)
  (* Qed. *)
  (* Lemma name_trans : Transitive eq. *)
  (* Proof. *)
  (*   unfold Transitive. *)
  (*   unfold eq. *)
  (*   intros. *)
  (*   rewrite H. *)
  (*   auto. *)
  (* Qed. *)
  (* Definition eq_equiv := *)
  (*   Build_Equivalence t eq name_refl name_sym name_trans. *)
  (* Theorem eq_dec : forall (x y : t), {eq x y} + {~ eq x y}. *)
  (* Proof. *)
  (*   destruct x, y. *)
  (*   unfold eq. *)
  (*   unfold not. *)
  (*   Set Printing All. *)
  (*   rewrite name_cons_prop. *)
  (*   generalize dependent n0. *)
  (*   induction n; induction n0. *)
  (*     left; auto. *)
  (*     right; intro; discriminate. *)
  (*     right; intro; discriminate. *)
  (*     assert ({name_cons n = name_cons n0} + {name_cons (S n) = name_cons (S n0) -> False} -> *)
  (*             {name_cons (S n) = name_cons (S n0)} + {name_cons (S n) = name_cons (S n0) -> False}). *)
  (*       intro. *)
  (*       inversion H. *)
  (*         left. *)
  (*         apply name_S; auto. *)
  (*         right; auto. *)
  (*     apply H. *)
  (*     assert ({name_cons n = name_cons n0} + {name_cons n = name_cons n0 -> False} -> *)
  (*             {name_cons n = name_cons n0} + {name_cons (S n) = name_cons (S n0) -> False}). *)
  (*       intro. *)
  (*       inversion H0. *)
  (*         left; auto. *)
  (*         right; intro. *)
  (*         apply name_S with n n0 in H2. *)
  (*         contradiction. *)
  (*     apply H0. *)
  (*     apply IHn. *)
  (* Qed. *)
