Require Import Coq.Arith.EqNat Coq.Vectors.Vector Sets Fun.

Module Tuple.

  Definition tn := Vector.t name.

  Definition singleton (n : name) : tn 1 :=
    cons name n 0 (nil name).

  Fixpoint to_set {n : nat} (ntup : tn n) : NameSets.t :=
    match ntup with
      | nil => NameSets.empty
      | cons n _ t => NameSets.add n (to_set t)
    end.

  Definition append {p q : nat} (vp : tn p) (vq : tn q) := Vector.append vp vq.

  Fixpoint lookup {n : nat} (a : name) (v : tn n) : option nat :=
    match v with
      | nil => None
      | cons n _ v' => if beq_name a n
                       then Some 0
                       else option_map S (lookup a v')
    end.

  Definition add {p : nat} (n : name) (v : tn p) := Vector.cons name n p v.

  Definition empty := Vector.nil name.

  Goal lookup (name_cons 0) (add (name_cons 0) (add (name_cons 1) empty)) = Some 0.
  Proof. auto. Qed.
  Goal lookup (name_cons 1)
       (add (name_cons 0)
            (add (name_cons 1)
                 (add (name_cons 2) empty))) = Some 1.
  Proof. auto. Qed.
  Goal lookup (name_cons 2)
       (add (name_cons 0)
            (add (name_cons 1) empty)) = None.
  Proof. auto. Qed.

  Fixpoint nth_option {n : nat} (v : tn n) (num : nat) : option name :=
    match num with
      | O => match v with
               | nil => None
               | cons na _ _ => Some na
             end
      | S num' => match v with
                    | nil => None
                    | cons _ _ v' => nth_option v' num'
                  end
    end.

  Definition ch {n : nat} (ntup : tn n) : Fun.temp_name_mapping :=
    fun x : name =>
      match lookup x ntup with
        | None => None
        | Some n' => if beq_nat (pred n) n'
                     then Some star_bottom
                     else match nth_option ntup (S n') with
                            | None => None
                            | Some na => Some (star_name na)
                          end
      end.

  Lemma ch_S : forall x y, ch (singleton (name_cons x)) (name_cons y) =
                         ch (singleton (name_cons (S x))) (name_cons (S y)).
  Proof.
    compute.
    auto.
  Qed.

  Goal forall (x : name), ch (nil name) x = None.
  Proof. auto. Qed.

  Goal forall (x : name), ch (Tuple.singleton x) x = Some star_bottom.
  Proof.
    intros.
    destruct x.
    induction n.
      auto.
      compute.
      rewrite <- beq_nat_refl.
      auto.
  Qed.

  Goal forall (x y z : name), ch (add x (add y (add z empty))) x = Some (star_name y).
  Proof.
    intros.
    induction x.
      induction n.
        auto.
        compute.
        rewrite <- beq_nat_refl.
        auto.
  Qed.

  Lemma name_S : forall x y, name_cons (S x) = name_cons (S y) <-> name_cons x = name_cons y.
  Proof.
    induction x; induction y; split; intros; auto; try discriminate; try (inversion H; auto).
  Qed.

  Lemma name_cons_prop : forall n m, name_cons n = name_cons m <-> n = m.
  Proof.
    split; induction n, m; intros; auto; try discriminate; try (inversion H; auto).
  Qed.

  Lemma ch_singleton_None : forall (x y : name), x <> y -> ch (singleton x) y = None.
  Proof.
    unfold not.
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
        rewrite <- ch_S.
        apply IHn.
        intro.
        apply H.
        apply name_S.
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

  Definition to_tuple (t' : t) : Tuple.tn (length t') :=
    match t' with
      | None => nil name
      | Some n => cons name n 0 (nil name)
    end.

  Definition append {p : nat} (v : Tuple.tn p) (t' : t) : Tuple.tn (p + length t') :=
    Tuple.append v (to_tuple t').

End Option.
