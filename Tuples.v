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

  Fixpoint ch {n : nat} (ntup : tn n) : function (to_set ntup) :=
    fun x : name =>
      match lookup x ntup with
        | None => None
        | Some n' => if beq_nat (n - 1) n'
                     then Some star_bottom
                     else match nth_option ntup (n' + 1) with
                            | None => None
                            | Some na => Some (star_name na)
                          end
      end.

  Goal forall (x : name), ch (nil name) x = None.
  Proof. auto. Qed.

  Goal forall (x : name), ch (Tuple.singleton x) x = Some star_bottom.
  Proof.
    intros.
    destruct x.
    induction n.
      auto.
      simpl.
      rewrite <- beq_nat_refl.
      auto.
  Qed.

  Goal forall (x y z : name), ch (add x (add y (add z empty))) x = Some (star_name y).
  Proof.
    intros.
    induction x.
    induction n.
    auto.
    simpl.
    rewrite <- beq_nat_refl.
    simpl.
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
