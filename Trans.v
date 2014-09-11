Require Import Names Fun Sets Config.

Module L := List.
Module V := Vector.

Inductive action : Set :=
| silent : action
| free_out : name -> name -> action
| bound_out : name -> name -> action
| free_inp : name -> name -> action
| bound_inp : name -> name -> action.

Hint Constructors action.

Inductive not_silent : action -> Prop :=
| not_silent_free_out : forall x y, not_silent (free_out x y)
| not_silent_bound_out : forall x y, not_silent (bound_out x y)
| not_silent_free_inp : forall x y, not_silent (free_inp x y)
| not_silent_bound_inp : forall x y, not_silent (bound_inp x y).

Hint Constructors not_silent.

Definition action_names (a : action) : NameSets.t :=
  match a with
    | silent => NameSets.empty
    | free_out n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | bound_out n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | free_inp n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | bound_inp n1 n2 => NameSets.add n1 (NameSets.singleton n2)
  end.

Fixpoint action_bound_names (a : action) : NameSets.t. Admitted.

Inductive ActionBoundName (x : name) : action -> Prop :=
| out_bound : forall y, ActionBoundName x (bound_out y x)
| inp_bound : forall y, ActionBoundName x (bound_inp y x).

Hint Constructors ActionBoundName.

(* もし x == z なら、y に入れ替えて、違うならそのまま *)
Definition replace (x y z : name) : name :=
  if beq_name x z then y else z.

Definition replace_vect (x y : name) {n : nat} (v : V.t name n) : V.t name n :=
  V.map (replace x y) v.

Open Scope bool_scope.

Fixpoint inb_vect (x : name) {n : nat} (v : V.t name n) : bool :=
  match v with
    | V.nil => false
    | V.cons y _ v' => (beq_name x y) || (inb_vect x v')
  end.

Fixpoint substitute (x y : name) (c : config) : config :=
  match c with
    | nil => nil
    | create n1 n2 c' =>
      create (replace x y n1) n2
             (if beq_name x n2 then
                c'
              else
                (substitute x y c'))
    | send n1 n2 => send (replace x y n1) (replace x y n2)
    | restrict n c' => restrict (replace x y n) (substitute x y c')
    | compose c1 c2 => compose (substitute x y c1) (substitute x y c2)
    | caseof n l => caseof (replace x y n)
                           (List.map (fun p => (replace x y (fst p), substitute x y (snd p))) l)
    | instantiate_1 num x' ys z p u vs =>
      instantiate_1 num x' ys z
                    (if beq_name x x' || inb_vect x ys || beq_name x z then
                       p
                     else
                       (substitute x y p))
                    (replace x y u) (replace_vect x y vs)
    | instantiate_2 num x1 x2 ys z p u1 u2 vs =>
      instantiate_2 num x1 x2 ys z
                    (if beq_name x x1 || beq_name x x2 || inb_vect x ys || beq_name x z then
                       p
                     else
                       (substitute x y p))
                    (replace x y u1) (replace x y u2) (replace_vect x y vs)
  end.

Notation "c { y / x }" := (substitute x y c) (at level 0, y at level 0).

Definition substitute_vect {n : nat} (xs ys : V.t name n) (c : config) : config :=
  V.fold_right2 substitute xs ys c.

Notation "c { ys // xs }" := (substitute_vect xs ys c) (at level 0, ys at level 0).

Reserved Notation "p == a ==> q" (at level 40).

Inductive trans : config -> action -> config -> Prop :=
| INP : forall (x y z : name) (p : config),
          create x y p == free_inp x z ==> (p { z / y })
| OUT : forall x y : name,
          send x y == free_out x y ==> nil
| BINP : forall (x y : name) (p p' : config),
           p == free_inp x y ==> p' ->
           ~ ConfigFreeName y p ->
           p == bound_inp x y ==> p'
| RES : forall (y : name) (p p' : config) (a : action),
          not_silent a ->
          p == a ==> p' ->
          NameSets.mem y (action_names a) = false ->
          restrict y p == a ==> restrict y p'
| OPEN : forall (x y : name) (p p' : config),
           p == free_out x y ==> p' ->
           x <> y ->
           restrict y p == bound_out x y ==> p'
| PAR : forall (a : action) (p1 p1' p2 : config),
          p1 == a ==> p1' ->
          (forall x, (ActionBoundName x a -> ~ ConfigFreeName x p2) /\
                     (ConfigFreeName x p2 -> ~ ActionBoundName x a)) ->
          compose p1 p2 == a ==> compose p1' p2
| COM : forall (x y : name) (p1 p1' p2 p2' : config),
          p1 == free_out x y ==> p1' ->
          p2 == free_inp x y ==> p2' ->
          compose p1 p2 == silent ==> compose p1' p2'
| CLOSE : forall (x y : name) (p1 p1' p2 p2' : config),
            p1 == bound_out x y ==> p2 ->
            p2 == free_inp x y ==> p2' ->
            ~ ConfigFreeName y p2 ->
            compose p1 p2 == silent ==> restrict y (compose p1' p2')
| BRNCH : forall (x : name) (l : list (name * config)) (n : nat),
            Some x = L.nth_error (L.map (fun p => fst p) l) n ->
            caseof x l == silent ==> L.nth n (L.map (fun p => snd p) l) nil
| BEHV_1 : forall n x1 (ys : V.t name n) z p u1 vs a p',
             create u1 z ((p { u1 / x1 }) { vs // ys }) == a ==> p' ->
             instantiate_1 n x1 ys z p u1 vs == a ==> p'
| BEHV_2 : forall n x1 x2 (ys : V.t name n) z p u1 u2 vs a p',
             create u1 z (((p { u1 / x1 }) { u2 / x2 }) { vs // ys }) == a ==> p' ->
             instantiate_2 n x1 x2 ys z p u1 u2 vs == a ==> p'
where "p == a ==> q" := (trans p a q).

Hint Constructors trans.
