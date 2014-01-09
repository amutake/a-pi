Require Import Names Fun Sets APi.

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
