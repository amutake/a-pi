Require Import Coq.Logic.FunctionalExtensionality Sets Fun Tuples.

Inductive config : Set :=
  | nil : config
  | create : name -> name -> config -> config
  | send : name -> name -> config
  | restrict : name -> config -> config
  | compose : config -> config -> config.

Lemma diff_subset : forall (ns1 ns2 : NameSets.t),
  NameSets.subset (NameSets.diff ns1 ns2) ns1 = true.
Proof.
  intros.
  unfold NameSets.Ok.


  induction ns1.
    induction ns2.
      auto.

      assert (forall ns : NameSets.t, NameSets.diff Datatypes.nil ns = Datatypes.nil).
      intro.
      induction ns.
        auto.
        auto.
      rewrite H.
      auto.

    assert (forall (ns1 ns2 : NameSets.t) (x : name), NameSets.subset ns1 ns2 = true -> NameSets.subset ns1 (x :: ns2)%list = true).
    intros.
Admitted.

Reserved Notation "ns ';' f '|-' p" (at level 40).

Definition func := name -> option star.

Inductive typing : NameSets.t -> func -> config -> Prop :=
  | NIL : NameSets.empty ; empty |- nil
  | MSG : forall x y : name, NameSets.empty ; empty |- send x y
  | ACT : forall {ns : NameSets.t} (f : func) (p : config) (x y : name) (z : option name),
            ns ; f |- p ->
            NameSets.diff ns (NameSets.singleton x) = Option.to_set z ->
            NameSets.mem y ns = false ->
            (forall x' : name, NameSets.mem x ns = true -> Tuple.ch (Option.append (Tuple.singleton x) z) x' = f x') ->
            (forall x' : name, NameSets.mem x ns = false -> Tuple.ch (Option.to_tuple z) x' = f x') ->
            NameSets.union (NameSets.singleton x) (Option.to_set z) ; Tuple.ch (Option.append (Tuple.singleton x) z) |- create x y p
  | COMP : forall (ns1 ns2 : NameSets.t) (f1 : func) (f2 : func) (p1 p2 : config),
             ns1 ; f1 |- p1 ->
             ns2 ; f2 |- p2 ->
             NameSets.inter ns1 ns2 = NameSets.empty ->
             NameSets.union ns1 ns2 ; fun_plus f1 f2 |- compose p1 p2
  | RES : forall (ns : NameSets.t) (f : func) (p : config) (x : name),
            ns ; f |- p ->
            NameSets.diff ns (NameSets.singleton x) ; fun_diff' f (NameSets.diff ns (NameSets.singleton x)) |- restrict x p
  where "ns ';' f '|-' p" := (typing ns f p).

Goal exists (ns : NameSets.t) (f : function ns), ns ; f |- create (name_cons 0) (name_cons 1) nil.
Proof.
  exists (NameSets.singleton (name_cons 0)).
  exists (fun x => match x with
                     | name_cons 0 => Some star_bottom
                     | _ => None
                   end).
  assert (NameSets.singleton (name_cons 0) = NameSets.union (NameSets.singleton (name_cons 0)) (Option.to_set None)).
    auto.
  assert (forall x : name,
            (fun x : name =>
               match x with
                 | name_cons 0 => Some star_bottom
                 | name_cons (S _) => None
               end) x =
            Tuple.ch (Option.append (Tuple.singleton (name_cons 0)) None) x).
    intros.
    induction x.
    induction n.
      auto.
      auto.
  apply functional_extensionality in H0.

  rewrite H.
  rewrite H0.

  eapply ACT with (x := name_cons 0) (y := name_cons 1) (z := None) (p := nil) (f := Fun.empty).
  apply NIL.
  auto.
  auto.
  intros.
  inversion H1.
  intros.
  auto.
Qed.

Goal forall (ns : NameSets.t) (f : function ns), ~ ns ; f |- compose (create (name_cons 0) (name_cons 1) nil) (create (name_cons 0) (name_cons 2) nil).
Proof.
  unfold not.
  intros.
Admitted.

Goal exists (ns : NameSets.t) (f : function ns), ns ; f |- compose (create (name_cons 0) (name_cons 1) nil) (create (name_cons 2) (name_cons 3) nil).
Proof.
  exists (NameSets.add (name_cons 0) (NameSets.singleton (name_cons 2))).
  exists (fun x : name => match x with
                            | name_cons 0 => Some star_bottom
                            | name_cons 2 => Some star_bottom
                            | _ => None
                          end).
  assert (NameSets.add (name_cons 0) (NameSets.singleton (name_cons 2)) = NameSets.union (NameSets.singleton (name_cons 0)) (NameSets.singleton (name_cons 2))).
  auto.
  assert (forall x : name,
            (fun x : name => match x with
                               | name_cons 0 => Some star_bottom
                               | name_cons 2 => Some star_bottom
                               | _ => None
                             end) x =
            Fun.fun_plus (ns1 := (NameSets.singleton (name_cons 0))) (ns2 := NameSets.singleton (name_cons 2)) (fun x => match x with
                                     | name_cons 0 => Some star_bottom
                                     | _ => None
                                   end)
                         (fun x => match x with
                                     | name_cons 2 => Some star_bottom
                                     | _ => None
                                   end) x).
    intros.
    induction x.
      induction n.
        unfold fun_plus.
        simpl.
        compute.
        destruct NameDecidableType.eq_dec.
          auto.
          assert (NameDecidableType.eq (name_cons 0) (name_cons 0)).
            compute; auto.
          apply n in H0.
          inversion H0.
Admitted.


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

Fixpoint config_names (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create n1 n2 c' => NameSets.add n1 (NameSets.add n2 (config_names c'))
    | send n1 n2 => NameSets.add n1 (NameSets.singleton n2)
    | restrict n c' => NameSets.add n (config_names c')
    | compose c1 c2 => NameSets.union (config_names c1) (config_names c2)
  end.

Fixpoint config_free_names' (bounded : NameSets.t) (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create n1 n2 c' => if NameSets.mem n1 bounded
                         then (config_free_names' (NameSets.add n2 bounded) c')
                         else NameSets.add n1 (config_free_names' (NameSets.add n2 bounded) c')
    | send n1 n2 => if NameSets.mem n1 bounded
                    then NameSets.empty
                    else NameSets.singleton n1
    | restrict n c' => config_free_names' (NameSets.add n bounded) c'
    | compose c1 c2 => NameSets.union (config_free_names' bounded c1) (config_free_names' bounded c2)
  end.

Definition config_free_names (c : config) : NameSets.t := config_free_names' NameSets.empty c.

Goal forall x y : name, config_free_names (send x y) = NameSets.singleton x.
Proof.
  intros.
  unfold config_free_names.
  auto.
Qed.

Fixpoint config_bound_names (c : config) : NameSets.t :=
  match c with
    | nil => NameSets.empty
    | create _ n c' => NameSets.add n (config_bound_names c')
    | send _ _ => NameSets.empty
    | restrict n c' => NameSets.add n (config_bound_names c')
    | compose c1 c2 => NameSets.union (config_bound_names c1) (config_bound_names c2)
  end.

Definition ConfigSubset {ns : NameSets.t} {f : function ns} {p : config} (ty : ns ; f |- p) : Prop :=
  NameSets.subset ns (config_free_names p) = true.

Lemma config_subset : forall (ns : NameSets.t) (f : function ns) (p : config) (ty : ns ; f |- p), ConfigSubset ty.
Proof.
  intros.
  unfold ConfigSubset.
  unfold config_free_names.
  induction ty.
    auto.

    auto.

Admitted.

Definition FunctionProperty {ns : NameSets.t} {f : function ns} {p : config} (ty : ns ; f |- p) : Prop :=
  Fun_prop f.

Lemma function_property : forall (ns : NameSets.t) (f : function ns) (p : config) (ty : ns ; f |- p), FunctionProperty ty.
Proof.
  unfold FunctionProperty.
  unfold Fun_prop.
  intros.
  induction ty.
    inversion H2.

    inversion H2.

    apply IHty.
Admitted.


Definition Uniqueness {ns : NameSets.t} {f : function ns} {p : config} (ty : ns ; f |- p) : Prop :=
  forall (ns' : NameSets.t) (f' : function ns'),
    ns' ; f' |- p -> ns = ns' /\ f = f'.

Lemma uniqueness : forall (ns : NameSets.t) (f : function ns) (p : config) (ty : ns ; f |- p), Uniqueness ty.
Proof.
  unfold Uniqueness.
  intros.
  remember p.
  split.
  induction ty.
    inversion H.
    induction H.
      auto.
      auto.


      rewrite <- IHtyping in H0.
      rewrite <- IHtyping in H1.

      assert (Option.to_set z = NameSets.empty).
      compute in H0.
      unfold NameSets.empty.
      rewrite

Theorem Soundness : forall (ns : NameSets.t) (f : function ns) (p : config) (ty : ns ; f |- p),
                      ConfigSubset ty /\ FunctionProperty ty /\ Uniqueness ty.
Proof.
  intros.
  split.
  apply config_subset.
  split.
  apply function_property.
  apply uniqueness.
Qed.

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
