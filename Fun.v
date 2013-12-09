Require Import Coq.Lists.List Sets.

Definition to_star (ns : NameSets.t) : StarSets.t :=
  StarSets.add star_bottom (StarSets.add star_star (map star_name ns)).

Definition to_star' (ns : NameSets.t) : StarSets.t := map star_name ns.

Definition function (ns : NameSets.t) := name -> option star.

Definition function_star (ss : StarSets.t) := star -> option star.

Definition to_star_function {ns : NameSets.t} (f : function ns) : function_star (to_star ns) :=
  fun s : star =>
    match s with
      | star_name n => f n
      | _ => Some star_bottom
    end.

Definition beq_option_star (o1 : option star) (o2 : option star) : bool :=
  match o1, o2 with
    | Some s1, Some s2 => beq_star s1 s2
    | _, _ => false
  end.

Definition fun_plus {ns1 ns2 : NameSets.t} (f1 : function ns1) (f2 : function ns2) : function (NameSets.union ns1 ns2) :=
  fun x : name =>
    if andb (NameSets.mem x ns1) (beq_option_star (f1 x) (Some star_bottom) || negb (NameSets.mem x ns2))
    then f1 x
    else f2 x.

Definition fun_diff {ns1 : NameSets.t} (f : function ns1) (ns : NameSets.t) (_ : NameSets.subset ns ns1 = true) : function ns :=
  fun x : name =>
    match f x with
      | Some n => if StarSets.mem n (to_star' (NameSets.diff ns1 ns))
                  then Some star_star
                  else f x
      | None => None
    end.

Definition fun_diff' {ns1 : NameSets.t} (f : function ns1) (ns : NameSets.t) : function ns :=
  fun x : name =>
    match f x with
      | Some n => if StarSets.mem n (to_star' (NameSets.diff ns1 ns))
                  then Some star_star
                  else f x
      | None => None
    end.

Definition fun_join {ns : NameSets.t} (f : function ns) : function ns :=
  fun x : name =>
    match f x with
      | Some n => (to_star_function f) n
      | None => None
    end.

Definition Fun_comm {ns1 ns2 : NameSets.t} (f1 : function ns1) (f2 : function ns2) :=
  forall (x : name), fun_plus f1 f2 x = fun_plus f2 f1 x.

Definition Fun_prop {ns : NameSets.t} (f : function ns) :=
  forall (x y : name),
    NameSets.mem x ns = true ->
    NameSets.mem y ns = true ->
    f x <> Some (star_name x) ->
    fun_join f x = Some star_bottom ->
    f x = f y ->
    f x <> Some star_bottom ->
    f x <> Some star_star ->
    f y <> Some star_bottom ->
    f y <> Some star_star ->
    x = y.

Definition Fun_plus_prop {ns1 ns2 : NameSets.t} (f1 : function ns1) (f2 : function ns2) :=
  forall (x y : name), NameSets.mem x (NameSets.union ns1 ns2) = true ->
                       NameSets.mem y (NameSets.union ns1 ns2) = true ->
                       (fun_plus f1 f2) x <> Some (star_name x) ->
                       (fun_join (fun_plus f1 f2)) x = Some star_bottom ->
                       (fun_plus f1 f2) x = (fun_plus f1 f2) y ->
                       (fun_plus f1 f2) x <> Some star_bottom ->
                       (fun_plus f1 f2) x <> Some star_star ->
                       (fun_plus f1 f2) y <> Some star_bottom ->
                       (fun_plus f1 f2) y <> Some star_star ->
                       x = y.

Record Compatible {ns1 ns2 : NameSets.t} (f1 : function ns1) (f2 : function ns2) := Build_compatible {
  Compatible_comm : Fun_comm f1 f2;
  Compatible_prop : Fun_plus_prop f1 f2
}.

Definition empty : function NameSets.empty := fun _ => None.


(* Definition f (n : name) : star. Admitted. *)
(*   (* match temporary n with *) *)
(*   (*   | *) *)

(* Definition F := *)
(*   fun (nset : NameSets.t) (sset : StarSets.t) (n : name) (s : star) *)
(*     (p : NameSets.mem n nset = true) (q : StarSets.mem s sset = true) => s. *)
(* Definition F_star := star -> star. *)


(* Definition function (ns : NameSets.t) := forall (n : name), NameSets.mem n ns = true -> star. *)


(* Inductive function : NameSets.t -> Type := *)
(*   | empty : function NameSets.empty *)
(*   | cons : forall (n : name) (ns : NameSets.t) (s : star), *)
(*              NameSets.mem n ns = false -> StarSets.mem s (to_star ns) = true -> *)
(*              function ns -> function (NameSets.add n ns). *)

(* Fixpoint apply (ns : NameSets.t) (f : function ns) (n : name) : option star := *)
(*   match f with *)
(*     | empty => None *)
(*     | cons n' ns' s _ _ f' => if beq_name n n' then Some s else apply ns' f' n *)
(*   end. *)

(* Fixpoint fun_plus (ns1 ns2 : NameSets.t) (f1 : function ns1) (f2 : function ns2) : function (NameSets.union ns1 ns2) := *)
(*   match f1 with *)
(*     | empty => f2 *)
(*     | cons n' ns1' _ f1' s' => *)


(* Definition fun_plus (ns1 ns2 : NameSets.t) (f1 : function ns1) (f2 : function ns2) : function (NameSets.union ns1 ns2) := Function (fun x => *)
(*     if NameSets.mem x ns1 /\ (beq_star (apply ns1 f1 x) \/ ~ NameSets.mem x ns2) *)
(*     then *)



(* Definition emptyF : F := *)
