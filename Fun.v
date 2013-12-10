Require Import Coq.Lists.List Sets.

Module Fun.

  Definition to_star (ns : NameSets.t) : StarSets.t :=
    StarSets.add star_bottom (StarSets.add star_star (map star_name ns)).

  Definition to_star' (ns : NameSets.t) : StarSets.t := map star_name ns.

  Definition temp_name_mapping := name -> option star.

  Definition temp_name_mapping_star := star -> option star.

  Definition to_star_function (f : temp_name_mapping) : temp_name_mapping_star :=
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

  Definition fun_plus (f1 : temp_name_mapping) (f2 : temp_name_mapping) : temp_name_mapping :=
    fun x : name =>
      match f1 x with
        | Some n => match n with
                      | star_bottom => match f2 x with
                                         | Some n' => Some n'
                                         | None => Some n
                                       end
                      | _ => Some n
                    end
        | None => f2 x
      end.

  (* f : rho -> rho*, fun_diff f rho' : (rho - rho') -> (rho - rho')* *)
  Definition fun_diff (f : temp_name_mapping) (ns : NameSets.t) : temp_name_mapping :=
    fun x : name =>
      match NameSets.mem x ns with
        | true => Some star_star
        | false => f x
      end.

  Definition fun_join (f : temp_name_mapping) : temp_name_mapping :=
    fun x : name =>
      match f x with
        | Some n => (to_star_function f) n
        | None => None
      end.

  Definition Fun_comm (f1 : temp_name_mapping) (f2 : temp_name_mapping) :=
    forall (x : name), fun_plus f1 f2 x = fun_plus f2 f1 x.

  Definition Fun_prop (f : temp_name_mapping) :=
    forall (x y : name),
      f x <> Some (star_name x) /\ (* f(x) /= x *)
      (f x = f y ->
       f x <> Some star_bottom ->
       f x <> Some star_star ->
       f y <> Some star_bottom ->
       f y <> Some star_star ->
       x = y) /\ (* f(x) = f(y) and is not member of {_|_, *} -> x = y *)
      fun_join f x = Some star_bottom.

  Record Compatible (f1 : temp_name_mapping) (f2 : temp_name_mapping) := Build_compatible {
    Compatible_comm : Fun_comm f1 f2;
    Compatible_prop : Fun_prop (fun_plus f1 f2)
  }.

  Definition empty : temp_name_mapping := fun _ => None.

End Fun.
