Require Import Coq.Lists.List Coq.Logic.FunctionalExtensionality Names.

Inductive tmp_fun : Type :=
  | ch_0 : tmp_fun
  | ch_1 : name -> tmp_fun
  | ch_2 : forall x y : name, x <> y -> tmp_fun
  | fun_plus : tmp_fun -> tmp_fun -> tmp_fun
  | fun_remove : name -> tmp_fun -> tmp_fun.

Inductive domain (x : name) : tmp_fun -> Prop :=
  | domain_ch_1 : domain x (ch_1 x)
  | domain_ch_2 : forall y p, domain x (ch_2 x y p)
  | domain_ch_2' : forall y p, domain x (ch_2 y x p)
  | domain_fun_plus_l : forall f g, domain x f -> domain x (fun_plus f g)
  | domain_fun_plus_r : forall f g, domain x g -> domain x (fun_plus f g)
  | domain_fun_remove : forall f y, domain x f -> x <> y -> domain x (fun_remove y f).

Inductive is_hidden (x : name) : tmp_fun -> Prop :=
  | hidden_here : forall f, is_hidden x (fun_remove x f)
  | hidden_there : forall f g, is_hidden x f -> is_hidden x (fun_plus f g).

Inductive range (x : name) : tmp_fun -> Prop :=
  | range_ch_2 : forall y p, range x (ch_2 y x p)
  | range_fun_plus_l : forall f g, range x f -> range x (fun_plus f g)
  | range_fun_plus_r : forall f g, range x g -> range x (fun_plus f g)
  | range_fun_remove : forall f y, range x f -> x <> y -> range x (fun_remove y f).




  Definition range f x := exists y : name, f y = Some (star_name x).

  Definition range_domain f := forall x, range f x -> domain f x.
