
Module iht.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf.
Require Import Omega.

Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive sumbool => bool [ true false ].
Extract Inductive sumor => option [ Some None ].


(* Each node can branch up to 2^t children *)
Definition t: nat := 8.
Extraction Inline t.
Lemma t_pos: 0 < t.
Proof. unfold t. omega. Qed.

(* No tree will ever have depth greater than D *)
Definition D: nat := 16.
Extraction Inline D.
Lemma D_pos: 0 < D.
Proof. unfold D. omega. Qed.

(* Here's a handy trick to avoid extracting more cruft: *)
Axiom nat_eq_dec: forall a b: nat, {a = b} + {a <> b}.
Extract Inlined Constant nat_eq_dec => "erlang~=:=".

(* Our key and value types *)
Inductive K: Type := mkk: forall {T: Type}, T -> K.
Inductive V: Type := mkv: forall {T: Type}, T -> V.

Axiom K_eq_dec: forall a b: K, {a = b} + {a <> b}.
Extract Inlined Constant K_eq_dec => "erlang~=:=".

(* Tuples play an important role in our theory *)
Axiom tuple: Type -> nat -> Type.
Definition valid_tup_addr q sz: Prop := 0 <= q < sz.


(* As do integers *)
Axiom int: Type.
Axiom int_eq_dec: forall (a b: int), {a = b} + {a <> b}.
Extract Inlined Constant int_eq_dec => "erlang~=:=".
Axiom int_zero: int.
Extract Inlined Constant int_zero => "0".
Axiom int_one: int.
Extract Inlined Constant int_one => "1".
Axiom int_two: int.
Extract Inlined Constant int_two => "2".
Parameter int_opp : int -> int.
Extract Inlined Constant int_opp => "erlang~-".
Axiom int_add: int -> int -> int.
Extract Inlined Constant int_add => "erlang~+".
Axiom int_sub: int -> int -> int.
Extract Inlined Constant int_sub => "erlang~-".
Axiom int_mul: int -> int -> int.
Extract Inlined Constant int_mul => "erlang~*".

Fixpoint int_of_nat z :=
  match z with
    | 0 => int_zero
    | S n => int_add int_one (int_of_nat n)
  end.

(* The actual erlang tuple-getter. Note that it has (q: int), not (q: nat). *)
Axiom prim_tup_get: forall {A T: Type}, int -> T -> A.
Extract Inlined Constant prim_tup_get => "erlang~element".

(* Our tuple-getter. Only job us to convert q into int from nat,
   and to add 1 since Erlang tuples index from 1 not 0. *)
Definition tup_get {A} {sz} (tup: tuple A sz) (q: nat) (pr: valid_tup_addr q sz): A
  := prim_tup_get (int_of_nat (S q)) tup.

(* The result of tup_get doesn't depend on the structure of the proof pr *)
Axiom tup_get_pr_irrel:
 forall {A} {sz} (tup: tuple A sz) q pr1 pr2,
  tup_get tup q pr1 = tup_get tup q pr2.

(* A predicate asserting the value held in a given position of a tuple *)
Definition tup_at_is {A} {sz} (tup: tuple A sz) q a (prq: valid_tup_addr q sz): Prop
 := tup_get tup q prq = a.

(* A predicate about the contents of a tuple after one of its entries has been modified *)
Inductive updated_tuple (A: Type) (sz: nat) (tup: tuple A sz) q a: Prop
 := updated: forall (tup': tuple A sz),
     (forall q' prq', q =  q' -> tup_at_is tup' q' a prq'
                   /\ q <> q' -> tup_at_is tup' q' (tup_get tup q' prq') prq' )
     -> updated_tuple A sz tup q a.

(* Appends one element to the right-hand-side of a tuple *)
Axiom erlang_append_element: forall {T A T'}, T -> A -> T'.
Extract Inlined Constant erlang_append_element => "erlang~append_element".
Definition tup_tcons {A} {sz} (tup: tuple A sz) (a: A): tuple A (S sz)
  := erlang_append_element tup a.

(* Some equational reasoning about tup_tcons... *)
Axiom tup_tcons_prop:
 forall {A} {sz} (tup: tuple A sz) a pr,
  tup_get (tup_tcons tup a) sz pr = a.
Axiom tup_tcons_prop':
 forall {A} {sz} (tup: tuple A sz) a q pr pr',
  tup_get (tup_tcons tup a) q pr = tup_get tup q pr'.

(* Addresses are tuples of prim_addrs. Each prim_addr designates a branch. *)
(* Inductive prim_addr: Type := pa: forall z, 0 <= z < 2^t -> prim_addr. *)
Inductive prim_addr: Type := pa: int -> prim_addr.
Program Definition pa_eq_dec (a b: prim_addr): {a = b} + {a <> b}
 := match a, b with
      | pa a', pa b' =>
         if int_eq_dec a' b'
          then left _
          else right _
    end.

(* Of course, one often wants to compare two (prim-)addr's for equality *)
(*
Program Definition pa_eq_dec (a b: prim_addr): {a = b} + {a <> b}
 := match a, b with
      | pa za pra, pa zb prb => if Z.eq_dec za zb then left _ else right _
    end.
Next Obligation.
  replace (conj l1 l2) with (conj l l0) by apply proof_irrelevance.
  trivial.
Defined.
*)

(* Our hash function requires a bit of extraction trickery: *)
Axiom erl_list: Type.
Axiom erl_binary: Type.

Axiom phash2: K -> int.
Extract Inlined Constant phash2 => "erlang~phash2".
Axiom integer_to_erl_list: int -> erl_list.
Extract Inlined Constant integer_to_erl_list => "erlang~integer_to_list".
Axiom md5: erl_list -> erl_binary.
Extract Inlined Constant md5 => "erlang~md5".
Axiom binary_to_erl_list: erl_binary -> erl_list.
Extract Inlined Constant binary_to_erl_list => "erlang~binary_to_list".
Axiom erl_list_to_tuple: erl_list -> tuple prim_addr D.
Extract Inlined Constant erl_list_to_tuple => "erlang~list_to_tuple".
(* End of said trickery. *)

(* And now we have our hash function. *)
Definition hash (k: K): tuple prim_addr D
 := let ph := phash2 k in
    let l := integer_to_erl_list ph in
    let m := md5 l in
    let b := binary_to_erl_list m in
    let t := erl_list_to_tuple b
    in t.

(* This is the location of the root of a hash tree. *)
Axiom top_loc: tuple prim_addr 0.
Extract Inlined Constant top_loc => "{}".

(* A predicate indicating when a tuple of prim_addr's is a prefix of (hash k). *)
Definition hash_prefix {d} k (loc: tuple prim_addr d): Prop
  := forall d' prd'1 prd'2,
      0 <= d' < d
      -> tup_get loc d' prd'1 = tup_get (hash k) d' prd'2.

(* Hash trees themselves. *)
Inductive hash_tree d (loc: tuple prim_addr d): Type
  := ht_none: hash_tree d loc
   | ht_pair: forall k,
      V
      -> 0 <= d <= D
      -> hash_prefix k loc
      -> hash_tree d loc
   | ht_bran:
      (forall a, hash_tree (S d) (tup_tcons loc a))
      -> 0 <= d < D
      -> hash_tree d loc.

(* The getter. This isn't meant to be called directly; see 'get'. *)
Program Fixpoint prim_get
 {d} {loc} (ht: hash_tree d loc) (prd: 0 <= d <= D) k h (prh: h = hash k) (prloc: hash_prefix k loc): option V
  := match ht with
       | ht_none => None
       | ht_pair k' v' prd' prloc =>
          if K_eq_dec k k'
           then Some v'
           else None
       | ht_bran f prd' => prim_get (f (tup_get h d _)) _ k h prh _
     end.
Next Obligation. unfold valid_tup_addr. omega. Defined.
Next Obligation. 
  unfold hash_prefix.
  intros.
  destruct (nat_eq_dec d' d).
  + subst.
    rewrite tup_tcons_prop.
    rewrite (tup_get_pr_irrel _ _ _ prd'2).
    destruct (tup_get (hash k) d prd'2).
    trivial.
  + assert (valid_tup_addr d' d).
    { unfold valid_tup_addr. omega. }
    rewrite (tup_tcons_prop' loc (tup_get (hash k) d _) _ prd'1 H0).
    apply prloc.
    apply H0.
Defined.

(* A predicate indicating the value of a tree at a given location. *)
Definition tree_at_is {d} {loc} (ht: hash_tree d loc) k v: Prop
 := forall prd h prh prloc, prim_get ht prd k h prh prloc = Some v.

(* A predicate about the contents of a tree after it has been updated. *)
Inductive updated_hash_tree d loc (ht: hash_tree d loc) k v: Type
 := updated_ht: forall (ht': hash_tree d loc),
     (forall k', k =  k' -> tree_at_is ht' k' v
              /\ k <> k' -> tree_at_is ht' k' v)
     -> updated_hash_tree d loc ht k v.

(* A predicate indicating that two non-equal K's have the same hash. *)
Inductive collides k: Type
 := collide: forall k',
     k <> k'
     -> (forall d pr, tup_get (hash k) d pr = tup_get (hash k') d pr)
     -> collides k.

(* Some obnoxiously-useful technical lemmas... *)
Lemma d_bounds:
 forall d, 0 <= d -> d <= D -> d <> D -> valid_tup_addr d D.
Proof. intros. unfold valid_tup_addr. omega. Qed.
Hint Resolve d_bounds.
Lemma d_bounds':
 forall d, 0 <= d -> d <= D -> d <> D -> 0 <= d < D.
Proof. intros. omega. Qed.
Hint Resolve d_bounds'.
Lemma d_bounds'':
 forall d, 0 <= d -> d <= D -> d <> D -> 0 <= S d <= D.
Proof. intros. omega. Qed.
Hint Resolve d_bounds''.
Lemma d_bounds''':
 forall d, 0 <= d -> d <= D -> d < D -> 0 <= S d <= D.
Proof. intros. omega. Qed.
Hint Resolve d_bounds'''.
(* End of the silly lemmas. *)

(* The prim_set function (below) is so complex that we
   wanted to wrap up all of its arguments in one structure: *)
Record set_args: Type
 := mk_set_args
     { d: nat
     ; loc: tuple prim_addr d
     ; k: K
     ; v: V
     ; h: tuple prim_addr D
     ; prd: 0 <= d <= D
     ; prloc: hash_prefix (d:=d) k loc
     ; prh: h = hash k
     ; ht: hash_tree d loc
     }.
Hint Resolve prd.
Hint Resolve prloc.
Hint Resolve prh.

(* The setter. Not meant to be called directly; see 'set'. *)
Program Fixpoint prim_set
 (sa: set_args) {measure (D - d sa)}
 : updated_hash_tree (d sa) (loc sa) (ht sa) (k sa) (v sa) + collides (k sa)
  := let _ht := ht sa in
     match _ht with
       | ht_none => inl (updated_ht _ _ (ht _) (k _) (v _) (ht_pair _ _ (k _) (v _) _ _) _)
       | ht_pair k' v' prd' pfx' =>
          if K_eq_dec (k sa) k'
           then inl (updated_ht _ _ (ht _) (k _) (v _) (ht_pair _ _ (k _) (v _) _ _) _)
           else if nat_eq_dec (d sa) D
                 then inr (collide (k _) k' _ _)
                 else let f a :=
                           if pa_eq_dec a (tup_get (h _) (d _) _)
                            then ht_pair (S (d _)) (tup_tcons (loc _) a) (k _) (v _) _ _
                      else if pa_eq_dec a (tup_get (hash k') (d sa) _)
                            then ht_pair (S (d _)) (tup_tcons (loc _) a) k' v' _ _
                            else ht_none (S (d _)) (tup_tcons (loc _) a)
                      in inl (updated_ht _ _ (ht _) (k _) (v _) (ht_bran (d _) (loc _) f _) _)
       | ht_bran f prd' =>
          let k_a := tup_get (h _) (d _) _ in
          let _ht := prim_set (mk_set_args _ _ (k _) (v _) (h _) _ _ (prh _) (f k_a))
          in match _ht with
               | inl (updated_ht ht' _) =>
                  let f' a: hash_tree (S (d _)) (tup_tcons (loc _) a)
                       := if pa_eq_dec a k_a then ht' else f a
                  in inl (updated_ht _ _ (ht _) (k _) (v _) (ht_bran _ _ f' _) _)
               | inr pr => inr pr
             end
     end.
Next Obligation.
  destruct sa.
  simpl in *.
  subst.
  transitivity (tup_get loc0 d0 pr).
  + symmetry.
    apply prloc0.
    apply pr.
  + apply pfx'.
    apply pr.
Defined.
Next Obligation.
  destruct sa.
  simpl in *.
  unfold hash_prefix.
  intros.
  destruct (nat_eq_dec d' d0).
  + subst d'.
    rewrite (tup_tcons_prop loc0 a prd'1).
    rewrite (tup_get_pr_irrel _ d0 _ prd'2) in H1.
    rewrite prh0 in H1.
    assumption.
  + assert (valid_tup_addr d' d0).
    { unfold valid_tup_addr. omega. }
    rewrite (tup_tcons_prop' loc0 a d' _ H3).
    apply prloc0.
    apply H3.
Defined.
Next Obligation.
  destruct sa.
  simpl in *.
  unfold hash_prefix.
  intros.
  destruct (nat_eq_dec d' d0).
  + subst d'.
    rewrite (tup_tcons_prop loc0 a prd'1).
    rewrite (tup_get_pr_irrel _ d0 _ prd'2) in H2.
    assumption.
  + assert (valid_tup_addr d' d0).
    { unfold valid_tup_addr. omega. }
    rewrite (tup_tcons_prop' loc0 a d' _ H4).
    apply pfx'.
    apply H4.
Defined.
Next Obligation. unfold valid_tup_addr. unfold prim_set_obligation_26. firstorder. Defined.
Next Obligation.
  destruct sa.
  simpl in *.
  unfold hash_prefix.
  intros.
  destruct (nat_eq_dec d' d0).
  + subst.
    rewrite (tup_tcons_prop loc0 _ prd'1).
    rewrite (tup_get_pr_irrel _ d0 _ prd'2).
    trivial.
  + assert (valid_tup_addr d' d0).
    { unfold valid_tup_addr. omega. }
    rewrite (tup_tcons_prop' loc0 _ d' _ H0).
    apply prloc0.
    apply H0.
Defined.
Next Obligation.
  replace (_ < _) with (D - (S (d sa)) < D - d sa) by trivial.
  omega.
Defined.


(* The getter. Use this function. *)
Program Definition get
 (ht: hash_tree 0 top_loc) (k: K): option V
  := prim_get ht _ k (hash k) _ _.
Next Obligation. generalize D_pos. omega. Defined.
Next Obligation. unfold hash_prefix. intros. omega. Defined.
Extraction Inline get_obligation_1.
Extraction Inline get_obligation_2.


(* The setter. Use this function. *)
Program Definition set
 (ht: hash_tree 0 top_loc) (k: K) (v: V): updated_hash_tree 0 top_loc ht k v + collides k
  := prim_set (mk_set_args 0 top_loc k v (hash k) _ _ _ ht).
Next Obligation. generalize D_pos. omega. Defined.
Next Obligation. unfold hash_prefix. intros. omega. Defined.
Extraction Inline set_obligation_1.
Extraction Inline set_obligation_2.
End iht.

Extraction Language CoreErlang.
