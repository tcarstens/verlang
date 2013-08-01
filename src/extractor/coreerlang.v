Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlIntConv.
Require Import ZArith.
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.


Module Extras.
  (* Triples come up in MiniML. *)
  Inductive triple (A B C: Type) := T: A -> B -> C -> triple A B C.
  Extract Inductive triple => "( * * )" [ "" ].

  (* OCaml strings. *)
  Axiom caml_string: Set.
  Extract Inlined Constant caml_string => "string".

  Axiom caml_string_eq_dec:
   forall (a b: caml_string),
    {a = b} + {a <> b}.
  Extract Constant caml_string_eq_dec => "(fun a -> fun b -> a = b)".

  Axiom str_cast: string -> caml_string.
  Extract Constant str_cast =>
    "(fun s ->
       let r = String.create (List.length s) in
       let rec fill pos = function
         | [] -> r
         | c :: s -> r.[pos] <- c; fill (pos + 1) s
       in fill 0 s)".

  Program Fixpoint map2 {X Y Z} f (xs: list X) (ys: list Y): list Z
    := match xs, ys with
         | cons x xs', cons y ys' => cons (f x y) (map2 f xs' ys')
         | _, _ => nil
       end.

  Program Fixpoint map3 {X Y Z W} (f: X -> Y -> Z -> W) xs ys zs: list W
    := match xs, ys, zs with
         | cons x xs', cons y ys', cons z zs' => cons (f x y z) (map3 f xs' ys' zs')
         | _, _, _ => nil
       end.
End Extras.
Import Extras.


(* After extracting coreerlang.v, we delete this module from the result.
 * Its contents are all axioms with "Extract Inlined" directives.
 *)
Module DeleteMe.
  Module Str.
    Axiom regexp_t: Set.

    Axiom regexp: caml_string -> regexp_t.
    Extract Inlined Constant regexp => "Str.regexp".

    Axiom reg_split: regexp_t -> caml_string -> list caml_string.
    Extract Inlined Constant reg_split => "Str.split".

    Axiom global_replace: regexp_t -> caml_string -> caml_string -> caml_string.
    Extract Inlined Constant global_replace => "Str.global_replace".

    Axiom string_match: regexp_t -> caml_string -> int -> bool.
    Extract Inlined Constant string_match => "Str.string_match".
  End Str.


  Module Pp.
    Axiom std_ppcmds: Set.

    Axiom str: caml_string -> std_ppcmds.
    Extract Inlined Constant str => "Pp.str".

    Axiom fnl: std_ppcmds.
    Extract Inlined Constant fnl => "(Pp.fnl ())".

    Axiom concat: std_ppcmds -> std_ppcmds -> std_ppcmds.
    Extract Inlined Constant concat => "(++)".

    Axiom pp_int: int -> std_ppcmds.
    Extract Inlined Constant pp_int => "Pp.int".
  End Pp.


  Module Libnames.
    Axiom global_reference: Set.
  End Libnames.


  Module Names.
    Axiom mod_bound_id: Set.

    Axiom module_path: Set.
    Axiom string_of_mp: module_path -> caml_string.
    Extract Inlined Constant string_of_mp => "Names.string_of_mp".

    Axiom identifier: Set.
    Axiom string_of_id: identifier -> caml_string.
    Extract Inlined Constant string_of_id => "Names.string_of_id".
    Axiom id_of_string: caml_string -> identifier.
    Extract Inlined Constant id_of_string => "Names.id_of_string".

    Axiom label: Set.
    Axiom module_ident: Set.
    Axiom dir_path: Set.
    Axiom kernel_name: Set.
    Axiom mutual_inductive: Set.
  End Names.


  Module Table.
    Import Libnames.
    Import Names.

    Axiom is_custom: global_reference -> bool.
    Extract Inlined Constant is_custom => "Table.is_custom".

    Axiom is_inline_custom: global_reference -> bool.
    Extract Inlined Constant is_inline_custom => "Table.is_inline_custom".

    Axiom find_custom: global_reference -> caml_string.
    Extract Inlined Constant find_custom => "Table.find_custom".

    Axiom modpath_of_r: global_reference -> module_path.
    Extract Inlined Constant modpath_of_r => "Table.modpath_of_r".

    Axiom current_toplevel: module_path.
    Extract Inlined Constant current_toplevel => "(Table.current_toplevel ())".

    Axiom base_mp: module_path -> module_path.
    Extract Inlined Constant base_mp => "Table.base_mp".
  End Table.


  (* Cheap hack so that we can use arrays within our inductives. *)
  Inductive array (T: Type): Type := make: nat -> T -> array T.
  Module Array.
    Axiom map: forall {T T': Type}, (T -> T') -> array T -> array T'.
    Extract Inlined Constant map => "Array.map".

    Axiom to_list: forall {T}, array T -> list T.
    Extract Inlined Constant to_list => "Array.to_list".

    Axiom of_list: forall {T}, list T -> array T.
    Extract Inlined Constant of_list => "Array.of_list".

    Axiom ith: forall {T}, array T -> int -> T.
    Extract Inlined Constant ith => "(fun x -> fun i -> x.(i))".

    Axiom length: forall {T}, array T -> int.
    Extract Inlined Constant length => "Array.length".
  End Array.


  Module Idset.
    Axiom idset: Set.

    Axiom idset_empty: idset.
    Extract Inlined Constant idset_empty => "Idset.empty".

    Axiom idset_add: Names.identifier -> idset -> idset.
    Extract Inlined Constant idset_add => "Idset.add".
  End Idset.


  Module Miniml.
    Import Libnames.
    Import Names.

    Inductive kill_reason: Set
     := Ktype: kill_reason
      | Kother: kill_reason.

    Inductive sign
     := Keep: sign
      | Kill: kill_reason -> sign.

    Definition signature := list sign.

    Inductive ml_type: Type
     := Tarr: ml_type -> ml_type -> ml_type
      | Tglob: global_reference -> list ml_type -> ml_type
      | Tvar: int -> ml_type
      | Tvar': int -> ml_type
      | Tmeta: ml_meta -> ml_type
      | Tdummy: kill_reason -> ml_type
      | Tunknown
      | Taxiom
    with ml_meta: Type
     := Mk_ml_meta: int -> option ml_type -> ml_meta.

    Definition ml_schema: Type := (int * ml_type)%type.

    Inductive inductive_kind: Set
      := Singleton: inductive_kind
       | Coinductive: inductive_kind
       | Standard: inductive_kind
       | Record: list (option global_reference) -> inductive_kind.

    Record ml_ind_packet: Type
      := Mk_ml_ind_packet
          { ip_typename: identifier
          ; ip_consnames: list identifier
          ; ip_logical: bool
          ; ip_sign: signature
          ; ip_vars: list signature
          ; ip_types: list (list ml_type)
          }.

    Inductive equiv: Type
      := NoEquiv: equiv
       | Equiv: kernel_name -> equiv
       | RenEquiv: caml_string -> equiv.

    Record ml_ind: Type
      := ind_kind: inductive_kind -> ml_ind
       | ind_nparams: int -> ml_ind
       | ind_packets: list ml_ind_packet -> ml_ind
       | ind_equiv: equiv -> ml_ind.

    Inductive ml_ident: Type
      := Dummpy: ml_ident
       | Id: identifier -> ml_ident
       | Tmp: identifier -> ml_ident.

    Inductive ml_pattern: Type
      := Pcons: global_reference -> list ml_pattern -> ml_pattern
       | Ptuple: list ml_pattern -> ml_pattern
       | Prel: nat -> ml_pattern
       | Pwild: ml_pattern
       | Pusual: global_reference -> ml_pattern.

    Inductive ml_ast: Type
      := MLrel: nat -> ml_ast
       | MLapp: ml_ast -> list ml_ast -> ml_ast
       | MLlam: ml_ident -> ml_ast -> ml_ast
       | MLletin: ml_ident -> ml_ast -> ml_ast -> ml_ast
       | MLglob: global_reference -> ml_ast
       | MLcons: ml_type -> global_reference -> list ml_ast -> ml_ast
       | MLtuple: list ml_ast -> ml_ast
       | MLcase: ml_type -> ml_ast -> array (triple (list ml_ident) ml_pattern ml_ast) -> ml_ast
       | MLfix: nat -> array identifier -> array ml_ast -> ml_ast
          (* In ``MLfix k xs e'' we require 0 <= k < Array.length xs *)
       | MLexn: caml_string -> ml_ast
       | MLdummy: ml_ast
       | MLaxiom: ml_ast
       | MLmagic: ml_ast -> ml_ast.

    Inductive ml_decl: Type
      := Dind: mutual_inductive -> ml_ind -> ml_decl
       | Dtype: global_reference -> identifier -> list ml_type -> ml_decl
       | Dterm: global_reference -> ml_ast -> ml_type -> ml_decl
       | Dfix: array global_reference -> array ml_ast -> array ml_type -> ml_decl.

    Inductive ml_spec: Type
      := Sind: mutual_inductive -> ml_ind -> ml_spec
       | Stype: global_reference -> list identifier -> option ml_type -> ml_spec
       | Sval: global_reference -> ml_type -> ml_spec.

    Inductive ml_specif: Type
      := Spec: ml_spec -> ml_specif
       | Smodule: ml_module_type -> ml_specif
       | Smodtype: ml_module_type -> ml_specif
    with ml_module_type: Type
      := MTident: module_path -> ml_module_type
       | MTfunsig: mod_bound_id -> ml_module_type -> ml_module_type -> ml_module_type
       | MTsig: module_path -> ml_module_sig -> ml_module_type
       | MTwith: ml_module_type -> ml_with_declaration -> ml_module_type
    with ml_with_declaration: Type
      := ML_With_type: list identifier -> list identifier -> ml_type -> ml_with_declaration
       | ML_With_module: list identifier -> module_path -> ml_with_declaration
    with ml_module_sig: Type
      := Mk_ml_module_sig: list (label * ml_specif) -> ml_module_sig.

    Inductive ml_structure_elem: Type
      := SEdecl: ml_decl -> ml_structure_elem
       | SEmodule: ml_module -> ml_structure_elem
       | SEmodtype: ml_module_type -> ml_structure_elem
    with ml_module_expr: Type
      := MEident: module_path -> ml_module_expr
       | MEfunctor: mod_bound_id -> ml_module_type -> ml_module_expr -> ml_module_expr
       | MEstruct: module_path -> ml_module_structure -> ml_module_expr
       | MEapply: ml_module_expr -> ml_module_expr -> ml_module_expr
    with ml_module: Type
      := Mk_ml_module: ml_module_expr -> ml_module_type -> ml_module
    with ml_module_structure: Type
      := Mk_ml_module_structure: list (label * ml_structure_elem) -> ml_module_structure.

    Extract Inductive ml_module_structure => "(label * ml_structure_elem) list" [ "" ].
    Extract Inductive ml_module => "ml_module" [ "" ].
    Axiom ml_mod_expr: ml_module -> ml_module_expr.
    Extract Inlined Constant ml_mod_expr => "(function e -> e.ml_mod_expr)".

    Definition ml_structure: Type := list (module_path * ml_module_structure).
    Definition ml_signature: Type := list (module_path * ml_module_sig).

    Record unsafe_needs: Set
      := Mk_unsafe_needs
          { mldummy: bool
          ; tdummy: bool
          ; tunknown: bool
          ; magic: bool
          }.

    Record language_descr: Type
      := Mk_language_descr
          { keywords: Idset.idset
          ; file_suffix: caml_string
          ; preamble:     (* preamble for modules *)
             identifier            (* module name *)
             -> list module_path   (* module imports *)
             -> unsafe_needs       (* casts which are used in the module *)
             -> Pp.std_ppcmds
          ; pp_struct:    (* render-er of modules *)
             ml_structure -> Pp.std_ppcmds
          ; sig_suffix:   (* suffix for header files (e.g., .mli) *)
             option caml_string
          ; sig_preamble: (* preamble for header files *)
             identifier -> list module_path -> unsafe_needs -> Pp.std_ppcmds
          ; pp_sig:       (* render-er of header files *)
             ml_signature -> Pp.std_ppcmds
          ; pp_decl:      (* render-er of decl's *)
             ml_decl -> Pp.std_ppcmds
          }.
  End Miniml.

  Module Mlutil.
    Import Names.
    Import Miniml.

    Axiom id_of_mlid: ml_ident -> identifier.
    Extract Inlined Constant id_of_mlid => "id_of_mlid".

    Axiom collect_lams: ml_ast -> (list ml_ident * ml_ast).
    Extract Inlined Constant collect_lams => "collect_lams".
  End Mlutil.
End DeleteMe.


(* Basic types in Core Erlang *)
Definition atom_t: Set := caml_string.
Definition integer_t: Type := int.
Definition char_t: Set := ascii.

Definition atom_eq_str_dec (a: atom_t) (s: string): {a = str_cast s} + {a <> str_cast s}
  := caml_string_eq_dec a (str_cast s).


(* Function name (with arity) *)
Inductive fname_t: Set
  := Fname: atom_t -> nat -> fname_t.

(* Literals *)
Inductive lit_t: Set
  := Lit_atom: atom_t -> lit_t
   | Lit_str: caml_string -> lit_t
   | Lit_cons: caml_string -> lit_t
   | Lit_nil: lit_t
   | Lit_tup: lit_t.

(* Variables *)
Inductive var_t: Set
  := Var: caml_string -> var_t.

(* Patterns *)
Inductive pat_t: Set
  := Pat_var: var_t -> pat_t
   | Pat_lit: lit_t -> list pat_t -> pat_t
   | Pat_alias: var_t -> pat_t -> pat_t.

(* Modules and primops *)
Definition modname_t: Set := atom_t.
Definition primop_t: Set := atom_t.

(* Definitions, functions, terms, and clauses *)
Inductive def_t: Type
  := Def: fname_t -> fun_t -> def_t
   | Def_custom: caml_string -> caml_string -> def_t
 with fun_t: Type
  := Func: list var_t -> term_t -> fun_t
 with term_t: Type
  := Term_var: var_t -> term_t
   | Term_fname: fname_t -> term_t
   | Term_lit: lit_t -> list term_t -> term_t
   | Term_fun: fun_t -> term_t
   | Term_let: var_t -> term_t -> term_t -> term_t
   | Term_letrec: list def_t -> term_t -> term_t
   | Term_case: term_t -> list clause_t -> term_t
   | Term_apply: term_t -> list term_t -> term_t
   | Term_call: modname_t -> fname_t -> list term_t -> term_t
   | Term_primop: primop_t -> list term_t -> term_t
   | Term_recv: list clause_t -> term_t -> term_t -> term_t
   | Term_globl: atom_t -> term_t
   | Term_custom: caml_string -> term_t
 with clause_t: Type
  := Clause: pat_t -> term_t -> term_t -> clause_t.

(* Modules *)
Inductive module_t: Type
  := Module: modname_t -> list fname_t -> list def_t -> module_t.


(* Now we get into the bulk of the extractor. *)
Import DeleteMe.Idset.
Import DeleteMe.Names.

Definition file_suffix: caml_string := str_cast ".core".
Definition sig_suffix := None (A:=caml_string).

Open Scope string_scope.
Definition keywords: idset
  := List.fold_right (fun s => idset_add (id_of_string (str_cast s))) idset_empty
      [ "after" ; "apply" ; "attributes"
      ; "call" ; "case" ; "catch"
      ; "do" ; "end" ; "fun"
      ; "in" ; "let" ; "letrec"
      ; "module" ; "of" ; "primop"
      ; "receive" ; "try" ; "when"
      ; "_wc"
      ].
Close Scope string_scope.

Program Fixpoint extr_pat (e: Common.env) (p: Miniml.ml_pattern) (ids: list Names.identifier): pat_t
  := match p with
       | Miniml.Pcons r xs =>
           pat_lit (lit_cons (mk_atom (pp_global Common.KCons r)))
                   (List.map (fun x => extr_pat e x ids) xs)
       | Miniml.Ptuple xs => pat_lit lit_tup (List.map (fun x => extr_pat e x ids) xs)
       | Miniml.Prel k => pat_var (var (string_of_id (Common.get_db_name k e)))
       | Miniml.Pwild => pat_var (var (camlstring_of_coqstring "_wc"))
       | Miniml.Pusual k =>
           pat_lit (lit_cons (mk_atom (pp_global Common.KCons k)))
                   (map (fun i => pat_var (var (string_of_id i))) ids)
     end.

Program Fixpoint extr_ast (e: Common.env) (t: Miniml.ml_ast) {measure (Miniml.ast_depth t)}: term_t
  := match t with
       | Miniml.MLrel k => term_var (var (string_of_id (Common.get_db_name k e)))
       | Miniml.MLapp (Miniml.MLglob r) xs =>
          let r_modpath := Names.string_of_mp (Table.modpath_of_r r) in
          let r' := pp_global Common.KTerm r
          in match reg_split (regexp (camlstring_of_coqstring "[~]")) r' with
               | [m ; f] => term_call (term_globl (mk_atom m))
                                      (term_globl (mk_atom f))
                                      (List.map (fun x => extr_ast e x) xs)
               | _ => term_call (term_globl (mk_atom r_modpath))
                                (term_globl (mk_atom r'))
                                (List.map (fun x => extr_ast e x) xs)
             end
       | Miniml.MLapp f xs =>
          let f' := extr_ast e f
          in match f' with
               | term_letrec defs (term_var v) =>
                   term_letrec defs (term_apply (term_var v) (List.map (fun x => extr_ast e x) xs))
               | _ => term_apply f' (List.map (fun x => extr_ast e x) xs)
             end
       | Miniml.MLlam _ _ =>
           let (bl, t') := Mlutil.collect_lams t in
           let (bl', e') := Common.push_vars (List.map Mlutil.id_of_mlid bl) e
           in term_fun (func (List.map (fun s => var (string_of_id s)) (List.rev bl'))
                       (extr_ast e' t'))
       | Miniml.MLletin v e1 e2 =>
           let (bl, e') := Common.push_vars [ Mlutil.id_of_mlid v ] e
           in match bl with
                | [ v' ] => let e1' := extr_ast e e1 in
                            let e2' := extr_ast e' e2
                            in term_let (var (string_of_id v')) e1' e2'
                | _ => False_rect _ _
              end
       | Miniml.MLglob r =>
          let r' := pp_global Common.KTerm r
          in if Table.is_inline_custom r
              then term_custom r'
              else term_globl (mk_atom r')
       | Miniml.MLcons _ r xs => term_lit (lit_cons (mk_atom (pp_global Common.KCons r)))
                                          (map (fun x => extr_ast e x) xs)
       | Miniml.MLtuple xs => term_lit lit_tup (map (fun x => extr_ast e x) xs)
       | Miniml.MLcase _ t' br =>
           let extr_branch (b: triple (list Miniml.ml_ident) Miniml.ml_pattern Miniml.ml_ast) :=
             match b with
               | T ids p t' =>
                   let (ids', e') := Common.push_vars (map Mlutil.id_of_mlid ids) e
                   in clause (extr_pat e' p (rev ids'))
                             (term_lit (lit_atom (mk_atom (camlstring_of_coqstring "true"))) nil)
                             (extr_ast e' t')
             end in
           let t'' := extr_ast e t' in
           let clauses := Array.to_list (Array.map extr_branch br) in
           let as_case := term_case t'' clauses
           in match t'' with
                | term_apply (term_fname (fname a 2)) [ delay ; default ]
                      => if atom_eq_dec a "receive_fin"
                          then term_recv clauses delay default
                          else as_case
                | _ => as_case
              end
       | Miniml.MLfix k ids fns =>
           let (ids', e') := Common.push_vars (rev (Array.to_list ids)) e in
           let zip n f :=
                let n' := string_of_id n in
                let (vs, f') := Mlutil.collect_lams f in
                let (vs', e'') := Common.push_vars (map Mlutil.id_of_mlid vs) e' in
                let f'' := extr_ast e'' f'
                in def (fname (mk_atom n') (List.length vs'))
                       (func (rev (map (fun v => var (string_of_id v)) vs')) f'') in
           let defs := map2 zip (rev ids') (Array.to_list fns) in
           let id := Array.ith (Array.of_list (rev ids')) (int_of_nat k)
           in term_letrec defs (term_var (var_atom (string_of_id id)))
       | Miniml.MLexn s =>
           term_primop (mk_atom (camlstring_of_coqstring "raise"))
                       [ term_lit (lit_atom (mk_atom (camlstring_of_coqstring "error"))) nil
                       ; term_lit (lit_str s) nil
                       ]
       | Miniml.MLdummy => term_lit (lit_atom (mk_atom (camlstring_of_coqstring "dummy"))) nil
       | Miniml.MLaxiom =>
           term_primop (mk_atom (camlstring_of_coqstring "raise"))
                       [ term_lit (lit_atom (mk_atom (camlstring_of_coqstring "exit"))) nil
                       ; term_lit (lit_str (camlstring_of_coqstring "axiom to be realized")) nil
                       ]
       | Miniml.MLmagic t' => extr_ast e t'
     end.
Ltac prove_termination
  := match goal with
       | |- (_ < _) => try (intros ; simpl ; omega) ; admit
     end.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. admit. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.
Next Obligation. prove_termination. Defined.


Program Definition extr_decl (d: Miniml.ml_decl): list def_t
  := let extr_decl' e r t ty :=
       if Table.is_custom r
        then def_custom (pp_global Common.KTerm r) (Table.find_custom r)
        else let (bl, t') := Mlutil.collect_lams t in
             let (bl, e') := Common.push_vars (map Mlutil.id_of_mlid bl) e
             in def (fname (mk_atom (pp_global Common.KTerm r)) (List.length bl))
                    (func (map (fun i => var (string_of_id i)) (rev bl)) (extr_ast e' t'))
     in match d with
          | Miniml.Dind mi ind => [ ]
          | Miniml.Dtype r id tys => [ ]
          | Miniml.Dterm r t ty => [ extr_decl' Common.empty_env r t ty ]
          | Miniml.Dfix rs asts tys =>
              map3 (extr_decl' Common.empty_env)
                   (Array.to_list rs)
                   (Array.to_list asts)
                   (Array.to_list tys)
        end.

Axiom bogus: list (Names.label * Miniml.ml_structure_elem) -> nat.

Program Fixpoint extr_defs (defs: list (Names.label * Miniml.ml_structure_elem)) {measure (bogus defs)}: list def_t :=
  match defs with
    | cons d defs' =>
        match d with
          | (_, Miniml.SEdecl dec) => List.app (extr_decl dec) (extr_defs defs')
          | (_, Miniml.SEmodule m) =>
             match Miniml.ml_mod_expr m with
               | Miniml.MEstruct path' (Miniml.mk_ml_module_structure defs'') => 
                  List.app (extr_defs defs'') (extr_defs defs')
               | _ => extr_defs defs'
             end
          | _ => extr_defs defs'
        end
    | nil => nil
  end.
Admit Obligations of extr_defs.

Fixpoint def_names (ds: list def_t): list fname_t
 := match ds with
      | nil => nil
      | cons (def n _) ds' =>
         match n with
           | fname _ k => if eq_nat_dec k 0
                           then def_names ds'
                           else cons n (def_names ds')
         end
      | cons _ ds' => def_names ds'
    end.

Definition extr_struct (mlss: Miniml.ml_structure): list module_t
  := let extr_struct' (mls: Names.module_path * Miniml.ml_module_structure) :=
       let (path, struct) := mls in
       let mk_defs (_: unit) :=
         match struct with
           Miniml.mk_ml_module_structure defs' => extr_defs defs'
         end in
       let defs := Common.with_visible
                    path
                    nil
                    mk_defs
       in module (mk_atom (Names.string_of_mp path))
                 (def_names defs)
                 [ ] (* TODO: attributes *)
                 defs
     in map extr_struct' mlss.

Notation "a ++ b" := (Pp.concat a b).

Definition str s := Pp.str (camlstring_of_coqstring s).

Definition pp_atom (a: atom_t): Pp.std_ppcmds
  := let r' := regexp (camlstring_of_coqstring "'") in
     let q  := camlstring_of_coqstring "@"
     in match a with
          mk_atom s => str "'" ++ Pp.str (global_replace r' q s) ++ str "'"
        end.

Definition pp_fname (f: fname_t): Pp.std_ppcmds
  := match f with fname a n => pp_atom a ++ str "/" ++ Pp.pp_int (int_of_nat n) end.

Fixpoint pp_concat (ps: list Pp.std_ppcmds): Pp.std_ppcmds
  := fold_right Pp.concat (str "") ps.

Fixpoint pp_concat_sep (s: Pp.std_ppcmds) (ps: list Pp.std_ppcmds): Pp.std_ppcmds
  := match ps with
       | nil => str ""
       | cons a ps' =>
           match ps' with
             | nil => a
             | cons _ _ => a ++ s ++ pp_concat_sep s ps'
           end
     end.

Axiom hash: caml_string -> int.
Extract Inlined Constant hash => "Hashtbl.hash".

Definition pp_var (v: var_t): Pp.std_ppcmds
  := let rlc := regexp (camlstring_of_coqstring "^[a-z]") in
     let r'  := regexp (camlstring_of_coqstring "'") in
     let a   := camlstring_of_coqstring "@"
     in match v with
          | var s => let s' := global_replace r' a s
                     in if string_match rlc s' (int_of_nat 0)
                         then str "_" ++ Pp.str s'
                         else Pp.str s'
          | var_atom s => str "'" ++ Pp.str (global_replace r' a s) ++ str "'"
        end.

Definition pp_lit (spc: Pp.std_ppcmds) (l: lit_t) (args: list Pp.std_ppcmds): Pp.std_ppcmds
  := match l with
       | lit_int i => Pp.pp_int i
       | lit_atom a => pp_atom a
       | lit_char c => str (String "'" (String c (String "'" EmptyString)))
       | lit_str s => str """" ++ Pp.str s ++ str """"
       | lit_nil => str "[]"
       | lit_cons s =>
           let default :=
             if atom_eq_dec s ""
              then match args with
                     | cons arg nil => str "{" ++ arg ++ str "}"
                     | _ => str "{ "
                            ++ pp_concat_sep (Pp.fnl ++ spc ++ str ", ") args
                            ++ Pp.fnl ++ spc ++ str "}"
                   end
              else match args with
                     | nil => pp_atom s
                     | cons arg nil => str "{" ++ pp_atom s ++ str ", " ++ arg ++ str "}"
                     | _ => str "{ "
                            ++ pp_concat_sep (Pp.fnl ++ spc ++ str ", ") (pp_atom s :: args)
                            ++ Pp.fnl ++ spc ++ str "}"
                   end
           in if atom_eq_dec s "Cons"
               then match args with
                      | [ a ; b ] => str "[" ++ a ++ str "|" ++ b ++ str "]"
                      | _ => default
                 end
            else if atom_eq_dec s "Nil"
                  then match args with
                         | nil => str "[]"
                         | _ => default
                       end
                  else default
       | lit_tup =>
          match args with
            | cons arg nil => str "{" ++ arg ++ str "}"
            | _ => str "{ "
                   ++ pp_concat_sep (Pp.fnl ++ spc ++ str ", ") args
                   ++ Pp.fnl ++ spc ++ str "}"
          end
     end.

Program Fixpoint pp_pat (spc: Pp.std_ppcmds) (p: pat_t): Pp.std_ppcmds
  := match p with
       | pat_var v => pp_var v
       | pat_lit l ps => pp_lit spc l (map (pp_pat spc) ps)
       | pat_alias v p' => pp_var v ++ str " = " ++ pp_pat (spc ++ str "   ") p'
     end.

Program Fixpoint pp_term (spc: Pp.std_ppcmds) (t: term_t): Pp.std_ppcmds
  := let pp_fun f :=
       match f with
         | func vars t =>
            let vars' := pp_concat_sep (str ", ") (map pp_var vars) in
            let spc' := spc ++ str "  "
            in str "fun (" ++ vars' ++ str ") -> "
               ++ Pp.fnl ++ spc' ++ pp_term spc' t
       end in
     let pp_clause (spc: Pp.std_ppcmds) (c: clause_t) :=
       let spc' := spc ++ str "    " in
       let (pat, guard, body) := c
       in pp_pat spc pat ++ str " when " ++ pp_term spc guard ++ str " ->"
          ++ Pp.fnl ++ spc' ++ pp_term spc' body
     in match t with
          | term_var v => pp_var v
          | term_fname f => pp_fname f
          | term_lit l ts => pp_lit spc l (map (pp_term spc) ts)
          | term_fun fn => pp_fun fn
          | term_let v t1 t2 =>
             let spc' := spc ++ str "  "
             in str "let " ++ pp_var v ++ str " = "
                ++ Pp.fnl ++ spc' ++ pp_term spc' t1
                ++ Pp.fnl ++ spc ++ str "in " ++ pp_term (spc ++ str "   ") t2
          | term_case t cs =>
             let spc' := spc ++ str "  "
             in str "case " ++ pp_term (spc ++ str "     ") t ++ str " of"
                ++ Pp.fnl ++ spc' ++ pp_concat_sep (Pp.fnl ++ spc') (map (pp_clause spc') cs)
                ++ Pp.fnl ++ spc ++ str " end"
          | term_letrec defs t =>
             let pp_def (d: def_t) :=
               match d with
                 | def fn f => pp_fname fn ++ str " = " ++ pp_fun f
                 | def_custom c b => str "" (* note that we don't print such a definition *)
               end
             in str "letrec "
                 ++ pp_concat_sep (Pp.fnl ++ spc ++ str "        ") (map pp_def defs)
                 ++ Pp.fnl ++ spc ++ str "in " ++ pp_term (spc ++ str "   ") t
          | term_apply t args =>
             match args with
               | cons arg nil =>
                  str "apply " ++ pp_term (spc ++ str "  ") t ++ str " (" ++ pp_term (spc ++ str "  ") arg ++ str ")"
               | _ =>
                  let spc' := Pp.fnl ++ spc ++ str "      , " in
                  let args' := pp_concat_sep spc' (map (pp_term (spc ++ str "        ")) args)
                  in str "apply " ++ pp_term (spc ++ str "  ") t
                     ++ Pp.fnl ++ spc ++ str "      ( " ++ args'
                     ++ Pp.fnl ++ spc ++ str "      )"
             end
          | term_call m f args =>
             match args with
               | cons arg nil =>
                  str "call " ++ pp_term (spc ++ str "  ") m ++ str ":" ++ pp_term (spc ++ str "  ") f ++ str " (" ++ pp_term (spc ++ str "  ") arg ++ str ")"
               | _ =>
                  let spc' := Pp.fnl ++ spc ++ str "     , " in
                  let args' := pp_concat_sep spc' (map (pp_term (spc ++ str "       ")) args)
                  in str "call " ++ pp_term (spc ++ str "  ") m ++ str ":" ++ pp_term (spc ++ str "  ") f
                     ++ Pp.fnl ++ spc ++ str "     ( " ++ args'
                     ++ Pp.fnl ++ spc ++ str "     )"
             end
          | term_primop a args => 
             str "primop " ++ pp_atom a ++ str " (" ++ pp_concat_sep (str ", ") (map (pp_term (str "")) args) ++ str ")"
          | term_try e1 vs e2 cs e3 =>
             let spc' := spc ++ str "  " in
             let spc'' := spc' ++ str "  "
             in str "try " ++ pp_term (spc ++ str "    ") e1 ++ str " of"
                ++ Pp.fnl ++ spc' ++ pp_concat_sep (str ", ") (map pp_var vs) ++ str " -> " ++ Pp.fnl ++ spc'' ++ pp_term spc'' e2
                ++ Pp.fnl ++ spc ++ str "catch " ++ pp_concat_sep (str ", ") (map pp_var vs) ++ str " -> " ++ Pp.fnl ++ spc'' ++ pp_term spc'' e3
          | term_recv cs t1 t2 =>
             let spc' := spc ++ str "  "
             in str "receive " ++ pp_concat_sep (str " ") (map (pp_clause spc') cs) ++ str " after"
                ++ Pp.fnl ++ spc' ++ pp_term spc' t1 ++ str " ->"
                ++ Pp.fnl ++ spc' ++ pp_term spc' t2
          | term_do t1 t2 =>
             let spc' := spc ++ str "   "
             in str "do " ++ pp_term spc' t1
                ++ Pp.fnl ++ spc' ++ pp_term spc' t2
          | term_catch t => str "catch " ++ pp_term (spc ++ str "  ") t
          | term_globl s => pp_atom s
          | term_custom s => Pp.str s
     end.

Definition pp_fun (f: fun_t): Pp.std_ppcmds
  := match f with
       | func vars t =>
            let vars' := pp_concat_sep (str ", ") (map pp_var vars) in
            let spc' := str "  "
            in str "fun (" ++ vars' ++ str ") -> "
               ++ Pp.fnl ++ spc' ++ pp_term spc' t
     end.

Definition pp_decl (d: def_t): Pp.std_ppcmds
  := match d with
       | def fn f =>
          match fn with
            | fname _ k => if eq_nat_dec k 0 then str "" else pp_fname fn ++ str " = " ++ pp_fun f
          end
       | def_custom c b => str "% " ++ Pp.str c ++ str " => " ++ Pp.str b
     end.

Program Definition pp_struct (mods: list module_t): Pp.std_ppcmds
  := let pp_struct' (m: module_t) :=
       let (nam, exports, attrs, defs) := m in
       let nam' := pp_atom nam in
       let exports' := pp_concat_sep (str ", ") (map pp_fname exports)
       in str "module " ++ nam' ++ str " [ " ++ exports' ++ str " ] attributes [ ] "
          ++ Pp.fnl
          ++ pp_concat_sep Pp.fnl (map pp_decl defs)
          ++ Pp.fnl ++ str "end" ++ Pp.fnl ++ Pp.fnl
     in pp_concat (map pp_struct' mods).

Definition preamble
 (nam: Names.identifier)
 (imports: list Names.module_path)
 `(Miniml.unsafe_needs)
 : Pp.std_ppcmds
  := str "".

Definition sig_preamble `(Names.identifier) `(list Names.module_path) `(Miniml.unsafe_needs) : Pp.std_ppcmds
  := str "".
Definition pp_sig `(Miniml.ml_signature): Pp.std_ppcmds := str "".

Definition coreerlang_descr: Miniml.language_descr
  := Miniml.mk_language_descr
       keywords
       file_suffix
       preamble
       (fun x => pp_struct (extr_struct x))
       sig_suffix
       sig_preamble
       pp_sig
       (fun x => pp_concat (map pp_decl (extr_decl x))).

