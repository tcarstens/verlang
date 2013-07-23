Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlString.
Require Import String.
Require Import List.
Require Import OurString.
Require Import PP.


Inductive triple (A B C: Type) := T: A -> B -> C -> triple A B C.
Extract Inductive triple => "( * * )" [ "" ].



Module Libnames.
  Axiom global_reference: Set.
End Libnames.

Module Names.
  Axiom module_path: Type.
  Axiom string_of_mp: module_path -> caml_string.
  Extract Inlined Constant string_of_mp => "string_of_mp".
  Axiom mod_bound_id: Type.
  Definition identifier: Type := caml_string.
  Axiom string_of_id: identifier -> caml_string.
  Extract Inlined Constant string_of_id => "string_of_id".
  Definition label: Type := identifier.
  Definition module_ident: Type := identifier.
  Definition dir_path: Type := list module_ident.
  Definition kernel_name: Type := triple module_path dir_path label.
  Definition mutual_inductive: Type := prod kernel_name kernel_name.
End Names.

Module Common.
  Import Libnames.
  Import Names.

  Axiom env: Type.
  Axiom empty_env: env.
  Extract Inlined Constant empty_env => " (empty_env ()) ".

  Axiom get_db_name: nat -> env -> identifier.
  Extract Inlined Constant get_db_name => "get_db_name".

  Axiom push_vars: list identifier -> env -> (list identifier * env).
  Extract Inlined Constant push_vars => "push_vars".

  Axiom push_vars_len:
    forall vs e, length vs = length (fst (push_vars vs e)).

  Inductive Kind: Type := KTerm | KType | KCons | KMod.
  Extract Inductive Kind => "Kind" [ "Term" "Type" "Cons" "Mod" ].

  Axiom pp_global : Kind -> global_reference -> caml_string.
  Extract Inlined Constant pp_global => "pp_global".

  Axiom push_visible: Names.module_path -> list Names.module_path -> unit.
  Extract Inlined Constant push_visible => "push_visible".

  Axiom pop_visible: unit.
  Extract Inlined Constant pop_visible => "(pop_visible ())".

  Axiom with_visible: forall {T}, Names.module_path -> list Names.module_path -> (unit -> T) -> T.
  Extract Inlined Constant with_visible => "(function mp -> function sel -> function f -> push_visible mp sel; let p = f () in pop_visible (); p)".
End Common.

Module Table.
  Import Libnames.
  Import Names.

  Axiom is_custom: global_reference -> bool.
  Extract Inlined Constant is_custom => "is_custom".

  Axiom is_inline_custom: global_reference -> bool.
  Extract Inlined Constant is_inline_custom => "is_inline_custom".

  Axiom find_custom: global_reference -> caml_string.
  Extract Inlined Constant find_custom => "find_custom".

  Axiom modpath_of_r: global_reference -> module_path.
  Extract Inlined Constant modpath_of_r => "modpath_of_r".

  Axiom current_toplevel: module_path.
  Extract Inlined Constant current_toplevel => "(current_toplevel ())".

  Axiom base_mp: module_path -> module_path.
  Extract Inlined Constant base_mp => "base_mp".
End Table.


Inductive array (T: Type): Type := make: nat -> T -> array T.
Module Array.
  Axiom map: forall {T T': Type}, (T -> T') -> array T -> array T'.
  Extract Inlined Constant map => "Array.map".
  Axiom to_list: forall {T}, array T -> list T.
  Extract Inlined Constant to_list => "Array.to_list".
  Axiom of_list: forall {T}, list T -> array T.
  Extract Inlined Constant of_list => "Array.of_list".
  Axiom ith: forall {T}, array T -> int -> T.
  Extract Inlined Constant ith => "(function x -> function i -> x.(i))".
End Array.


(* Not sure what to do with these guys *)
Axiom idset: Type.
Axiom idset_empty: idset.
Extract Inlined Constant idset_empty => "Idset.empty".
Axiom idset_add: Names.identifier -> idset -> idset.
Extract Inlined Constant idset_add => "Idset.add".
(* End of the mystery bunch *)




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
   := mk_ml_meta: int -> option ml_type -> ml_meta.

  Definition ml_schema: Type := (int * ml_type)%type.

  Inductive inductive_kind: Set
    := Singleton: inductive_kind
     | Coinductive: inductive_kind
     | Standard: inductive_kind
     | Record: list (option global_reference) -> inductive_kind.

  Record ml_ind_packet: Type
    := mk_ml_ind_packet
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
     | Pusual: global_reference -> ml_pattern
  with ml_ast: Type
    := MLrel: nat -> ml_ast
     | MLapp: ml_ast -> list ml_ast -> ml_ast
     | MLlam: ml_ident -> ml_ast -> ml_ast
     | MLletin: ml_ident -> ml_ast -> ml_ast -> ml_ast
     | MLglob: global_reference -> ml_ast
     | MLcons: ml_type -> global_reference -> list ml_ast -> ml_ast
     | MLtuple: list ml_ast -> ml_ast
     | MLcase: ml_type -> ml_ast -> array (triple (list ml_ident) ml_pattern ml_ast) -> ml_ast
     | MLfix: nat -> array identifier -> array ml_ast -> ml_ast
       (* In ``MLfix k xs e'' we require 0 <= k < length xs (I think those are the right bounds.) *)
     | MLexn: caml_string -> ml_ast
     | MLdummy: ml_ast
     | MLaxiom: ml_ast
     | MLmagic: ml_ast -> ml_ast.

  Fixpoint series (ns: list nat): nat
    := match ns with
         | nil => 0
         | cons n ns' => n + series ns'
       end.

  Lemma series_bound:
    forall n ns, In n ns -> n <= series ns.
  Proof.
    intros.
    induction ns.
    + contradiction.
    + elim H.
      - intro ; subst.
        simpl.
        omega.
      - intro H'.
        apply IHns in H'.
        simpl.
        omega.
  Qed.

  Fixpoint ast_depth (a: ml_ast): nat
    := 1 + match a with
             | MLapp x xs => series (ast_depth x :: map ast_depth xs)
             | MLlam _ a => ast_depth a
             | MLletin _ e1 e2 => ast_depth e1 + ast_depth e2
             | MLcons _ _ xs => series (map ast_depth xs)
             | MLtuple xs => series (map ast_depth xs)
             | MLcase _ e bs => 0
               (* You would prefer to use the definition below, but bs
                  is an ML array and not a Coq list, hence such calculations
                  cannot actually be performed from within Coq.
                 series (ast_depth e ::
                         map (fun (b: triple (list ml_ident) ml_pattern ml_ast) =>
                                match b with
                                  | T _ _ b => ast_depth b
                                end)
                             bs)
               *)
             | MLfix _ _ xs => 0 (* same as above: series (map ast_depth xs) *)
             | MLmagic a => ast_depth a
             | MLrel _ => 0
             | MLglob _ => 0
             | MLexn _ => 0
             | MLdummy => 0
             | MLaxiom => 0
           end.

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
    := mk_ml_module_sig: list (label * ml_specif) -> ml_module_sig.

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
    := mk_ml_module: ml_module_expr -> ml_module_type -> ml_module
  with ml_module_structure: Type
    := mk_ml_module_structure: list (label * ml_structure_elem) -> ml_module_structure.

  Extract Inductive ml_module_structure => "(label * ml_structure_elem) list" [ "" ].
  Extract Inductive ml_module => "ml_module" [ "" ].
  Axiom ml_mod_expr: ml_module -> ml_module_expr.
  Extract Inlined Constant ml_mod_expr => "(function e -> e.ml_mod_expr)".

  Definition ml_structure: Type := list (module_path * ml_module_structure).
  Definition ml_signature: Type := list (module_path * ml_module_sig).

  Record unsafe_needs: Set
    := mk_unsafe_needs
        { mldummy: bool
        ; tdummy: bool
        ; tunknown: bool
        ; magic: bool
        }.

  Record language_descr: Type
    := mk_language_descr
        { keywords:     (* keywords in the larget language *)
           idset
        ; file_suffix:  (* suffix for modules (e.g., .ml) *)
           caml_string
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

