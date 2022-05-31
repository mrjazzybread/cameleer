open Gospel.Uast 
open Why3
open Ptree
open Gospel
open Parser_frontend

let debug = ref false

open Why3.Typing
open Wstdlib
open Ident
open Cameleer
module Pm = Pmodule
module E = Cameleer.Expression
module T = Cameleer.Uterm
open Effect

let print_modules = Debug.lookup_flag "print_modules"

let lambda_name = "lambda"
let cont_name = "continuation"
let eff_result = "eff_result"
let post_name = "post"
let continue_name = "contin"
let apply_name = "apply"


let mk_type_params n = 
  List.init n (fun n -> T.mk_id ("t" ^ string_of_int n))

let mk_param ?(name=None) pty : param =
  Loc.dummy_position, Option.map(fun x -> (T.mk_id x)) name, false, pty

let mk_tvars n =
  List.map (fun x -> PTtyvar x)
    (mk_type_params n)

let qualid_of_string s =
  Qident (T.mk_id s)

let mk_type name vis n_params def =
  {
  td_loc = Loc.dummy_position;
  td_ident = T.mk_id name;
  td_vis = vis;
  td_params = mk_type_params n_params;
  td_mut = false;
  td_inv = [];
  td_wit = None;
  td_def = def;
}

let mk_field name pty mut ghost =
  {
    f_loc = Loc.dummy_position;
    f_ident = T.mk_id name;
    f_pty = pty;
    f_mutable = mut;
    f_ghost = ghost
  }
(*
let _kont_type = 
  mk_type lambda_name Abstract 2 (TDrecord [])

let eff_kont =
  let kont_field = 
    mk_field "k" (PTtyapp(qualid_of_string lambda_name, mk_tvars 2)) false true in 
  let one_shot =
    mk_field "valid" (PTtyapp (qualid_of_string "bool", [])) true true in 
  mk_type cont_name Public 2 
  (TDrecord[kont_field; one_shot])
*)(*
let eff_result =
  let params = mk_tvars 2 in
  let result_cons =
    (Loc.dummy_position, T.mk_id "Result", 
    [mk_param (List.hd params)]) in 
  let eff_param = mk_param (PTtyapp(qualid_of_string eff_name, [])) in
  let cont_param = 
    mk_param (PTtyapp(qualid_of_string cont_name, List.rev params)) in
  let request_cons =
    (Loc.dummy_position, T.mk_id "Request",
    [eff_param; cont_param]) in 
  mk_type eff_result Public 2 
  (TDalgebraic([result_cons; request_cons]))
*)(*
let mk_logic_dummy name args return =
  {
    ld_loc = Loc.dummy_position;
    ld_ident = T.mk_id name;
    ld_params = args;
    ld_type = return;
    ld_def = None
  }

let post_pred =
  let params = mk_tvars 2 in 
  let kont_arg =
    mk_param (PTtyapp (qualid_of_string cont_name, params)) in 
  let arg_arg =
    mk_param (List.hd params) in 
  let result_arg =
    mk_param (List.nth params 1) in 
  mk_logic_dummy post_name [kont_arg; arg_arg; result_arg] None
*)


let term_of_string s =
  T.mk_term (Tident (Qident (T.mk_id s)))
let apply state_term is_kont =
  let params = mk_tvars 2 in
  let t = qualid_of_string (if is_kont then cont_name else lambda_name) in 
  let cont_arg = mk_param ~name:(Some "f") (PTtyapp (t, params)) in 
  let arg_arg = mk_param ~name:(Some "arg") (List.hd params) in 
  let args = [cont_arg; arg_arg] in 
  let post_term =  term_of_string post_name in 
  let kont_term = 
    if is_kont then T.mk_fcall [term_of_string "k"; term_of_string "f"]
    else term_of_string "f" in 
  let arg_term = term_of_string "arg" in 
  let result_term = term_of_string "result" in 
  let postcond = T.mk_fcall [post_term; kont_term; arg_term; state_term; state_term; result_term] in 
  let valid = T.mk_fcall [term_of_string "valid"; term_of_string "f"] in 
  let invalid_kont = 
    if is_kont then T.mk_term (Tbinnop(postcond, DTand, T.mk_term (Tnot(valid))))
    else postcond in
  let writes = Effect.writes_clause () in 
  let writes = if is_kont then valid::writes else writes in
  let pre = if is_kont then valid else (T.mk_term Ttrue) in 
  let spec = Vspec.mk_spec pre invalid_kont writes in 
  let exp = Eany(args, Expr.RKnone, Some(List.nth params 1), T.mk_pattern Pwild, Ity.MaskVisible, spec) in 
  let name = if is_kont then continue_name else apply_name in 
  Dlet(T.mk_id name, false, Expr.RKnone, E.mk_expr exp)


let use_std_lib ref_decls types refs =
  let dummy_pos = Loc.dummy_position in
  let stdlib = Qdot (Qident (T.mk_id "ocamlstdlib"), T.mk_id "Stdlib") in
  let stdlib_fun = Qdot (Qident (T.mk_id "ocamlstdlib"), T.mk_id "Stdlib_fun") in
  let ref_types = Seq.map (fun (_, pty) -> pty) refs in 
  let state_args = Seq.map (fun (x, _ ) -> 
    let id = T.mk_term (Tident (Qident (T.mk_id x))) in 
    let bang = T.mk_term (Tident (Qident (T.mk_id (Ident.op_prefix "!")))) in 
    T.mk_fcall [bang; id]
    ) refs in
  let state_term = T.mk_term (Ttuple(List.of_seq state_args)) in 
  let state_type = PTtuple (List.of_seq ref_types) in 
  let imports = 
    Odecl.mk_cloneexport stdlib []
  in
  let use_stdlib =
    Odecl.mk_cloneexport stdlib_fun
     [CStsym ( Qident (T.mk_id "state"), [], state_type);
      CStsym ( Qident (T.mk_id "exn"), [], PTtyapp(Qident(T.mk_id "exn"), []));
      CSprop ( Decl.Paxiom ) ]
  in
  [imports]@ types @ ref_decls @[use_stdlib;
  Odecl.mk_odecl dummy_pos (apply state_term true);
  Odecl.mk_odecl dummy_pos (apply state_term false);
  ]

let mk_info () =
  let info = Odecl.empty_info () in
  Odecl.add_info info "Some" 1;
  Odecl.add_info info "::" 2;
  info

let read_file filename nm c =
  let lb = Lexing.from_channel c in
  Location.init lb filename;
  let ocaml_structure = parse_ocaml_structure_lb lb in
  parse_structure_gospel ~filename ocaml_structure nm

(* TODO: type-checking structure items *)
(* let type_check name nm structs =
 *   let md = Gospel.Tmodule.init_muc name in
 *   let penv = Gospel.Typing.penv [] (Gospel.Utils.Sstr.singleton nm) in
 *   let md = List.fold_left (Gospel.Typing.type_str_item penv) md structs in
 *   Gospel.Tmodule.wrap_up_muc md *)

let rec add_decl od =
  match od with
  | Odecl.Odecl (loc, d) -> Why3.Typing.add_decl loc d
  | Odecl.Omodule (loc, id, dl) ->
      Why3.Typing.open_scope id.id_loc id;
      List.iter add_decl dl;
      Why3.Typing.close_scope ~import:false loc

open Format

let rec pp_qualid fmt = function
  | Qident id -> fprintf fmt "%s" id.id_str
  | Qdot (q, id) -> fprintf fmt "%a.%s" pp_qualid q id.id_str

open Mod_subst

let mk_refine_modules info top_mod_name =
  let rec merge_qualid q = function
    | Qident id -> Qdot (q, id)
    | Qdot (q', id) -> Qdot (merge_qualid q q', id)
  in
  let open_module_id id = open_module id in
  let use_top_mod id =
    let ouse = Odecl.mk_duseimport Loc.dummy_position [ (id, None) ] in
    add_decl ouse
  in
  let top_mod_qualid = Qident (T.mk_id top_mod_name) in
  let mk_ref_q mod_name id = Qdot (mod_name, id) in
  let mk_clone_subst mod_refinee mod_refiner subst acc odecl =
    let open Odecl in
    let mk_id_refinee id = mk_ref_q mod_refinee id in
    let mk_id_refiner id = mk_ref_q mod_refiner id in
    let mk_id_ref id =
      let id = Ptree.{ id with id_loc = Loc.dummy_position } in
      (* FIXME *)
      (mk_id_refinee id, mk_id_refiner id)
    in
    let mk_cstsym id td_params =
      let id_refee, id_refer = mk_id_ref id in
      let pty_params = List.map (fun x -> PTtyvar x) td_params in
      CStsym (id_refee, td_params, PTtyapp (id_refer, pty_params))
    in
    (* let mk_cspsym id = let id_refee, id_refer = mk_id_ref id in
     *   CSpsym (id_refee, id_refer) in *)
    match odecl with
    | Odecl (_, Dlet (id, _, _, _)) ->
        let id = { id with id_loc = Loc.dummy_position } in
        (* FIXME *)
        let id_refinee = mk_id_refinee id in
        let id_refiner =
          try (Mstr.find id.id_str subst.subst_ts).td_ident
          with Not_found -> id
        in
        let id_refiner = mk_id_refiner id_refiner in
        CSvsym (id_refinee, id_refiner) :: acc
    | Odecl (_, Dtype [ { td_ident; td_params; _ } ]) ->
        mk_cstsym td_ident td_params :: acc
    | Odecl (_, Dlogic [ { ld_ident; ld_type = None; _ } ]) ->
        let ld_id = { ld_ident with id_loc = Loc.dummy_position } in
        let id_refinee = mk_id_refinee ld_id in
        let id_refiner =
          try
            let id = Mstr.find ld_id.id_str subst.subst_ps in
            merge_qualid mod_refiner id
          with Not_found -> mk_id_refiner ld_id
        in
        CSpsym (id_refinee, id_refiner) :: acc
    | Odecl (_, Dlogic [ { ld_ident; ld_type = Some _; _ } ]) ->
        let ld_id = { ld_ident with id_loc = Loc.dummy_position } in
        let id_refinee = mk_id_refinee ld_id in
        let id_refiner =
          try
            let id = Mstr.find ld_id.id_str subst.subst_fs in
            merge_qualid mod_refiner id
          with Not_found -> mk_id_refiner ld_id
        in
        CSfsym (id_refinee, id_refiner) :: acc
    | Odecl (_, Dexn (id, _, _)) ->
        let id = { id with id_loc = Loc.dummy_position } in
        let id_refinee = mk_id_refinee id in
        let id_refiner = mk_id_refiner id in
        CSxsym (id_refinee, id_refiner) :: acc
    | Odecl (_, Dprop (Decl.Paxiom, id, _)) ->
        let id = { id with id_loc = Loc.dummy_position } in
        CSlemma (mk_id_refinee id) :: acc
    | _ -> acc
    (* TODO *)
  in
  let mk_module refines_name info_refinement =
    let mod_id = "Refinement__" ^ refines_name in
    open_module_id (T.mk_id mod_id);
    use_top_mod top_mod_qualid;
    let mod_refinee =
      match info_refinement.Odecl.info_ref_name with
      | Some s -> s
      | None -> assert false
      (* TODO *)
    in
    let mod_refiner = Qident (T.mk_id refines_name) in
    let odecl_ref = info_refinement.Odecl.info_ref_decl in
    let subst = info_refinement.info_subst in
    let mk_subst = mk_clone_subst mod_refinee mod_refiner subst in
    let acc = [ CSprop Decl.Paxiom ] in
    let clone_subst = List.fold_left mk_subst acc odecl_ref in
    let odecl_clone = Odecl.mk_cloneexport top_mod_qualid clone_subst in
    add_decl odecl_clone;
    close_module Loc.dummy_position
  in
  Hashtbl.iter mk_module info.Odecl.info_refinement

(** Checks if a decleration is an effect declaration. As of OCaml 5.0.0, the only way to do this is by
    extending the {!eff} type.   

    @param d the top level declaration which we will add to either the left or right list 
    @result a type extension, if the declaration was an effect, marked for the left list, 
      or a top level declaration marked for the right list.
*)
let is_effect d =
  match d.sstr_desc with 
  |Str_typext t
    when Longident.flatten t.ptyext_path.txt = ["eff"] -> Some t
  |_ -> None

(**Turns an OCaml constructor into a Why3 constructor
      @param cons the arguments of the constructor (records not supported)
      @result A list of parameters for an equivelent Why3 constructor *)
let params cons =
  match cons with 
  |Ppxlib.Pcstr_tuple l -> 
    [mk_param (PTtuple (List.map (fun t -> E.core_type t) l))]
  |_ -> assert false

(** Turns an effect decleration {!E of t1 * t2 * ... : ... } into 
    a Why3 constructor with the same name that receives arguments of type {!t1}, {!t2} ...
    @param e An OCaml effect, declared as a type extension
    @return an equivelent Why3 constructor*)
let eff_of_cons e = 
  match e.Ppxlib.pext_kind with 
  |Ppxlib.Pext_decl (_, args, Some ({ptyp_desc = Ptyp_constr (_, [t]);_})) ->
    let () = map_effect e.Ppxlib.pext_name.txt (E.core_type t) in
    let loc = T.location e.pext_loc in 
    let id = T.mk_id ~id_loc:(T.location e.pext_name.loc) e.pext_name.txt in 
    let tuple_of l = List.map E.core_type (match l with | Ppxlib.Pcstr_tuple l -> l|_-> assert false) in 
    (loc, id, params args), tuple_of args
  |_ -> assert false


(** Turns a list of type extensions into a single algebraic data type. 
If the list of type extensions is empty, this function will return None

@param effects the type_extension objects representing effect decleration
@return an algebraic data type {!type eff = ...} with all the user defined effects*)
let mk_effect_type effects =
  let mk_decl name eff_type vis = Odecl.mk_dtype Loc.dummy_position
    [{
    td_loc = Loc.dummy_position;
    td_ident = T.mk_id name;
    td_params = [];
    td_vis = vis;
    td_mut = false;
    td_inv = [];
    td_wit = None;
    td_def = eff_type
  }] in
match effects with
|[] -> [], mk_decl exn_name (TDrecord []) Abstract
|_ ->
  let cons_list = List.flatten (List.map (fun e -> e.Ppxlib.ptyext_constructors) effects) in 
  let eff_list = List.map eff_of_cons cons_list in 
  let eff_type = TDalgebraic (List.map (fun (x, _) -> x) eff_list) in
  let param_types = List.map (fun ((_, id, _), args) -> 
      mk_decl ("param_" ^ id.id_str) (TDalias (PTtuple args)) Public) eff_list  in
  let decl = mk_decl exn_name eff_type Public in
   param_types, decl

(** Seperates the program into two lists, one with declerations of variables of type {'a !ref} and another with the remaining declerations
We also assume that all references are declared at the start of the program. We also map the name of each reference to its type in a global variable.

    @param p list of Gospel definitions
    @returns l1, l2 where l1 is a list of reference definitions and l2 are the remaining program definitions*)
let rec add_state_var p =
  match p with 
  |d::t -> begin
      match d.sstr_desc with 
      |Uast.Str_value(Nonrecursive, 
      [{spvb_pat = {ppat_desc = Ppat_constraint( {ppat_desc = Ppat_var v;_} , core_t);_};_}]) ->  
        begin match core_t.ptyp_desc with 
        |Ptyp_poly(_, {ptyp_desc=Ptyp_constr(id, [core_t]);_}) when Longident.flatten id.txt = ["ref"] -> 
            map_ref_type (v.txt) (E.core_type core_t);
            let l1, l2 = add_state_var t in 
            d::l1, l2
        |_ -> [], p end
      |_ -> [], p end  
  |[] -> [], []

let read_channel env path file c =
  if !debug then Format.eprintf "Reading file '%s'@." file;
  let mod_name =
    let f = Filename.basename file in
    String.capitalize_ascii (Filename.chop_extension f)
  in
  let f = read_file file mod_name c in
  (* let f = type_check file mod_name f in *)
  open_file env path;
  (* This is the beginning of the Why3 file construction *)
  let id = T.mk_id mod_name in
  open_module id;
  (* This is the beginning of the top module construction *)
  let info = mk_info () in
  let effects = List.filter_map is_effect f in
  (*The generated program will have the following structure:
    imports  
  
    type exn = ... 
    
    user defined types 
    
    reference variables 
    
    pre, post, apply, contin 
    
    rest of program *)
  let p, eff_type = mk_effect_type effects in 
  let types, program = 
    List.partition 
      (fun x -> match x.sstr_desc with |Uast.Str_type _ -> true |_ -> false) 
      f in 
  let refs, program = add_state_var program in
  let types = Declaration.s_structure info types in 
  let refs = Declaration.s_structure info refs in 
  let use_std_lib = use_std_lib refs types (Map.to_seq !tl_ref_types) in 
  let f = Declaration.s_structure info program in
  let f = eff_type::(use_std_lib@p@f) in
  (*let f = top_level f in*)
  let rec pp_list pp fmt l =
    match l with
    | [] -> ()
    | x :: r ->
        Format.eprintf "%a" pp x;
        pp_list pp fmt r
  in
  let rec pp_decl fmt d =
    match d with
    | Odecl.Odecl (_loc, d) -> Format.fprintf fmt "%a@." (Mlw_printer.pp_decl ~attr:true) d
    | Odecl.Omodule (_loc, id, dl) ->
        Format.eprintf "@[<hv 2>scope %s@\n%a@]@\nend@." id.id_str
          (pp_list pp_decl) dl
  in
  if !debug then pp_list pp_decl Format.err_formatter f;
  List.iter add_decl f;
  close_module Loc.dummy_position;
  (* Closes the top module *)
  mk_refine_modules info mod_name;
  let mm = close_file () in
  (if Debug.test_flag print_modules then
   let print_m _ m = Format.eprintf "%a@\n@." Pm.print_module m in
   let add_m _ m mm = Mid.add m.Pm.mod_theory.Theory.th_name m mm in
   Mid.iter print_m (Mstr.fold add_m mm Mid.empty));
  mm

let () =
  Env.register_format Pm.mlw_language "ocaml" [ "ml" ] read_channel
    ~desc:"OCaml format"
