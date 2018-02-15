open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree

let unit_expr loc = 
  {
    pexp_desc = Pexp_construct (Location.mkloc (Longident.Lident "()") loc, None);
    pexp_loc = loc;
    pexp_attributes = [];
  }
    
(* turn test into a no-op *)
let unit_test_mapper argv =
  { default_mapper with
    expr = fun mapper expr ->
      match expr with
      | { pexp_desc =
	  Pexp_extension ({ txt = "unit_test"; loc }, _)} ->
	 (* Replace with let _ = () in () *)
	 Exp.let_ ~loc Nonrecursive
	      (* _ *)
	   [ {
	     pvb_pat =
	       {
		 ppat_desc = Ppat_any;
		 ppat_loc = loc;
		 ppat_attributes = [];
	       };         
	     pvb_expr = unit_expr loc;
	     pvb_attributes = [];
	     pvb_loc = loc;
	   } ]
	   (unit_expr loc)
      (* Delegate to the default mapper. *)
      | x -> default_mapper.expr mapper x;
  }

let () = register "unit_test" unit_test_mapper
