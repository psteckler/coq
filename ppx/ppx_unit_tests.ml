open Ast_mapper
open Asttypes
open Parsetree
open OUnit2

let unit_test_mapper argv =
  { default_mapper with
    expr = fun mapper expr ->
      match expr with
      | { pexp_desc =
	  Pexp_extension ({ txt = "unit_test"; loc },
			  PStr [{ pstr_desc = Pstr_eval ({ pexp_loc;
							   pexp_desc = test }, _)
				}
			       ])
	} ->
	 { pexp_desc = test;
	   pexp_loc = loc;
	   pexp_attributes = []
	 }
      (* Delegate to the default mapper. *)
      | x -> default_mapper.expr mapper x;
  }

let () = register "unit_test" unit_test_mapper
