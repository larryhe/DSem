
(* ============================================	*)
(* ---------- Test it..! ----------------------	*)

(*  Test for direct semantics implementations  *)

val e1 = num(2);
val e2 = sumof(num(1),num(2));
evaluate e1 env_null sto_null;		(*  = 2 *)
evaluate e2 env_null sto_null;		(*  = 3 *)

evaluate (sumof(num(1), prodof(num(2),num(3)))) env_null sto_null; (*  = 7 *)

val dx = constdef("x",num(2));	(* a declaration *)
elaborate dx env_null sto_null;

(*
evaluate (  letin( dx, sumof( num(1), id("x") ))  ) env_null sto_null; (* = 3 *)
 *)

(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var y : int
 *      in  y:= 3
 *          if x<y then y:=1
 *                 else y:=2
 *)
val pgm = 
  letin( constdef( "x", num(2)),
         letin( vardef( "y", Int),
		cmdcmd( assign( "y", num(3)),
		        ifthen( less(id("x"),id("y")),
			        assign("y",num(1)),
			        assign("y",num(2))
				)
			)
		)
         )
  ;
execute pgm  env_null sto_null;
				(* dump the store.... *)
                (* y *)
map ($ fetch it) [ 1 ];

(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var     y : int
 *      in y := 3;
 *         let var z : int
 *         in  z:= 0
 *             z := z+1
 *)
val x = id("x");	(* a shorthand... *)
val y = id("y");
val z = id("z");
val pgm3 = 
  letin( constdef( "x", num(2)),
       letin( vardef( "y", Int),
              cmdcmd( assign( "y", num(3)),
	              letin ( vardef( "z", Int),
		              cmdcmd( assign( "z",num(0)),
                                      assign("z", sumof(z,num(1)))
				      )
			      )
		      )
	      )
       )
  ;
execute pgm3  env_null sto_null;
val     sto3 = it;

				(* dump the store.... *)
(*                (* y  z *)
map ($ fetch sto3) [ 1, 2 ];
 *)
				(* dump the store.... *)
fun dump (sto as store(lo, hi, data) ) =
    map ($ fetch sto) (from lo hi);
dump sto3;


(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var     y : int
 *      in y := 3;
 *         let var z : int
 *         in  z:= 0		{ multiply z = x*y }
 *             while 0<y do  z := z+x; y := y-1
 *)
val x = id("x");	(* a shorthand... *)
val y = id("y");
val z = id("z");
val pgm2 = 
  letin( constdef( "x", num(2)),
       letin( vardef( "y", Int),
              cmdcmd( assign( "y", num(3)),
	              letin ( vardef( "z", Int),
		              cmdcmd( assign( "z",num(0)),
                                      whiledo( less(num(0),y),
                                          cmdcmd( assign("z", sumof(z,x)),
                                                  assign("y", subof(y,num(1)))
						  )
					  )
				      )
			      )
		      )
	      )
       )
  ;
execute pgm2  env_null sto_null;
val     sto2 = it;

				(* dump the store.... *)
                  (* y  z *)
dump sto2;
