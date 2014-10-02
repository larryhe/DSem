
(* ============================================	*)
(* ---------- Test it..! ----------------------	*)

(*  Test for standard (continuation) semantics implementations  *)

				(* some convienences.. *)
fun kont_null v         = output(v,halt);		(* Econt *)
val end_cont     :Ccont = fn any_store => halt;
val qont_null    :Dcont = fn any_env   => end_cont;

val input  = id("input");	(* a shorthand.. *)
val result = id("result");

                                (* dump the store.... *)
fun dump (sto as store(lo, hi, data) ) =
    map ($ fetch sto) (from lo hi);

                                (* a continuation to dump the store.... *)
fun dump_cont sto = ( print (dump sto); halt );

(* ========== *
                                (* a continuation to output the store.... *)
fun output_cont (sto as store(lo, hi, data) ) =
    let fun put []      = halt
          | put (v::vs) = output(v, put vs)
    in  put (dump sto)
    end;
 * ========== *)
                                (* a continuation to output the store.... *)
fun output_cont sto = reduce ( output oo pair ) halt (dump sto);

(* --------------------------------------------	*)


val e1 = num(2);
val e2 = sumof(num(1),num(2));

val Trace_flag = "Test: expressions    [ 2, 1+2]";
evaluate e1 env_null kont_null sto_null;		(*  = 2 *)
evaluate e2 env_null kont_null sto_null;		(*  = 3 *)

val Trace_flag = "Test: expressions    [ 1+2*3 = 7 ]";
evaluate (sumof(num(1), prodof(num(2),num(3))))
			env_null kont_null sto_null; (*  = 7 *)

 (* ------------------------- *)

val Trace_flag = "Test: declaration    [ const x = 2 ]";
val dx = constdef("x",num(2));	(* a declaration *)
elaborate dx env_null qont_null sto_null;

(* ========== *
evaluate (  leten( dx, sumof( num(1), id("x") ))  )
			env_null kont_null sto_null; (* = 3 *)
 * ========== *)

(* ----------------------------------------------- *)
(*   result := input
 *)
val Trace_flag = "Test: result = input  [ 1, 2]";
val pgm = prog( assign( "result", input ));

			(* run the program on an input *)
run pgm  1;
run pgm  2;

(* ----------------------------------------------- *)
(*   result := input + 1
 *)
val Trace_flag = "Test: result = input+1  [ 1, 2]";
val pgm = prog( assign( "result", sumof( num(1),input ) ));

			(* run the program on an input *)
run pgm  1;
run pgm  2;

(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var y : int
 *      in  y:= 3
 *          if x<y then y:=1
 *                 else y:=2
 *)
val Trace_flag = "Test: program.1  [ y=1 ]";
val cmd =
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

		(* get Answer *)
execute cmd  env_null end_cont sto_null;

		(* get a full result..!  *)
                (* y  z *)
execute cmd  env_null dump_cont   sto_null;

		(* get a full set of Answers..!  *)
execute cmd  env_null output_cont sto_null;

(* ----------------------------------------------- *)
(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var     y : int
 *      in y := 3;
 *         let var z : int
 *         in  z:= 0
 *             z := z+1
 *)
val x = id("x");        (* a shorthand... *)
val y = id("y");
val z = id("z");

val Trace_flag = "Test: program.3  [ x=2, y=3, z=1 ]";
val pgm3 = 
 prog(
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
 );

val Trace_flag = "now run test.3";
run pgm3 0;

		(* -- also try direct execution *)
val Trace_flag = "now re-run test.3";
val prog(c3) = pgm3;
execute c3  env_null   dump_cont sto_null;
execute c3  env_null output_cont sto_null;

(* ----------------------------------------------- *)
(*   let const x ~ 2
 *   in let var     y : int
 *      in y := 3;
 *         let var z : int
 *         in  z:= 0                { multiply z = x*y }
 *             while 0<y do  z := z+x; y := y-1
 *)
val x = id("x");        (* a shorthand... *)
val y = id("y");
val z = id("z");
val pgm2 = 
 prog(
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
 );

run pgm2 0;
