(* --------------------------------------------	*)
(* denotational semantics definitions: in SML	*)
(* --------------------------------------------	*)

(* --------------------------------------------	*)
(* Expression Calculator:  (Watt, Ex. 3.2)	*)
(* ds_calc.ml					*)
(* --------------------------------------------	*)


(* ---------- Abstract Syntax ---------- *)

			(* terminal nodes of the syntax *)
type  Numeral = int;

			(* parsed phrases of the abstract syntax *)
datatype
    Expression =
              num    of Numeral
    	    | sumof  of Expression * Expression
    	    | subof  of Expression * Expression
    	    | prodof of Expression * Expression
and
    Command =
              expreq  of Expression
	    ;


(* ---------- Semantic Domains ---------- *)
type  Integer = int;

datatype Value =
              integer     of int
    	    | truthvalue  of bool
	    ;

(* ---------- Semantic Functions ---------- *)
(*  These declarations are automatically inferred from the equations *)


(* ---------- Auxiliary Semantic Functions ---------- *)
fun sum   (x, y) = x + y:int;
fun diff  (x, y) = x - y:int;
fun prod  (x, y) = x * y:int;

(* ---------- Semantic Equations ---------- *)
print "----------  Semantic Equations";

				(* from integer to Value *)
fun  valuation ( n )   = integer(n)
and
     evaluate ( sumof (e1,e2) ) = 
     		let val integer(i1) = evaluate e1
     		    val integer(i2) = evaluate e2
		in  integer( sum(i1,i2) )
		end
  |  evaluate ( subof (e1,e2) ) =
     		let val integer(i1) = evaluate e1
     		    val integer(i2) = evaluate e2
		in  integer( diff(i1,i2) )
		end
  |  evaluate ( prodof(e1,e2) ) =
     		let val integer(i1) = evaluate e1
     		    val integer(i2) = evaluate e2
		in  integer( prod(i1,i2) )
		end
  |  evaluate ( num(n) )   = valuation(n)
and
     execute ( expreq(e)  )  =
		evaluate e
  ;

(* ============================== *)
(* ========== Test it! ========== *)
print "----------  Test";
val e1 = num(2);
val e2 = sumof(num(1),num(2));
evaluate e1;
evaluate e2;

evaluate (sumof(num(1), prodof(num(2),num(3))));

val c1 = expreq(e1);
val c2 = expreq(e2);
execute c1;
execute c2;
