(* ----------------------------------------------------	*
 *   Handout for foundation routines for		*
 *    D.Sem. labs;					*
 *   This is the code for the fundamental 		*
 *    models of stores and environments. You will	*
 *    need to provide the definitions of the types	*
 *    used here, i.e. Denotable, Value, etc..		*
 * ----------------------------------------------------	*)



(* --------------------------------------------	*)
(* ---------- Auxiliary Semantic Functions ----	*)
fun sum   (x, y) = x + y:int;
fun diff  (x, y) = x - y:int;
fun prod  (x, y) = x * y:int;

fun lessthan  (x, y) = x < (y:int);

(* ---------- Storage   ---------- *)
(*
fun deallocate sto loc:Location = sto;	(* ... later *)
*)

datatype Sval  = stored of Storable | undef | unused;

(*                        --bot---   --top---   ----data--------- *)
datatype Store = store of Location * Location * (Location -> Sval);

val sto_init  =  fn loc:Location => unused;
val sto_null  =  store( 1, 0, sto_init);

fun update (store(bot,top,data), loc, v) = 
	let fun new adr =  if adr=loc
			   then stored v else (data adr);
	in store( bot, top, new)
	end;
                                            
		(* fetch from store and convert into Storable (=Value) *)
fun fetch  (store(bot,top,data), loc:Location)  =
	let fun stored_value(stored stble) = stble
	      | stored_value(unused)       = raise fail
	      | stored_value(undef)        = raise fail
	in stored_value( data loc)
	end;

		(* create a new "undefined" location in a store *)
fun allocate ( store(bot,top,data) )  =
	let val newtop = top+1
	    fun new adr =  if adr=newtop
			   then undef else (data adr);
	in (store( bot, newtop, new), newtop)
	end;


(* ---------- Envirionment   ---------- *)
type  Environ  =  Ident -> Denotable;

val env_null  =  fn i:Ident => unbound;
fun bind  (name, vl) =  fn idn => if idn=(name:Ident)
                                     then bound(vl) else unbound;
fun find  (env:Environ, idn)  =
	let fun getbv(bound bdbl) = bdbl
	      | getbv(unbound)    = raise fail
	in getbv( env idn)
	end;
fun overlay  (env', env:Environ)  =
	fn idn => let val val' = env' idn
	          in if val'<>unbound then val'
	                              else env idn
		  end;

