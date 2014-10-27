-----------------------------------------------------------------------------
--
-- Module      :  :  DSem_imp
-- APL Lab Template in Haskell!!
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
-- Imp: expressions language (Watt, Ex. 3.6)	--
--      with commands    (store).. 		--
--      and  definitions (evnironment).. 	--
--
--     (A nicer version of Ex. 4.7 from text)	--
-- --------------------------------------------	--
--
-----------------------------------------------------------------------------

-- --------------------------------------------	--
-- ---------- Abstract Syntax -----------------	--
			-- terminal nodes of the syntax --
type      Numeral  = Int
type      Ident    = String

			-- parsed phrases of the abstract syntax --
data Command =
              Skip
            | Assign   (Ident,       Expression)
            | Letin    (Declaration, Command   )
            | Cmdcmd   (Command,     Command   )
            | Ifthen   (Expression,  Command, Command)
            | Whiledo  (Expression,  Command   )
            | Proccall (Ident, Expression)

data Expression =
            Num    Numeral
    	    | False_
    	    | True_
    	    | Notexp   Expression
    	    | Id       Ident
    	    | Sumof   (Expression,  Expression)
    	    | Subof   (Expression,  Expression)
    	    | Prodof  (Expression,  Expression)
    	    | Less    (Expression,  Expression)
    	    | Equ    (Expression,  Expression)
           deriving Show

data Declaration =
	      Constdef (Ident,  Expression)
	    | Vardef   (Ident,  TypeDef   )
        | ProcDef     (Ident,  Ident, Command)

data TypeDef =
	      Bool | Int
	
-- --------------------------------------------	--
-- ---------- Semantic Domains ----------------	--

type	Integer	= Int
type	Boolean	= Bool
type	Location	= Int

data	Value	= IntValue    Int
		        | TruthValue  Bool
                  deriving (Eq, Show)

type	Storable  = Value
type	Procedure  = Value -> Store -> Store

instance Show (a->b) where show a= "function"

data	Bindable  = Const Value | Variable Location | Proc Procedure
                    deriving (Show)

data	Denotable = Unbound | Bound Bindable
                    deriving (Eq, Show)

instance Eq Bindable where _ == _ = True

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation :: Int         -> Value
evaluate  :: Expression  -> Environ -> Store ->  Value
elaborate :: Declaration -> Environ -> Store ->  (Environ,Store)
execute   :: Command     -> Environ -> Store ->  Store

-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y

lessthan  (x, y) = x < y
equal  (x, y) = x == y

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval  = Stored Storable | Undef | Unused deriving (Show)

-- The actual storage in a Store
type DataStore = Location -> Sval

--	                 --bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore) 

update :: (Store, Location, Value) -> Store
update (Store(bot,top,sto), loc, v) =
	let new adr = if adr==loc
			      then Stored v else (sto adr)
	in Store( bot, top, new)

		-- fetch from store, and convert into Storable (=Const)
fetch ::(Store,Location) -> Storable
fetch  (Store(bot,top,sto), loc)  =
	let stored_value(Stored stble) = stble
	    stored_value(Unused)       = error ("Store: Unused")
	    stored_value(Undef)        = error ("Store: Undefined ")
	in  stored_value(sto loc)

		-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot,top,sto) )  =
	let newtop  = top+1
	    new adr = if adr==newtop
			      then Undef else (sto adr)
	in (Store( bot, newtop, new), newtop)

-- ---------- Envirionment   ----------
type  Environ  =  Ident -> Denotable

bind :: (Ident,Bindable) -> Environ
bind  (name, val) =  \id -> if id==name
                            then Bound(val) else Unbound

-- look through the layered environment bindings
find :: (Environ, Ident) -> Bindable
find  (env, id)  =
	let getbv(Bound bdbl) = bdbl
	    getbv(Unbound)    = error ("undefined: " ++ id)
	in getbv( env id)

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  =
	\id -> let val = env' id
	       in  if val/=Unbound then val
	                            else env id

-- ---------- Etc...
--    coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)

-- bind-parameter and give-argument utilities
bindParam :: (Ident, Value) -> Environ
bindParam (name, val) = bind (name, Const val)

giveArg :: (Expression, Environ, Store) -> Value
giveArg (exp, env, sto) = evaluate exp env sto

-- ---------- Initialize system  ----------
env_null :: Environ
env_null =  \i -> Unbound

--  store_null =  empty (=0), addressing starts at 1
sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

-- --------------------------------------------
-- ---------- Semantic Equations --------------

				-- from integer to Const Value
valuation ( n ) = IntValue(n)

execute ( Skip ) env sto = sto

execute ( Assign(name,exp) ) env sto  =
     		let rhs = evaluate exp env sto
     		    Variable loc = find( env,name)
     		in  update( sto, loc, rhs)

execute ( Letin(def,c) ) env sto =
            let (env', sto') = elaborate def env sto
            in execute c (overlay(env', env)) sto'

            --implement C1;C2 semantics 3.59d 
execute ( Cmdcmd(c1,c2) ) env sto  =
            execute c2 env (execute c1 env sto)

          --implement if else semantics 3.59e
execute ( Ifthen(e,c1,c2) ) env sto =
            let TruthValue b1 = evaluate e env sto
            in if b1 == True then execute c1 env sto
                else execute c2 env sto

execute ( Whiledo(e,c) ) env sto =
            let exe_while env' sto' = let TruthValue b1 = evaluate e env' sto' in if b1 == True then exe_while env' (execute c env' sto') else sto'
            in exe_while env sto

execute (Proccall(name, exp)) env sto = 
            let Proc proc = find (env, name) in 
                    let arg = giveArg(exp, env, sto) in proc arg sto

     			-- simple, just build a Const
evaluate ( Num(n)  )  env sto  = IntValue n
evaluate ( True_   )  env sto  = TruthValue  True
evaluate ( False_  )  env sto  = TruthValue  False

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env sto  = coerc( sto, find(env,n) )

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( add(i1,i2) )

evaluate ( Subof(e1,e2) ) env sto =
        let IntValue i1 = evaluate e1 env sto
            IntValue i2 = evaluate e2 env sto
        in IntValue (diff(i1, i2))

evaluate ( Prodof(e1,e2) ) env sto =
        let IntValue i1 = evaluate e1 env sto
            IntValue i2 = evaluate e2 env sto
        in IntValue (prod(i1, i2))

evaluate ( Less(e1,e2) ) env sto =
        let IntValue i1 = evaluate e1 env sto
            IntValue i2 = evaluate e2 env sto
        in TruthValue (lessthan(i1, i2))

evaluate ( Equ(e1,e2) ) env sto =
        let IntValue i1 = evaluate e1 env sto
            IntValue i2 = evaluate e2 env sto
        in TruthValue (lessthan(i1, i2))

evaluate ( Notexp(e) ) env sto =
        let TruthValue e1 = evaluate e env sto
        in TruthValue (not e1)

{-- ------- * Later...
     			-- layer environment, and compute result
evaluate ( leten(def,e) ) env sto =
     	let (env', sto') = elaborate def env sto
		in  evaluate e (overlay (env', env)) sto'
   ------- --}

elaborate ( Constdef(name,e) ) env sto =
     	let v = evaluate e env sto
		in  ( bind(name, Const  v), sto )

elaborate ( Vardef(name,tdef) ) env sto =
     	let (sto',loc) = allocate sto
		in  ( bind(name, Variable loc), sto' )

elaborate (ProcDef(name, fp, comm)) env sto = 
        let proc arg sto' = let parenv = bindParam (fp, arg) in execute comm (overlay (parenv, env)) sto'
        in (bind(name, Proc proc), sto)

-- ============================================	 --
-- run test suits 
input, result :: Expression
input  = Id "input"       -- a shorthand..
result = Id "result"

e1 = Num 2
e2 = Sumof (Num 1, Num 2)

-- Trace_flag = "Test: expressions    [ 2, 1+2]"
a1 = evaluate e1 env_null sto_null;        --  = 2
a2 = evaluate e2 env_null sto_null;        --  = 3

-- Trace_flag = "Test: expressions    [ 1+2*3 = 7 ]"
a3 = evaluate (Sumof (Num 1, Prodof (Num 2, Num 3))) env_null sto_null; --  = 7

test1() = do print ":---: expressions  [ 2, 1+2, 1+2*3 ]"
             print a1
             print a2
             print a3
-- ------------------------- --
dx = Constdef ("x" ,Num 2)      -- a declaration --
a4 = elaborate dx env_null sto_null

test2() = do print ":---: declaration    {const x = 2}"
             print (find(fst(a4), "x"))

{- -----------------------------------------------
 *   let value x ~ 2
 *   in let var y : int
 *      in  y:= 3
 *          if x<y then y:=1
 *                 else y:=2
 --}

cmd1 =
  Letin  (Constdef ("x", Num 2),
         Letin (Vardef ("y", Int),
                Cmdcmd (Assign ("y" , Num 3),
                        Ifthen (Less (Id "x", Id "y"),
                                Assign ("y" , Num 1),
                                Assign ("y" , Num 2)
                                )
                        )
                )
         )

cmd2 =
  Letin (Constdef ("x" , Num 2),
        Letin (Vardef ("y", Int),
               Cmdcmd (Assign ("y" , Num 3),
                       Assign ("y" , Num 10)
                       )
                )
        )

                -- get Answer --
sto2  = execute cmd1  env_null sto_null
sto3  = execute cmd2  env_null sto_null

test3() = do print ":---: Simple Program.2 "
             print " let value x = 2 in "
             print " let var y: Int in "
             print " y = 3 if x<y then y:=1 else y:=2"
             print (fetch(sto2, 1))

test4() = do print ":---: Simple Program.3 "
             print " let value x = 2 in "
             print " let var y: Int in "
             print " y:=3 ; y:=10"
             print (fetch(sto3, 1))
{- --------------------------------------------------------
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z := 0
 *             z := z+1
 --}
x    = Id "x"      -- some shorthands...
y    = Id "y"
z    = Id "z"
zero = Num 0
one  = Num 1

cmd3 =
  Letin (Constdef ("x" , Num 2),
        Letin (Vardef ("y", Int),
               Cmdcmd (Assign ("y" , Num 3),
                       Letin (Vardef ("z", Int),
                              Cmdcmd (
                                      Assign ("z", zero),
                                      Assign ("z", Sumof (z,one))
                                    )
                            )
                      )
         )
    )

sto5 = execute cmd3  env_null sto_null

test5() = do print ":---: Simple Program.4 z will evluated to 1 "
             print " let Const  x ~ 2 "
             print " in let var y : int "
             print "    in y := 3 "
             print "       let var z : int "
             print "       in  z := 0 "
             print (fetch(sto5, 2))

{- --------------------------------------------------------
 *   // a loop
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z:= 0            { multiply z = x*y }
 *             while 0<y do  z := z+x; y := y-1
 --}
cmd4 =
  Letin (Constdef ("x" ,Num 2),
        Letin  (Vardef ("y", Int),
                Cmdcmd (Assign ("y" , Num 3),
                        Letin (Vardef ("z", Int),
                               Cmdcmd (Assign ("z", zero),
                                       Whiledo (Less (zero, y),
                                                Cmdcmd (Assign ("z" , Sumof(z, x)),
                                                        Assign ("y" , Subof(y,one))
                                                        )
                                               )
                                      )
                              )
                       )
              )
        )

sto6 = execute cmd4  env_null sto_null

test6() = do print ":---: Simple Program.5  test loop z will be evaluated to 6"
             print "let Const  x ~ 2 "
             print "in let var y : int "
             print "   in y := 3 "
             print "      let var z : int "
             print "      in  z:= 0            { multiply z = x*y } "
             print "             while 0<y do  z := z+x; y := y-1"
             print (fetch(sto6, 2))

{- --------------------------------------------------------
 *   // a loop
 *   let proc factorial n
 *   in if n == 1 then 1 else n * factorial n-1
 --}
procall1 =
  Letin (ProcDef ("factorial" , "n",
                    Letin  (Vardef ("y", Int),
                            Cmdcmd (Assign ("y" , Id "n"),
                                    Letin (Vardef ("z", Int),
                                        Cmdcmd (Assign ("z", one),
                                                Whiledo (Less (zero, y),
                                                            Cmdcmd (Assign ("z" , Prodof(z, y)),
                                                                    Assign ("y" , Subof(y,one))
                                                                    )
                                                        )
                                                )
                                        )
                                )
                        )),
        Proccall  ("factorial", Num 5)
        )

sto7 = execute procall1  env_null sto_null
test7() = do print ":---: Simple Program.6  test loop z will be evaluated to 120"
             print "   let proc factorial n "
             print "   in if n == 1 then 1 else n * factorial n-1 "
             print (fetch(sto7, 2))
-- --------------------------------------------------------
-- ==== Tests::
testSuits = do print "------ APL:: DSem_impc"
               test1()   -- Expressions
               test2()   -- Declarations
               test3()   -- simple program.2
               test4()   -- simple program.3
               test5()   -- simple program.4
               test6()   -- simple program.5
               test7()   -- simple program.5

