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
         -- | Leten   (Declaration, Expression)
         --   deriving Show

data Declaration =
	      Constdef (Ident,  Expression)
	    | Vardef   (Ident,  TypeDef   )

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

data	Bindable  = Const Value | Variable Location
                  deriving (Eq, Show)

data	Denotable = Unbound | Bound Bindable
                  deriving (Eq, Show)

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

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval  = Stored Storable | Undef | Unused

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

-- ============================================	 --
-- run test suits 
input, result :: Expression
input  = Id "input"       -- a shorthand..
result = Id "result"

e1 = Num 2
e2 = Sumof (Num 1) (Num 2)

-- Trace_flag = "Test: expressions    [ 2, 1+2]"
a1 = evaluate e1 env_null sto_null;        --  = 2
a2 = evaluate e2 env_null sto_null;        --  = 3

-- Trace_flag = "Test: expressions    [ 1+2*3 = 7 ]"
a3 = evaluate (Sumof (Num 1) (Prodof (Num 2) (Num 3)))
                        env_null sto_null; --  = 7

test1() = do print ":---: expressions  [ 2, 1+2, 1+2*3 ]"
             print a1
             print a2
             print a3
-- ------------------------- --
-- dx = Constdef "x" (Num 2)      -- a declaration --
-- a4 = elaborate dx env_null sto_null

{- ========== --
a5 = evaluate (  Leten  dx (Sumof (Num 1) (Id "x") ) )
                        env_null kont_null sto_null; -- = 3
-- ========== --}
-- test2() = do print ":---: declaration    {const x = 2}"
--              print a4
-- =============================================== --
--   result := input
-- pgm1 = Prog( Assign "result" input )

                        -- run the program on an input --
-- test3() = do print ":---: {result = input}  [1, 2]"
--              print (run pgm1  1)
--              print (run pgm1  2)
-- =============================================== --
--   result := input + 1
--
-- pgm2 = Prog( Assign "result" (Sumof (Num 1) input ) )

                        -- run the program on inputs --
-- test4() = do print ":---: {result = input+1}  [2, 3]"
--              print $ run pgm2  1
--              print $ run pgm2  2

{- -----------------------------------------------
 *   let value x ~ 2
 *   in let var y : int
 *      in  y:= 3
 *          if x<y then y:=1
 *                 else y:=2
 --}

-- Note that we do no output, so need to dump store for results
-- cmd' =
--   Letin  (Constdef "x" (Num 2))
--          (Letin (Vardef "y" Int)
--                 (Cmdcmd (Assign "y" (Num 3))
--                         (Ifthen (Less (Id "x") (Id "y"))
--                                 (Assign "y" (Num 1))
--                                 (Assign "y" (Num 2))
--                                 )
--                         )
--                 )
--
-- cmd =
--   Letin (Constdef "x" (Num 2))
--         (Letin (Vardef "y" Int)
--                (Cmdcmd (Assign "y" (Num 3))
--                        (Assign "y" (Num 1))
--                        )
--                 )
--
--                 -- get Answer --
-- a9  = execute cmd  env_null sto_null
--
--                 -- get a full set Answers..!  --
-- a9b  = execute cmd  env_null sto_null
--
-- test5() = do print ":---: Simple Program.2  -> [1]"
--              -- trace("Pre-a9") print "Pre-a9"
--              print a9
--              print a9b
             -- print $ run (Prog cmd) 000

{- --------------------------------------------------------
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z := 0
 *             z := z+1
 --}
-- x    = Id "x"      -- some shorthands...
-- y    = Id "y"
-- z    = Id "z"
-- zero = Num 0
-- one  = Num 1
--
-- cmd3 =
--   Letin (Constdef "x" (Num 2))
--         (Letin (Vardef "y" Int)
--                (Cmdcmd (Assign "y" (Num 3))
--                        (Letin (Vardef "z" Int)
--                               (Cmdcmd (Assign "z" zero)
--                                       (Assign "z" (Sumof z one))                                      )
--                        )
--                 )
--          )
--
-- a10a = execute cmd3  env_null sto_null
-- a10b = execute cmd3  env_null sto_null
--
-- test6() = do print ":---: Simple Program.3  -> [3,1]"
--              -- print (run (Prog cmd3) 0)
--              print a10b

{- --------------------------------------------------------
 *   // a loop
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z:= 0            { multiply z = x*y }
 *             while 0<y do  z := z+x; y := y-1
 --}
-- cmd4 =
--   Letin (Constdef "x" (Num 2))
--         (Letin  (Vardef "y" Int)
--                 (Cmdcmd (Assign "y" (Num 3))
--                         (Letin (Vardef "z" Int)
--                                (Cmdcmd (Assign "z" zero)
--                                        (Whiledo (Less zero y)
--                                          (Cmdcmd (Assign "z" (Sumof z x  ))
--                                                  (Assign "y" (Subof y one))
--                                                   )
--                                         )
--                                 )
--                          )
--                  )
--          )
--
-- a11a = execute cmd4  env_null sto_null
-- a11b = execute cmd4  env_null sto_null

-- test7() = do print ":---: Simple Program.4  -> [0,6, Halt]"
             -- print $ run (Prog cmd4) 0
             -- print a11b
-- --------------------------------------------------------
-- ==== Tests::

-- impcAns = [ a1, a2, a3a, a4, a5, a6, a7, a8 ]
-- impcAns = [ a1, a2, a3, a4, a6, a7]

-- testSuits = do print "------ APL:: DSem_impc"
               -- test1()   -- Expressions
               -- test2()   -- Declarations
               -- test3()   -- Expressions
               -- test4()   -- Expressions
               -- test5()   -- simple program.2
               -- test6()   -- simple program.3
               -- test7()   -- simple program.4

