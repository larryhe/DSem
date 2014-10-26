-----------------------------------------------------------------------------
--
-- Module      :  :  Imp'c_tests
-- APL:: IMPc DSem - Lab Tests
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
--
-----------------------------------------------------------------------------
module DSemImplTests (

testSuits        -- export the test results...

) where
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
-- --------------------------------------------------------
-- ==== Tests::
testSuits = do print "------ APL:: DSem_impc"
               test1()   -- Expressions
               test2()   -- Declarations
               test3()   -- simple program.2
               test4()   -- simple program.3
               test5()   -- simple program.4
               test6()   -- simple program.5

