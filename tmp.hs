module ImpcTest (

impTests        -- export the test results...

) where

type    Ident    = String
type    Integer = Int
type    Boolean = Bool
type    Location    = Int

data    Value   = IntValue    Int
                | TruthValue  Bool
                  deriving (Eq, Show)

type    Storable  = Value

data    Bindable  = Const Value | Variable Location
                  deriving (Eq, Show)

data    Denotable = Unbound | Bound Bindable
                  deriving (Eq, Show)

-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto    -- ... later --

data Sval  = Stored Storable | Undef | Unused

-- The actual storage in a Store
type DataStore = Location -> Sval

--                   --bot---   --top---  --data---
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

sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

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

