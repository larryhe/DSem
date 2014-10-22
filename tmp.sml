type		Integer	= int;
type		Boolean	= bool;
type		Location= int;
type		Ident = string;
datatype	Value	= integer     of int
            | id of Ident
			| truth_value of bool;

type		Storable  = Value;

datatype	Bindable  = value of Value | variable of Location;

datatype	Denotable = unbound | bound of Bindable ;

type Environ = Ident -> Denotable;

exception fail;

val env_null = fn i:int => unbound;

fun bind (name, vl) = fn idn => if idn=(name:Ident) then bound(vl) else unbound;

