module IMP-SYNTAX
  syntax AExp  ::= Int | String | Id
                 | "++" Id
				 | Id "[" AExp "]"            [strict(2)]
				 | Id "[" "]"
                 | "read" "(" ")"
				 | "SymInt"
				 | "SymInt1"
                 > AExp "/" AExp              [left, strict, division]
				 | AExp "%" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
				 | AExp "-" AExp              [left, strict]
                 > "spawn" Block
                 > Id "=" AExp   

				 [strict(2)]
				 | Id "[" AExp "]" "=" AExp              [strict(3, 2)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
				  | AExp "<" AExp             [seqstrict, latex({#1}\leq{#2})]
				 | AExp "==" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
				 | "int" Id "[" AExp "]"  ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "join" AExp ";"            [strict]

  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  syntax Stmts ::= List{Stmt,""}
endmodule


module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool | String

  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue">
                      <k color="green"> $PGM:Stmts </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <id color="black"> 0 </id>
                    </thread>
                  </threads>
                  <store color="red"> .Map </store>
				   <arrayEnvs>
				  <arrayEnv multiplicity="*">
				  <arrayId> .K </arrayId>
				  <arrayStore> .Map </arrayStore>
				  </arrayEnv>
				  </arrayEnvs>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
				   <time> 0 </time>
                </T>
rule SymInt =>?_:Int
rule SymInt1 =>?_:Int

syntax KItem ::="["Id "," AExp "]"
//syntax KItem ::= "value-array" "("  Int  ")"
syntax Map::="arraySeq""("Int")"  [function]
rule arraySeq(I)=>(I|->I) arraySeq(I-Int 1) requires I>=Int 0
rule arraySeq(-1)=>.
syntax KItem::=  "update" "(" Id "," Int "," Int ")"
syntax Map::=	"array-map" "(" Int "," Int ")"  [function]
syntax Map::= "arrayIni" "("Int")"  [function]

rule arrayIni(I)=>I|->?_:Int arrayIni(I-Int 1) requires I>=Int 0
rule array(-1)=>.


rule <k> int X:Id[I:Int];=>[X,I]...</k>
     <env>M:Map</env>
	 when notBool(I in keys(M)) 

 rule <k>int X:Id[I:Id];=> [X, I']...</k>
 <env>...I|->N...</env>
 <store>...N|->I':Int...</store>
 
 //array

// AExp
rule array-map(I, L)=>(L-Int 1|->0) array-map(I, L-Int 1)
requires L>Int 0

rule array-map(I, 0)=>.Map

rule <k> ([X, I]=>.) ...</k>
 <arrayEnvs> AE:Bag=>AE <arrayEnv>
				  <arrayId> X:Id </arrayId>
				  <arrayStore> array-map(I,I) </arrayStore>
				  </arrayEnv>  </arrayEnvs>
<time> T=>T+Int 1 </time>

rule X:Id[I1:Int]=I2=>update(X,I1,I2)



rule <k>update(X,I1,I2)=>I2 ...</k>
<arrayEnv>
				  <arrayId> X:Id </arrayId>
				  <arrayStore>... I1:Int|->(_=>I2:Int) ...</arrayStore>
				  </arrayEnv>
//<store> ... value-array(X, I1)|->(_=>I2)...</store>
<time> T=>T+Int 1 </time>


rule <k>(X:Id[I1]=>I2:Int)...</k>
//<env>...X|->I...</env>
<arrayEnv>
		 <arrayId> X:Id </arrayId>
		<arrayStore>... I1|->I2 ...</arrayStore>
				  </arrayEnv>
				  


// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>
       	   [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store> 
       <time> M=>M+Int 1 </time> 	   [increment]
  rule <k> read() => I ...</k>
       <in> ListItem(I:Int) => .List ...</in>  [read]
  rule <k>(I1 / I2 => I1 /Int I2)...</k> <time> M=>M+Int 1 </time>   requires I2 =/=Int 0
  rule <k>(I1 + I2 => I1 +Int I2)...</k><time> M=>M+Int 1</time> 
   rule <k>(I1 - I2 => I1 -Int I2)...</k><time> M=>M+Int 1</time> 
  rule <k>(Str1 + Str2 => Str1 +String Str2)...</k><time> M=>M+Int 1 </time> 
  rule <k>(I1 % I2 => I1 %Int I2)...</k><time> M=>M+Int 1</time> requires I2 =/=Int 0
// BExp
  rule <k>(I1 <= I2 => I1 <=Int I2)...</k><time> M=>M+Int 1 </time>
  rule <k>(I1 < I2 => I1 <Int I2)...</k><time> M=>M+Int 1 </time>
  rule <k>(I1 == I2 => I1 ==Int I2)...</k><time> M=>M+Int 1 </time>
  rule <k>(! T => notBool T)...</k><time> M=>M+Int 1 </time>
  rule <k>(true && B => B)...</k><time> M=>M+Int 1 </time>
  rule <k>(false && _ => false)...</k><time> M=>M+Int 1 </time>
// Block
  rule <k> {Ss} => Ss ~> Rho ...</k> <env> Rho </env>  [structural]
  rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]
// Stmt
  rule _:Int; => .
  rule <k> X = I:Int =>I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store> 
		<time> M=>M+Int 1 </time>[assignment]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {.Stmts}  [structural]

  syntax KItem ::= "#initVars" "{" Ids"|" Int "}"
					

  
  
  rule <k> #initVars {X, Xs => Xs | A => A +Int 1} ... </k>
	  <env> Rho => Rho[X <- A] </env>
      <store>... .Map => A |-> 0 ...</store>
	  <time> M=>M+Int 1 </time>
  
  rule #initVars {.Ids | _} => .	[structural] 
  
  rule int X:Ids; => #initVars {X | 0}		[structural]

  syntax Printable ::= Int | String
/* currently it is necessary to subsort Printable to AExp,
  but future K should be able to infer that automatically. */
  syntax AExp ::= Printable
  context print(HOLE:AExp, AEs:AExps);
  
  rule <k> print(P:Printable,AEs => AEs); ...</k>
       <out>... .List => ListItem(P) </out>  [print]
  rule print(.AExps); => .  [structural]

  rule <k> halt; ~> _ => . </k>

  rule <k> spawn S => !T:Int ...</k> <env> Rho </env>
       (.Bag => <thread>... <k> S </k> <env> Rho </env> <id> !T </id> ...</thread>)
  rule <k> join(T:Int); => . ...</k>
       <thread>... <k> . </k> <id> T </id> ...</thread>

// Stmts
  rule .Stmts => .                 [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss  [structural]
  
// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
			  | "a"	    [token]
			  | "b"     [token]
			  | "c"      [token]
			  | "i"		[token]
 
endmodule
