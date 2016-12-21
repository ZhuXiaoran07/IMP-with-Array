module ARRAY-SPEC
imports IMP
//syntax Map::="arraySeq""("Int")"  [function]
//rule arraySeq(I)=>value-array(I-Int 1)|->I arraySeq(I-Int 1)
//rule arraySeq(-1)=>.Map

rule 

<k>
(while(i<n-1){
a[i]=i;
i=i+ 1;
}
=>.K)
...
</k>
<arrayEnv>
<arrayId>a</arrayId>
//<arrayStore>...value-array(X)|->V:Int value-array(X+Int 1)|->(_=>V+Int 1)...</arrayStore>
<arrayStore>_=>?_:Map</arrayStore>
</arrayEnv>

<env>
n|->LN:Int
i|->LI:Int
</env>
<store>
LN|->N:Int
LI|->(I:Int=>N -Int 1)
</store>
<time>
T:Int=>T+Int ?T1:Int
</time>
requires N>Int 1 andBool I <=Int (N -Int 1)
ensures ?T1>Int 0

endmodule