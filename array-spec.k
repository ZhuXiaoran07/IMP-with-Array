module ARRAY-SPEC
imports IMP


rule 

<k>
(while(i<n-1){
i=i+ 1;
}
=>.K)
...
</k>
<env>
n|->LN:Int
i|->LI:Int
</env>
<store>
LN|->N:Int
LI|->(I:Int=>N)
</store>
<time>
T:Int=>T+Int ?T1:Int
</time>
requires N>Int 1 andBool I <=Int (N)
ensures ?T1>Int 0

endmodule
