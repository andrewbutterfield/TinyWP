# TinyWP

Current problem with too many commas

ghci> bigArith
F "mul" [F "add" [I 42,I 99],F "add" [F "mul" [I 1,I 2],F "mul" [I 3,I 4]]]

ghci> ppExpr 40  bigArith 
[(0,4,"mul("),(8,13,"ppPrefix-NYFi"),(0,1,")")]
ghci> putFrags it
mul(
        ppPrefix-NYFi
)

ghci> ppExpr 45  bigArith 
[(0,4,"mul("),(2,73,"add,(,42,,,99,),add,(,mul,,,(,,,1,,,,,,,2,,,),,,mul,,,(,,,3,,,,,,,4,,,),)"),(0,1,")")]
ghci> putFrags it
mul(
  add,(,42,,,99,),add,(,mul,,,(,,,1,,,,,,,2,,,),,,mul,,,(,,,3,,,,,,,4,,,),)
)
