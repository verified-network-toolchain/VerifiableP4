i : Z
ValueBaseInt (to_lobool w i)
ValueBaseInt (to_lobool w 1)
Ops.add (ValueBaseInt (to_lobool w i)) (ValueBaseInt (to_lobool w 1))
= (ValueBaseInt (to_lobool w (i+1)))
ValueBaseInt (to_lobool w i)

Lemma test :
  forall (xi yi : Z), (z : Sval)
    (pre := (mem_denote
      [(["a"], ValBaseStruct [("x", ValBaseInt (P4Arith.to_lbool 8%N xi));
                              ("y", ValBaseInt (P4Arith.to_lbool 8%N yi));
                              ("z", z)])]),
    0 <= xi < 100 ->
    0 <= yi < 100 ->
    a.x + a.y

(x + 1) (a.x)

P4Arith.to_loptbool : N -> Z -> list (option bool)
ValBaseInt (to_lobool w i) 

    
    (expr := MkExpression dummy_tags (M
    
    
    
    hoare_expr ge p pre 
    
mem_assertion
lsv := P4Arith.to_loptbool w x 
eval_sval_to_val (ValBasebit (P4Arith.to_loptbool w x)) = Some (ValBasebit (P4Arith.to_lbool w x))
(ValBasebit (P4Arith.to_loptbool w (x+1)))