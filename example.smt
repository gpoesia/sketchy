;int W = 32;
;void main (bit[W] x, bit[W] y) {
;    bit[W] xold = x;
;    bit[W] yold = y;
;    if(??){x = x ^ y; } else { y = x ^ y; }
;    if(??){x = x ^ y; } else { y = x ^ y; }
;    if(??){x = x ^ y; } else { y = x ^ y; }
;    assert y == xold && x == yold;
;}
;
;Intermediate representation
;
;void main (bit[32] x0, bit[32] y0) {
;    bit[32] xold0 = x0;
;    bit[32] yold0 = y0;
;    if(c0) { x1 = x0 ^ y0; } else { y1 = x0 ^ y0; }
;    x2 = phi(x1, x0);
;    y2 = phi(y0, y1);
;    if(c1) { x3 = x2 ^ y2; } else { y3 = x2 ^ y2; }
;    x4 = phi(x3, x2);
;    y4 = phi(y2, y3);
;    if(c2) { x5 = x4 ^ y4; } else { y5 = x4 ^ y4; }
;    x6 = phi(x5, x4);
;    y6 = phi(y4, y5);
;    assert y6 == xold0 && x6 == yold0;
;}
;
;output constraints:

(set-logic UFBV)
(declare-const c0 (_ BitVec 32))
(declare-const c1 (_ BitVec 32))
(declare-const c2 (_ BitVec 32))

(assert (forall ((x0 (_ BitVec 32)) (y0 (_ BitVec 32)))
		(let ((xold0 x0))
		(let ((yold0 y0))
		 ; write down all assignments inside of ite
		(let ((x1 (bvxor x0 y0)))
		(let ((y1 (bvxor x0 y0)))
		 ; this is how you write phi function
		(let ((x2 (ite (not (= c0 (_ bv0 32))) x1 x0)))
		(let ((y2 (ite (not (= c0 (_ bv0 32))) y0 y1)))
		(let ((x3 (bvxor x2 y2)))
		(let ((y3 (bvxor x2 y2)))
		(let ((x4 (ite (not (= c1 (_ bv0 32))) x3 x2)))
		(let ((y4 (ite (not (= c1 (_ bv0 32))) y2 y3)))
		(let ((x5 (bvxor x4 y4)))
		(let ((y5 (bvxor x4 y4)))
		(let ((x6 (ite (not (= c2 (_ bv0 32))) x5 x4)))
		(let ((y6 (ite (not (= c2 (_ bv0 32))) y4 y5)))
	 	  (and (= y6 xold0) (= x6 yold0))))))))))))))))))
 
(check-sat)
(get-model)
