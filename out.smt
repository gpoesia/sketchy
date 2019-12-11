(set-logic UFBV)
(declare-const hole_1 (_ BitVec 32))
(declare-const hole_0 (_ BitVec 32))
(assert (forall ((x_0 (_ BitVec 32))
(y_0 (_ BitVec 32)))
(let ((x_1 (bvadd x_0 y_0)))
(let ((x_2 (bvadd x_1 y_0)))
(let ((x_3 (bvadd x_2 y_0)))
(let ((z_0 (bvadd (bvmul x_0 hole_0) (bvmul y_0 hole_1))))
(= x_3 z_0)))))))
(check-sat)
(get-model)