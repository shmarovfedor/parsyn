(set-logic QF_NRA_ODE)
(declare-fun t () Real)
(declare-fun v () Real)
(declare-fun k () Real)

(declare-fun t_0 () Real)
(declare-fun v_0 () Real)

(declare-fun t_1 () Real)
(declare-fun v_1 () Real)

(declare-fun t_2 () Real)
(declare-fun v_2 () Real)

(declare-fun t_3 () Real)
(declare-fun v_3 () Real)

(declare-fun k_0 () Real)
(declare-fun k_1 () Real)
(declare-fun k_2 () Real)
(declare-fun k_3 () Real)

(assert (<= 0 k_0))
(assert (<= k_0 4))
(assert (<= 0 k_1))
(assert (<= k_1 4))
(assert (<= 0 k_2))
(assert (<= k_2 4))
(assert (<= 0 k_3))
(assert (<= k_3 4))

(declare-fun time_0 () Real)
(declare-fun time_1 () Real)
(declare-fun time_2 () Real)

(define-ode flow_1 ((= d/dt[v] (* k t)) (= d/dt[t] 1) (= d/dt[k] 0)))

(assert (<= time_0 5))
(assert (<= 0 time_0))

(assert (<= time_1 5))
(assert (<= 0 time_1))

(assert (<= time_2 5))
(assert (<= 0 time_2))

(assert 
	(and
		(= [v_1 t_1 k_1] (integral 0. time_0 [v_0 t_0 k_0] flow_1))
		(= [v_2 t_2 k_2] (integral 0. time_1 [v_1 t_1 k_1] flow_1))
		(= [v_3 t_3 k_3] (integral 0. time_0 [v_2 t_2 k_2] flow_1))
		
		(= t_0 0)
		(>= v_0 -0.00001)
		(<= v_0 0.00001)

		(= t_1 1)
		(= t_2 2)
		(= t_3 3)

		(or
			(< v_1 0.99)
			(> v_1 1.01)
			(< v_2 3.99)
			(> v_2 4.01)
			(< v_3 8.99)
			(> v_3 9.01)
		)

		(= k_0 k_1)
		(= k_1 k_2)
		(= k_2 k_3)

	))
(check-sat)
(exit)
