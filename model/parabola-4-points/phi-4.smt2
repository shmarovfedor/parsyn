(set-logic QF_NRA_ODE)
(declare-fun t () Real)
(declare-fun v () Real)
(declare-fun k () Real)

(declare-fun t_0 () Real)
(declare-fun v_0 () Real)

(declare-fun t_3 () Real)
(declare-fun v_3 () Real)

(declare-fun k_0 () Real)
(declare-fun k_3 () Real)

(declare-fun time_0 () Real)

(define-ode flow_1 ((= d/dt[v] (* k t)) (= d/dt[t] 1) (= d/dt[k] 0)))

(assert (<= time_0 5))
(assert (<= 0 time_0))

(assert 
	(and
		(= [v_3 t_3 k_3] (integral 0. time_0 [v_0 t_0 k_0] flow_1))
		
		(= t_0 0)
		(>= v_0 -0.00001)
		(<= v_0 0.00001)

		(= t_3 3)
		(>= v_3 8.99)
		(<= v_3 9.01)

		(= k_0 k_3)
	))
(check-sat)
(exit)
