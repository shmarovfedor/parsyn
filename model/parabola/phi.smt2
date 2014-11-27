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

(declare-fun t_4 () Real)
(declare-fun v_4 () Real)

(declare-fun t_5 () Real)
(declare-fun v_5 () Real)

(declare-fun k_0 () Real)
(declare-fun k_1 () Real)
(declare-fun k_2 () Real)
(declare-fun k_3 () Real)
(declare-fun k_4 () Real)
(declare-fun k_5 () Real)

(assert (<= 0 k_0))
(assert (<= k_0 4))
(assert (<= 0 k_1))
(assert (<= k_1 4))
(assert (<= 0 k_2))
(assert (<= k_2 4))
(assert (<= 0 k_3))
(assert (<= k_3 4))
(assert (<= 0 k_4))
(assert (<= k_4 4))
(assert (<= 0 k_5))
(assert (<= k_5 4))

(declare-fun time_0 () Real)
(declare-fun time_1 () Real)
(declare-fun time_2 () Real)
(declare-fun time_3 () Real)
(declare-fun time_4 () Real)

(define-ode flow_1 ((= d/dt[v] (* k t)) (= d/dt[t] 1) (= d/dt[k] 0)))

(assert (<= time_0 5))
(assert (<= 0 time_0))

(assert (<= time_1 5))
(assert (<= 0 time_1))

(assert (<= time_2 5))
(assert (<= 0 time_2))

(assert (<= time_3 5))
(assert (<= 0 time_3))

(assert (<= time_3 5))
(assert (<= 0 time_3))

(assert 
	(and
		(= [v_1 t_1 k_1] (integral 0. time_0 [v_0 t_0 k_0] flow_1))
		(= [v_2 t_2 k_2] (integral 0. time_1 [v_1 t_1 k_1] flow_1))
		(= [v_3 t_3 k_3] (integral 0. time_0 [v_2 t_2 k_2] flow_1))
		(= [v_4 t_4 k_4] (integral 0. time_1 [v_3 t_3 k_3] flow_1))
		(= [v_5 t_5 k_5] (integral 0. time_0 [v_4 t_4 k_4] flow_1))
		
		(= t_0 0)
		(>= v_0 -0.00001)
		(<= v_0 0.00001)

		(= t_1 1)
		(>= v_1 0.99)
		(<= v_1 1.01)

		(= t_2 2)
		(>= v_2 3.99)
		(<= v_2 4.01)

		(= t_3 3)
		(>= v_3 8.99)
		(<= v_3 9.01)

		(= t_4 4)
		(>= v_4 15.99)
		(<= v_4 16.01)

		(= t_5 5)
		(>= v_5 24.99)
		(<= v_5 25.01)

		(= k_0 k_1)
		(= k_1 k_2)
		(= k_2 k_3)
		(= k_3 k_4)
		(= k_4 k_5)

	))
(check-sat)
(exit)
