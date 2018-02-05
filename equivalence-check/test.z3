(set-option :fixedpoint.engine "duality")
(declare-rel Goal ()) 

(rule (=>  Goal))
 (query Goal :print-certificate true)