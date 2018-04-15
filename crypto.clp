(defmodule MAIN (export ?ALL))
	
(deffacts input
		(digits 0 1 2 3 4 5 6 7 8 9))

;**************TEMPLATES*********************
(deftemplate possible
	(multislot letters (type SYMBOL))
	(multislot digits (type INTEGER))
)
(deftemplate assign
	(slot letter (type SYMBOL))
	(slot digit (type INTEGER))
)

(deftemplate add
	(multislot op1)
	(multislot op2)
	(multislot result))
;*********************************************

(defrule setup
	=>
	(focus SETUP))
	
(defrule first-look
	=>
	(focus FIRSTLOOK)
	(assert (done first-look))
)

	
(defrule calculate
	(add
		(op1 $? ?x)
		(op2 $? ?y)
		(result $? ?z)
	)
	?f <- (done first-look)
	=>
	(retract ?f)
	(assert (process ?x ?y ?z))
)

(defrule enumerate
	(process $? ?a $?)
	(digits $? ?d $?)
	(assign(letter ?l)(digit ?n))
	=>
	(if (eq ?a ?l)
		then (assert (enum ?l ?n))
		else (assert (enum ?a ?d))
	)
)

(defrule solving
	(process ?op1 ?op2 ?result)
	(enum ?op1 ?d1)
	(enum ?op2 ?d2)
	(enum ?result ?d3)

	(test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))

	(test (or (and (eq ?op1 ?result) (eq ?d1 ?d3)) (and (neq ?op1 ?result) (neq ?d1 ?d3))))

	(test (or (and (eq ?op2 ?result) (eq ?d2 ?d3)) (and (neq ?op2 ?result) (neq ?d2 ?d3))))

	(test (eq (mod (+ ?d1 ?d2) 10) ?d3))
	=>
	(assert
		(possible 
			(letters ?op1 ?op2 ?result)
			(digits ?d1 ?d2 ?d3)
		)
	)
)

;**********************************************************************************************************


(defmodule SETUP (import MAIN ?ALL))
(defrule input
	=>
	(printout t "op1: ")
	(bind ?op1 (readline))
	(printout t "op2: ")
	(bind ?op2 (readline))
	(printout t "result: ")
	(bind ?result (readline))
	(assert (add 
		(op1 (explode$ ?op1))
		(op2 (explode$ ?op2))
		(result (explode$ ?result)))))

;**********************************************************************************************************

(defmodule FIRSTLOOK (import MAIN ?ALL))
(defrule count-digits
	(add(op1 $?op1)(op2 $?op2)(result ?z $?rest))
	(test (or (>(+ (length ?z)(length $?rest))(length $?op1)) (>(+ (length ?z)(length $?rest))(length ?op2))))
	=>
	(assert(assign (letter ?z)(digit 1)))
)

(defrule remove-digit
	(assign(letter ?l)(digit ?d2))
	?f <- (digits $?before ?d1 $?after)
	(test (eq ?d1 ?d2))
	=>
	(retract ?f)
	(assert (digits $?before $?after))
)
;**********************************************************************************************************




