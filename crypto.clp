(defmodule MAIN (export ?ALL))
	
(deffacts input
		(digits 0 1 2 3 4 5 6 7 8 9))

;**************TEMPLATES*********************
(deftemplate do
	(slot column))

(deftemplate done
	(slot column))

(deftemplate is-result-longer
	(slot boolean))

(deftemplate max-length
	(slot length (type INTEGER)))

(deftemplate possible
	(multislot letters (type SYMBOL))
	(multislot digits (type INTEGER))
	(slot carryover))

(deftemplate assign
	(slot letter (type SYMBOL))
	(slot digit (type INTEGER)))

(deftemplate add
	(multislot op1)
	(multislot op2)
	(multislot result))

(deftemplate enumerate
	(slot column (type INTEGER))
	(multislot letters))
;*********************************************

(defrule setup
	=>
	(focus SETUP))
	
(defrule first-look
	=>
	(assert (do (column 0)))
	(focus FIRST_LOOK)
	(assert (done (column 0)))
)

(defrule select-column
	(max-length (length ?length))
	(is-result-longer (boolean false))
	(done (column ?column&:(< ?column ?length)))
	?f <- (do (column ?column))
	=>
	(retract ?f)
	(focus SELECT_COLUMN)
)

(defrule select-column-result-longer
	(max-length (length ?length))
	(is-result-longer (boolean true))
	(done (column ?column&:(< (* ?column -1) (- ?length 1))))
	?f <- (do (column ?column))
	=>
	(retract ?f)
	(focus SELECT_COLUMN)
)


;***************************************************
; PROCESS COLUMN ....can't seem to use defmodule
;***************************************************
(defrule process-column-result-longer
	(do (column ?c))
	(is-result-longer (boolean true))
	(add
		(op1 $?x)
		(op2 $?y)
		(result $?z)
	)
	=>
	(assert (enumerate (column ?c) (letters (nth$ (* ?c -1) ?x)  (nth$ (* ?c -1) ?y) (nth$ (+ (* ?c -1) 1) ?z))))
)

(defrule process-column
	(do (column ?c))
	(is-result-longer (boolean false))
	(add
		(op1 $?x)
		(op2 $?y)
		(result $?z)
	)
	=>
	(assert (enumerate (column ?c) (letters (nth$ ?c ?x)  (nth$ ?c ?y) (nth$ ?c ?z))))
)


(defrule enumerate-with-assignments
	(enumerate (column ?) (letters $? ?a $?))
	(digits $? ?d $?)
	(assign(letter ?l)(digit ?n))
	=>
	(if (eq ?a ?l)
		then (assert (enum ?l ?n))
		else (assert (enum ?a ?d))
	)
)

(defrule enumerate-without-assignments
	(enumerate (column ?) (letters $? ?a $?))
	(digits $? ?d $?)
	(is-result-longer (boolean false))
	=>
	else (assert (enum ?a ?d))	
)

;***************************************************

(defrule solve-column
	(do (column ?column))
	=>
	(focus SOLVE_COLUMN))

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

(defmodule FIRST_LOOK (import MAIN ?ALL))


(defrule find-max-length
	(add(op1 $?op1)(op2 $?op2)(result ?z $?rest))
	=>
	(assert (max-length (length (+ (length ?z)(length $?rest)))))
)

(defrule assign-left-most-letter-of-result
	(add(op1 $?op1)(op2 $?op2)(result ?z $?rest))
	(max-length (length ?max))
	=>
	(if (or (> ?max (length $?op1)) (> ?max (length ?op2)))
		then (assert (is-result-longer (boolean true))) (assert(assign (letter ?z)(digit 1)))
		else (assert (is-result-longer (boolean false))))
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

(defmodule SELECT_COLUMN (import MAIN ?ALL))

(defrule determine-next-column
	?f <- (done (column ?column))
	(is-result-longer (boolean ?boolean))
	=>
	(if (eq ?boolean true)
		then (assert (do (column (- ?column 1))))
		else (assert (do (column (+ ?column 1))))
	)
	(retract ?f)
)

;**********************************************************************************************************
(defmodule SOLVE_COLUMN (import MAIN ?ALL))

(defrule solving
	(do (column ?column))
	(enumerate (column ?column) (letters ?op1 ?op2 ?result))
	(enum ?op1 ?d1)
	(enum ?op2 ?d2)
	(enum ?result ?d3)

	(test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))

	(test (or (and (eq ?op1 ?result) (eq ?d1 ?d3)) (and (neq ?op1 ?result) (neq ?d1 ?d3))))

	(test (or (and (eq ?op2 ?result) (eq ?d2 ?d3)) (and (neq ?op2 ?result) (neq ?d2 ?d3))))

	(test (eq (mod (+ ?d1 ?d2) 10) ?d3))
	=>
	(if
		(or(eq ?column -1) (eq ?column 1))
		then(
			if (or (and (eq ?column -1) (>= (+ ?d1 ?d2) 10))(and (eq ?column 1) (< (+ ?d1 ?d2) 10)))
			then (assert(possible (letters ?op1 ?op2 ?result)(digits ?d1 ?d2 ?d3)(carryover false)))
		)
		else(assert(possible (letters ?op1 ?op2 ?result)(digits ?d1 ?d2 ?d3)(carryover false)))
	)

	(assert (done (column ?column)))
)
