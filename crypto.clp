(defmodule MAIN (export ?ALL))
(deffacts input
		(digits 0 1 2 3 4 5 6 7 8 9))
	
;************** TEMPLATES *********************
(deftemplate do
	(slot column))

(deftemplate done
	(slot column))

(deftemplate is-result-longer
	(slot boolean))

(deftemplate are-operands-same-length
	(slot boolean))

(deftemplate shorter-operand
	(slot operand (type INTEGER)))

(deftemplate max-length
	(slot length (type INTEGER)))

(deftemplate min-length
	(slot length (type INTEGER)))

(deftemplate possible
	(slot column (type INTEGER))
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

(deftemplate enum
	(slot letter (type SYMBOL))
	(slot digit (type INTEGER)))

(deftemplate combination
	(slot column)
	(multislot letters)
	(multislot numbers)) 
;************* PROGRAM FLOW ********************************

(defrule setup
	(declare (salience 100))
	=>
	(focus SETUP))
	
(defrule first-look
	(declare (salience 99))
	=>
	(assert (do (column 0)))
	(focus FIRST_LOOK))

(defrule select-column
	(declare (salience 97))
	(max-length (length ?max))
	(done (column ?column&:(< ?column ?max)))
	=>
	(focus SELECT_COLUMN))

(defrule process-column
	(declare (salience 96))
	(do (column ?column))
	=>
	(focus PROCESS_COLUMN))

(defrule permutate-possibilities
	(declare (salience 95))
	(do (column ?column))
	=>
	(assert(done (column ?column)))
	(focus PERMUTATE_POSSIBILITIES))

(defrule combine-permutations
	(declare (salience 94))
	(done (column ?column))
	(max-length (length ?max))

	(test(eq ?column ?max))
	=>
	(focus COMBINE_PERMUTATIONS))


; **********************************************************************************************************

(defmodule SETUP (import MAIN ?ALL))
(deffacts empty-combination
		(combination (letters nil) (numbers nil)))
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
	(assert (max-length (length (+ (length ?z)(length $?rest))))))

(defrule analyze-length
	(add(op1 $?op1)(op2 $?op2)(result ?z $?rest))
	(max-length (length ?max))
	?f <- (combination (letters $?front ?combination_letters $?back) (numbers $?front2 ?combination_digits $?back2))

	(test (eq ?combination_letters nil))
	=>
	(if (and (> ?max (length $?op1)) (> ?max (length ?op2)))
	then 
		(if(eq ?combination_letters nil)
		then
			(assert (combination (letters ?z) (numbers 1)))
			(retract ?f)
		) 
		(assert (is-result-longer (boolean true))) (assert(assign (letter ?z)(digit 1)))
	else 
		(assert (is-result-longer (boolean false)))
	)
	(if (> (length ?op1) (length ?op2))
	then
		(assert (shorter-operand (operand 2)))
		(assert (min-length (length (length ?op2))))
		(assert (are-operands-same-length (boolean false)))
	else
		(if (> (length ?op2) (length ?op1))
		then
			(assert (shorter-operand (operand 1)))
			(assert (min-length (length (length ?op1))))
			(assert (are-operands-same-length (boolean false)))
		else
			(assert (min-length (length (length ?op1))))
			(assert (are-operands-same-length (boolean true)))
		)	
	)
	(assert (done (column 0))))

(defrule check-last-column
	(add(op1 $? ?x)(op2 $? ?y)(result $? ?z))
	(test (or (eq ?x ?z) (eq ?y ?z)))
	=>
	(if (eq ?x ?z)
		then (assert (assign (letter ?y)(digit 0)))
		else (assert (assign (letter ?x)(digit 0)))
	)
	(assert (done (column 0))))

(defrule remove-digit
	(assign(letter ?l)(digit ?d2))
	?f <- (digits $?before ?d1 $?after)
	(test (eq ?d1 ?d2))
	=>
	(retract ?f)
	(assert (digits $?before $?after))
	(assert (done (column 0))))

;**********************************************************************************************************
(defmodule SELECT_COLUMN (import MAIN ?ALL))

(defrule select-column-result-longer
	(max-length (length ?max))
	(is-result-longer (boolean true))
	(done (column ?column&:(< ?column ?max)))
	?f1 <- (do (column ?column))
	?f2 <- (done (column ?column))
	=>
	(if (eq ?column 0)
	then 
		(assert (do (column 2)))
	else
		(assert (do (column (+ ?column 1))))
	)
	(retract ?f1)
	(retract ?f2))

(defrule select-column-result-not-longer
	(max-length (length ?max))
	(is-result-longer (boolean false))
	(done (column ?column&:(< ?column ?max)))
	?f1 <- (do (column ?column))
	?f2 <- (done (column ?column))
	=>
	(assert (do (column (+ ?column 1))))
	(retract ?f1)
	(retract ?f2))

;**********************************************************************************************************
(defmodule PROCESS_COLUMN (import MAIN ?ALL))

(defrule process-column-operands-diff-length-result-longer
	(do (column ?c))
	(shorter-operand (operand ?shortest))
	(is-result-longer (boolean true))
	(min-length (length ?min))
	(max-length (length ?max))
	(add
		(op1 $?x)
		(op2 $?y)
		(result $?z)
	)
	=>
	(if (<= (+ ?c ?min) ?max)
	then
		(if (eq ?shortest 1)
		then
			(assert (enumerate (column ?c) (letters (nth$ (- ?c 1) ?y) (nth$ ?c ?z))))
		else
			(assert (enumerate (column ?c) (letters (nth$ (- ?c 1) ?x) (nth$ ?c ?z))))
		)
	else
		(if (eq ?shortest 1)
		then
			(assert (enumerate (column ?c) (letters (nth$ (- ?c (- ?max ?min)) ?x)  (nth$ (- ?c 1) ?y) (nth$ ?c ?z))))
		else
			(assert (enumerate (column ?c) (letters (nth$ (- ?c 1) ?x)  (nth$ (- ?c (- ?max ?min)) ?y) (nth$ ?c ?z))))
		)
	) )

(defrule process-column-operands-diff-length-result-same
	(do (column ?c))
	(shorter-operand (operand ?shortest))
	(is-result-longer (boolean false))
	(min-length (length ?min))
	(max-length (length ?max))
	(add
		(op1 $?x)
		(op2 $?y)
		(result $?z)
	)
	=>
	(if (<= (+ ?c ?min) ?max)
	then
		(if (eq ?shortest 1)
		then
			(assert (enumerate (column ?c) (letters (nth$ ?c ?y) (nth$ ?c ?z))))
		else
			(assert (enumerate (column ?c) (letters (nth$ ?c ?x) (nth$ ?c ?z))))
		)
	else
		(if (eq ?shortest 1)
		then
			(assert (enumerate (column ?c) (letters (nth$ (- ?c (- ?max ?min)) ?x)  (nth$ ?c ?y) (nth$ ?c ?z))))
		else
			(assert (enumerate (column ?c) (letters (nth$ ?c ?x)  (nth$ (- ?c (- ?max ?min)) ?y) (nth$ ?c ?z))))
		)
	) )

(defrule process-column-all-same-length
	(do (column ?c))
	(is-result-longer (boolean false))
	(are-operands-same-length (boolean true))
	(add
		(op1 $?x)
		(op2 $?y)
		(result $?z)
	)
	=>
	(assert (enumerate (column ?c) (letters (nth$ ?c ?x)  (nth$ ?c ?y) (nth$ ?c ?z)))))

(defrule process-column-result-longer-operands-same-length
	(do (column ?c))
	(is-result-longer (boolean true))
	(are-operands-same-length (boolean true))
	(add
		(op1 $?x)
		(op2 $?y)
		(result $?z)
	)
	=>
	(assert (enumerate (column ?c) (letters (nth$ (- ?c 1) ?x)  (nth$ (- ?c 1) ?y) (nth$ ?c ?z)))))

(defrule enumerate-with-assignments
	(do (column ?c))
	(enumerate (column ?c) (letters $? ?a $?))
	(digits $? ?d $?)
	(assign(letter ?l)(digit ?n))
	=>
	(if (eq ?a ?l)
	then
		(assert (enum (letter ?l) (digit ?n)))

	else 
		(assert (enum (letter ?a) (digit ?d)))
	))

(defrule enumerate-without-assignments
	(do (column ?c))
	(enumerate (column ?) (letters $? ?a $?))
	(digits $? ?d $?)
	(is-result-longer (boolean false))
	=>
	else (assert (enum (letter ?a) (digit ?d))))

;**********************************************************************************************************
(defmodule PERMUTATE_POSSIBILITIES (import MAIN ?ALL))

(defrule permutate-no-carry-over-3-letters
	(do (column ?column))
	(enumerate (column ?column) (letters ?op1 ?op2 ?result))
	(max-length (length ?length))
	(is-result-longer (boolean ?result-longer))
	(enum (letter ?op1) (digit ?d1))
	(enum (letter ?op2) (digit ?d2))
	(enum (letter ?result) (digit ?d3))

	(test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))

	(test (or (and (eq ?op1 ?result) (eq ?d1 ?d3)) (and (neq ?op1 ?result) (neq ?d1 ?d3))))

	(test (or (and (eq ?op2 ?result) (eq ?d2 ?d3)) (and (neq ?op2 ?result) (neq ?d2 ?d3))))

	(test (eq (mod (+ ?d1 ?d2) 10) ?d3))
	=>
	(if (or(and (eq ?column 1) (< (+ ?d1 ?d2) 10))(and(and(eq ?column 2)(eq ?result-longer true)) (>= (+ ?d1 ?d2) 10)))
	then
		(assert(possible (column ?column)(letters ?op1 ?op2 ?result)(digits ?d1 ?d2 ?d3)(carryover false)))
	else
		(if (or(and(> ?column 1)(eq ?result-longer false))(and(> ?column 2)(eq ?result-longer true)))
		then
			(assert(possible (column ?column)(letters ?op1 ?op2 ?result)(digits ?d1 ?d2 ?d3)(carryover false)))
		)
	))	

(defrule permutate-carry-over-3-letters
	(do (column ?column))
	(max-length (length ?length))
	(is-result-longer (boolean ?result-longer))
	(enumerate (column ?column) (letters ?op1 ?op2 ?result))
	(enum (letter ?op1) (digit ?d1))
	(enum (letter ?op2) (digit ?d2))
	(enum (letter ?result) (digit ?d3))

	(test (or (and (eq ?op1 ?op2) (eq ?d1 ?d2)) (and (neq ?op1 ?op2) (neq ?d1 ?d2))))

	(test (or (and (eq ?op1 ?result) (eq ?d1 ?d3)) (and (neq ?op1 ?result) (neq ?d1 ?d3))))

	(test (or (and (eq ?op2 ?result) (eq ?d2 ?d3)) (and (neq ?op2 ?result) (neq ?d2 ?d3))))

	(test (eq (mod (+ ?d1 ?d2) 10) (- ?d3 1)))

	(test (< ?column ?length))
	=>
	(if (or(and (eq ?column 1) (< (+ ?d1 ?d2) 9))(and(and(eq ?column 2)(eq ?result-longer true)) (>= (+ ?d1 ?d2) 10)))
	then
		(assert(possible (column ?column)(letters ?op1 ?op2 ?result)(digits ?d1 ?d2 ?d3)(carryover true)))
	else
		(if (or(and(> ?column 1)(eq ?result-longer false))(and(> ?column 2)(eq ?result-longer true)))
		then
			(assert(possible (column ?column)(letters ?op1 ?op2 ?result)(digits ?d1 ?d2 ?d3)(carryover true)))
		)
	))

(defrule permutate-2-letters-same
	(do (column ?column))
	(enumerate (column ?column) (letters ?op ?result))
	(enum (letter ?op) (digit ?d1))
	(enum (letter ?result) (digit ?d3))

	(test (and (eq ?op ?result) (eq ?d1 ?d3)))

	=>

	(assert(possible (column ?column)(letters ?op ?result)(digits ?d1 ?d3)(carryover false))))

(defrule permutate-2-letters-diff
	(do (column ?column))
	(enumerate (column ?column) (letters ?op ?result))
	(enum (letter ?op) (digit ?d1))
	(enum (letter ?result) (digit ?d3))

	(test (and(and (neq ?op ?result) (neq ?d1 ?d3))(eq(- ?d3 ?d1)1)))

	=>
	(assert(possible (column ?column)(letters ?op ?result)(digits ?d1 ?d3)(carryover true))))

;**********************************************************************************************************
(defmodule COMBINE_PERMUTATIONS (import MAIN ?ALL))

(defrule merge-possibilities-3-letters
	(possible (column ?column1)(letters ?l1 ?l2 ?l3) (digits ?d1 ?d2 ?d3) (carryover ?carryover1))
	(possible (column ?column2&~?column1)(letters ?l4 ?l5 ?l6) (digits ?d4 ?d5 ?d6) (carryover ?carryover2))

	(test (eq ?column2 (+ ?column1 1)))

	(test (or(and(eq ?carryover1 true)(>=(+ ?d4 ?d5)10))(and(eq ?carryover1 false)(<(+ ?d4 ?d5)10))))

	(test(or(or(or(or(or(or(or(or(or

	(and(and(and(and(eq ?l1 ?l4)(eq ?d1 ?d4))
	(or(and(eq ?l2 ?l5)(eq ?d2 ?d5))(and(neq ?l2 ?l5)(neq ?d2 ?d5))))
	(or(and(eq ?l3 ?l6)(eq ?d3 ?d6))(and(neq ?l3 ?l6)(neq ?d3 ?d6))))
	(and(and(and(eq ?l1 ?l4)(eq ?d1 ?d4))
	(or(and(eq ?l2 ?l6)(eq ?d2 ?d6))(and(neq ?l2 ?l6)(neq ?d2 ?d6))))
	(or(and(eq ?l3 ?l4)(eq ?d3 ?d4))(and(neq ?l3 ?l4)(neq ?d3 ?d4)))))
	
	(and(and(and(and(eq ?l1 ?l5)(eq ?d1 ?d5))
	(or(and(eq ?l2 ?l4)(eq ?d2 ?d4))(and(neq ?l2 ?l4)(neq ?d2 ?d4))))
	(or(and(eq ?l3 ?l6)(eq ?d3 ?d6))(and(neq ?l3 ?l6)(neq ?d3 ?d6))))
	(and(and(and(eq ?l1 ?l5)(eq ?d1 ?d5))
	(or(and(eq ?l2 ?l6)(eq ?d2 ?d6))(and(neq ?l2 ?l6)(neq ?d2 ?d6))))
	(or(and(eq ?l3 ?l4)(eq ?d3 ?d4))(and(neq ?l3 ?l4)(neq ?d3 ?d4))))))

	(and(and(and(and(eq ?l1 ?l6)(eq ?d1 ?d6))
	(or(and(eq ?l2 ?l4)(eq ?d2 ?d4))(and(neq ?l2 ?l4)(neq ?d2 ?d4))))
	(or(and(eq ?l3 ?l5)(eq ?d3 ?d5))(and(neq ?l3 ?l5)(neq ?d3 ?d5))))
	(and(and(and(eq ?l1 ?l6)(eq ?d1 ?d6))
	(or(and(eq ?l2 ?l5)(eq ?d2 ?d5))(and(neq ?l2 ?l5)(neq ?d2 ?d5))))
	(or(and(eq ?l3 ?l4)(eq ?d3 ?d4))(and(neq ?l3 ?l4)(neq ?d3 ?d4))))))

	(and(and(and(and(eq ?l2 ?l4)(eq ?d2 ?d4))
	(or(and(eq ?l1 ?l5)(eq ?d1 ?d5))(and(neq ?l1 ?l5)(neq ?d1 ?d5))))
	(or(and(eq ?l3 ?l6)(eq ?d3 ?d6))(and(neq ?l3 ?l6)(neq ?d3 ?d6))))
	(and(and(and(eq ?l2 ?l4)(eq ?d2 ?d4))
	(or(and(eq ?l1 ?l6)(eq ?d1 ?d6))(and(neq ?l1 ?l6)(neq ?d1 ?d6))))
	(or(and(eq ?l3 ?l5)(eq ?d3 ?d5))(and(neq ?l3 ?l5)(neq ?d3 ?d5))))))

	(and(and(and(and(eq ?l2 ?l5)(eq ?d2 ?d5))
	(or(and(eq ?l1 ?l4)(eq ?d1 ?d4))(and(neq ?l1 ?l4)(neq ?d1 ?d4))))
	(or(and(eq ?l3 ?l6)(eq ?d3 ?d6))(and(neq ?l3 ?l6)(neq ?d3 ?d6))))
	(and(and(and(eq ?l2 ?l5)(eq ?d2 ?d5))
	(or(and(eq ?l1 ?l6)(eq ?d1 ?d6))(and(neq ?l1 ?l6)(neq ?d1 ?d6))))
	(or(and(eq ?l3 ?l4)(eq ?d3 ?d4))(and(neq ?l3 ?l4)(neq ?d3 ?d4))))))

	(and(and(and(and(eq ?l2 ?l6)(eq ?d2 ?d6))
	(or(and(eq ?l1 ?l4)(eq ?d1 ?d4))(and(neq ?l1 ?l4)(neq ?d1 ?d4))))
	(or(and(eq ?l3 ?l5)(eq ?d3 ?d5))(and(neq ?l3 ?l5)(neq ?d3 ?d5))))
	(and(and(and(eq ?l2 ?l6)(eq ?d2 ?d6))
	(or(and(eq ?l1 ?l5)(eq ?d1 ?d5))(and(neq ?l1 ?l5)(neq ?d1 ?d5))))
	(or(and(eq ?l3 ?l4)(eq ?d3 ?d4))(and(neq ?l3 ?l4)(neq ?d3 ?d4))))))

	(and(and(and(and(eq ?l3 ?l4)(eq ?d3 ?d4))
	(or(and(eq ?l2 ?l5)(eq ?d2 ?d5))(and(neq ?l2 ?l5)(neq ?d2 ?d5))))
	(or(and(eq ?l1 ?l6)(eq ?d1 ?d6))(and(neq ?l1 ?l6)(neq ?d1 ?d6))))
	(and(and(and(eq ?l3 ?l4)(eq ?d3 ?d4))
	(or(and(eq ?l2 ?l6)(eq ?d2 ?d6))(and(neq ?l2 ?l6)(neq ?d2 ?d6))))
	(or(and(eq ?l1 ?l5)(eq ?d1 ?d5))(and(neq ?l1 ?l5)(neq ?d1 ?d5))))))

	(and(and(and(and(eq ?l3 ?l4)(eq ?d3 ?d4))
	(or(and(eq ?l1 ?l5)(eq ?d1 ?d5))(and(neq ?l1 ?l5)(neq ?d1 ?d5))))
	(or(and(eq ?l2 ?l6)(eq ?d2 ?d6))(and(neq ?l2 ?l6)(neq ?d2 ?d6))))
	(and(and(and(eq ?l3 ?l4)(eq ?d3 ?d4))
	(or(and(eq ?l1 ?l6)(eq ?d1 ?d6))(and(neq ?l1 ?l6)(neq ?d1 ?d6))))
	(or(and(eq ?l2 ?l5)(eq ?d2 ?d5))(and(neq ?l2 ?l5)(neq ?d2 ?d5))))))

	(and(and(and(and(eq ?l3 ?l5)(eq ?d3 ?d5))
	(or(and(eq ?l1 ?l4)(eq ?d1 ?d4))(and(neq ?l1 ?l4)(neq ?d1 ?d4))))
	(or(and(eq ?l2 ?l6)(eq ?d2 ?d6))(and(neq ?l2 ?l6)(neq ?d2 ?d6))))
	(and(and(and(eq ?l3 ?l5)(eq ?d3 ?d5))
	(or(and(eq ?l1 ?l6)(eq ?d1 ?d6))(and(neq ?l1 ?l6)(neq ?d1 ?d6))))
	(or(and(eq ?l2 ?l4)(eq ?d2 ?d4))(and(neq ?l2 ?l4)(neq ?d2 ?d4))))))


	(and(and(and(and(and(and(and(and

	(and(neq ?l1 ?l4)(neq ?d1 ?d4))

	(and(neq ?l1 ?l5)(neq ?d1 ?d5)))

	(and(neq ?l1 ?l6)(neq ?d1 ?d6)))

	(and(neq ?l2 ?l4)(neq ?d2 ?d4)))

	(and(neq ?l2 ?l5)(neq ?d2 ?d5)))

	(and(neq ?l2 ?l6)(neq ?d2 ?d6)))

	(and(neq ?l3 ?l4)(neq ?d3 ?d4)))

	(and(neq ?l3 ?l5)(neq ?d3 ?d5)))

	(and(neq ?l3 ?l6)(neq ?d3 ?d6)))))


	=>
	(assert (combination (column ?column2) (letters ?l1 ?l2 ?l3 ?l4 ?l5 ?l6) (numbers ?d1 ?d2 ?d3 ?d4 ?d5 ?d6)))
)

(defrule merge-combinations-3-letters
	(combination (column ?column1)(letters $?l1 ?l2 ?l3 ?l4) (numbers $?n1 ?n2 ?n3 ?n4))
	(combination (column ?column2&:(eq ?column2 (+ ?column1 1)))(letters ?l2 ?l3 ?l4 $?l5) (numbers  ?n2 ?n3 ?n4 $?n5))


	=>
	(assert (combination (column (+ ?column2 1)) (letters $?l1 ?l2 ?l3 ?l4 $?l5)(numbers $?n1 ?n2 ?n3 ?n4 $?n5)))
)


