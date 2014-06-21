Evaluation-of-Lambda-Calculus-in-Haskell
========================================



The List of Functions that can be used in the program:

---------------------------------
 in de Bruijn Indices Evaluation
---------------------------------
1. evaluateDB ---> it takes a DB Expression and evaluate
2. lift ---------> lifting operation
3. Subs ---------> substitution in de Bruijn
4. reduction ----> reduction in de Bruijn

-----------------------------
 in Krivine Abstract Machine
-----------------------------
1.compile ---> it takes a DB Expression and transform into KAM Instructions
2.initial ---> it takes a KAM Instructions and transform into an initial state
	             for evaluation in KAM
3.interp ----> it takes a state and output a state
4.evaluate --> a function that takes a compiled de Bruijn Expression, initialize,
		           evaluate,and output the final state.

		           
---------------------		           
 Testing the program
---------------------

To show program correctness in 2 different evaluation namely as :

      (a.)	Evaluation in de Bruijn Indices
      (b.)	Evaluation using Krivine Abstract Machine

We need a standard input for the two evaluations. The standard inputs are:
      (a.1) ((/./.(0 1)) (/.0))
      
A full syntax in Lambda Calculus in de Bruijn Indices
      (a.2) ((/.((/.(0 1)) (/.0))) (/.0))

A full syntax in Lambda Calculus in de Bruijn Indices

When evaluated it must give us the following:
		(a.1) /.(0 (/.0))
			In de Bruijn
		(a.2) /.0
			In de Bruijn
