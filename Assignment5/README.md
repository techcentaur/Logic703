### Assignment 5: Terms, substitution, unification, resolution

Consider the representation of "pre-terms" using the following data type definition

**type term = V of variable | Node of symbol * (term list);;**

Choose suitable type representations for types variable and symbol.


- Given a signature consisting of symbols and their arities (>= 0) in any suitable form -- either as a list of (symbol, arity) pairs, or as a function from symbols to arities, write a function check_sig that checks whether the signature is a valid signature (no repeated symbols, arities are non-negative etc.)
- Given a valid signature (checked using check_sig), define a function wfterm that checks that a given preterm is well-formed according to the signature.
- Define functions ht, size and vars that given a well-formed term, return its height, its size and the set of variables appearing in it respectively.  Use map, foldl and other such functions as far as possible wherever you use lists.  
- Define a suitable representation for substitutions.  Come up with an efficient representation of composition of substitutions. 
- Define the function subst that given a term t and a substitution s, applies the (Unique Homomorphic Extension of) s to t.  Ensure that subst is efficiently implemented. 
- Define the function mgu that given two terms t1 and t2, returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.


#### RESOLUTION:

1. Now, treating an atomic proposition as a pseudo-term (where the root symbol is a predicate symbol rather than a function symbol), represent sets of clauses, where each clause is a set of literals, where a literal is an atomic proposition or the negation of an atomic proposition.  [You need to choose an efficient representation of sets, ensuring that there are no duplicates, and you can easily identify empty sets, and where you have efficient implementations of selection and removal of an element from a set, and union of sets]
2. Implement an efficient way to select two clauses where one has a positive literal and the other a negative literal, such that the positive forms can be unified. 
3. Implement the one-step resolution of two given clauses, given the literal which can be unified. 
4. Implement a general resolution semi-algorithm, given a set of clauses.  
5. Show 4 examples of sets of Horn clauses with a single goal clause, for which your algorithm terminates. 
6. Does your algorithm always terminate if there is a sequence of unifications leading to a resolvent clause that is the empty clause, even if the clauses are not Horn? 
