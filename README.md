# Group Identification

 - Luís Xu, 99100, luisxu@tecnico.ulisboa.pt
 - Gonçalo Carvalho , 99227, goncalo.pires.carvalho@tecnico.ulisboa.pt
 - Sebastião Carvalho, 99326, sebastiaovscarvalho@tecnico.ulisboa.pt

# Implemented Features
Made the necessary changes to the Imp file, extending the commands, adding the new notations and adding the examples.

Implemented the step-indexer evaluator and proved p1_equals_p2 and ceval_step_more.

Defined ceval, proving it with examples, and also proving equivalence with two examples and also idempotence,
commutativity, associativity, distributivity on the left and congruence for non determinism.

Finally, extended the parser and created 3 new examples.

# Extras
Improved the step-indexed evaluator so that: i) when it fails, instead of just returning OutOfGas or
Fail, it returns an appropriate error message; ii) when it succeeds, it shows the resulting state and
continutation, but also the number of “steps” taken.
