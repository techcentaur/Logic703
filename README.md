# Logic703
This repository is in correspondence with the assignments of course COL703 (Logic for Computer Science) taught by Prof Sajeeva Prasad during fall of 2019.


### Assignments:

- 0. Syntax and Semantics of Propositional Logic
- 1. Analytic Tableaux
- 2. Hilbert Style Proof System
- 3. Natural Deduction Proof System
- 4. Normalisation in Natural deduction proofs
- 5. Terms, substitution, unification, resolution


### What did the assignment's demo went?

- 0. I did a coding mistake in nnf where I put Iff(a, b) as And(Impl(a, b), Impl(a, b)) when it is obviously And(Impl(a, b), Impl(b, a)). Rest worked correctly, and so does the examples.
- 1. Everything correct, with examples.
- 2. Everything correct, with examples.
- 3. Everything correct, with examples.
- 4. There was one mistake in the `End` matching in grafting where I didn't change the gamma, but corrected it now | Complete with all examples.
- 5. One mistake: When normalizing, you have to normalize the tree until there is nothing to be normalized; I did it just once. But corrected in the updated code | Complete with all examples.