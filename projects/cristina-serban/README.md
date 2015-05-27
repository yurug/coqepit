I have recently come across the paper ["Automating Proofs of Data-Structure Properties in Imperative Programs"](http://arxiv.org/pdf/1407.6124v1.pdf). It would be very interesting for me to see how the proof in Figure 11, page 8, could be mechanized in Coq.

The properties of the data structures are formalized using separation logic and involve recursive predicates. The proof I selected is about list segments and involves two predicates: one that unfolds the list segment from the left end to the right end and one that unfolds it from the right end to the left end. The goal is to prove that these predicates describe the same data structure, i.e. ls^(x, y, L) is the same as ls(x, y, L), where their definitions are given on page 5.

Their method builds on the unfold-and-match and cyclic proof techniques. The general proof rules are described in Figure 6, page 6.

Some ideas about what should be done:

* Writing separation logic in Coq. This is a bit different from what we were shown by Arthur Charguéraud, since it does not involve code (and, thus, we are not working with triples). I would just like to know how to describe properties of data structures and how to define inductive (recursive) predicates for this purpose.

* I am guessing that the proof rules can be implemented as lemmas and maybe some kind of new tactics, specifically tailored for them, are needed. One of the more difficult points is that IA-1 and IA-2 need to keep track of the generation of atoms (they need to be able to tell whether an atom is newer that another one or not).

* An interesting aspect of their method is the use of proof obligations, which contain the goals and a set of entailments whose truth can be assumed inductively. The proof rules work not only with the goals, but also with these sets of entailments. LU+I even modifies the set.
