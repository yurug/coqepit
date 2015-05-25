* Formalization of the notion of *static equivalence* in Coq. This notion is central
  for verification of cryptographic protocols.
  Static equivalence is defined for term algebras equipped with equational theories.
  Two (not necessary finite) lists of terms are said to be *static equivalent* if there
  is no equality relation using elements of lists that holds for one list but that does
  not holds for the other one (modulo the equational theory).
  e.g. L1 = [k; k xor n xor m; n xor m] and L2 = [k; n xor k ; n] are static equivalent
  but L1 and L3 = [k; k xor n xor m; n] are not.
* Prove some easy equivalences.
* Write some tactics helping to prove static equivalences.
