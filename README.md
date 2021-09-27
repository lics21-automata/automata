# From Finite-Valued Nondeterministic Transducers to Deterministic Two-Tape Automata

## Directory Structure:

`html/` contains the formalization of the paper in Isabelle exported to html (open `html/index.html` in your favourite web browser).

`thys/` contains the formalization of the paper in Isabelle (open a theory source file in Isabelle/jEdit).

`LICS_2021.pdf` is the paper accepted LICS 2021.

## Formalization in Isabelle

The Isabelle sources are included in a separate directory called `thys`.
The theories can be studied by opening them in Isabelle/jEdit.
The latest version Isabelle2021 can be downloaded from

https://isabelle.in.tum.de/

and installed following the standard instructions from

https://isabelle.in.tum.de/installation.html

## Mapping Results in the Paper to the Formalization

The parts in the formalization corresponding to a particular definition, lemma, and theorem are labeled as comments, e.g., (* Theorem 15 *).

We model states and symbols from an input or output alphabet as values of a type. Every type is always non-empty in Isabelle so such a condition need not be formulated explicitly. The finiteness of an alphabet is formulated as finiteness of the respective type (e.g., the Boolean alphabet). The finiteness of a set of states is expressed by a finite closed subset of states from a potentially infinite type, e.g., the set of states can be a finite subset of the infinite set of natural numbers and closed under the transition relation.

The transition function of a two-tape deterministic automaton is partial and the automaton rejects an input-output pair if the computation gets stuck.
