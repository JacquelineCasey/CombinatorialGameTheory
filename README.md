
# Formalizing Combinatorial Game Theory in Coq

This is a project that I made for CMSC 22400 Programming Proofs.

The goal of this project is twofold. First, I define the fundamental constructs 
of Combinatorial Game Theory, and I prove many of the basic facts about those
constructs. Then, after I've gathered enough tools in the first part, I use these
facts to analyze an actual game - I've chosen Nim for analysis, because analysis
is relatively simple (we don't need to venture into another field, like graph theory),
complete (I can and do give an algorithm to decide who wins a given Nim position),
interesting (while it is simple, it is not trivial, and the facts in part 1 are
very much necessary), and important (the analysis of Nim can be generalized to get
an analysis for all impartial games).

Caveats: 
- I was able to do all proofs except one - Finishing the analysis of Nim 
requires a proof about a certain bitwise operation that I felt was out of scope
for the project. I do give an informal proof in place of the formal one.
- The code requires a library (Equations) to compile.
- I use some other people's code, but only in a few places that are marked throughout
the file. I did this only to solve problems that were orthogonal to the main goals
of the project, like some basic logic proofs from Logical Foundations, and some 
code I've adapted that uses the Equations library.
