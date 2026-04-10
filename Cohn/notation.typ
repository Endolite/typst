#import "preamble.typ": *
#show: preamble
== Notation

This document uses the following conventions:
-
  $ev(italic("lhs")) eq.delta ev(italic("rhs"))$ denotes that $ev(italic("rhs"))$ is the _definition_ of $ev(italic("lhs"))$.
-
  $ev(italic("lhs")) equiv ev(italic("rhs"))$ denotes that $ev(italic("lhs"))$ is _set-theoretically equivalent_ to $ev(italic("rhs"))$.
-
  $A subset B$ denotes that $A$ is a _proper_ subset of $B$, while $A subset.eq B$ denotes that $A$ is an _improper_ subset.
-
  The power set of $A$ is denoted $cal(P)(A)$
-
  $0 in NN equiv omega$
-
  For $n in NN$, $[|n|]$ denotes the von Neumann ordinal $n in omega$; that is, $[|n|] eq.delta {i}_(i = 0)^(n - 1)$.
-
  $chi_A$ denotes the indicator function equal to 1 on $A$ and zero on $A^complement$.
-
  $id$ denotes the identity function and may be subscripted with its domain.
-
  The restriction of a function $f$ to some subset $A$ of its domain is denoted $f|_A$.
-
  The following notation is used for common measures:
  - $\#$ is the counting measure.
  - $lambda^n$ is the Lebesgue measure on $RR^n$.
  - $delta_x$ is the point mass.
-
  The collection of Borel subsets of a topological space $(X, tau)$ is denoted $scr(B)(X)$ or $scr(B)(tau)$.
