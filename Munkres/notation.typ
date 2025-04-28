#import "preamble.typ": *
#show: preamble

=== Notation
This document uses the following conventions:
- $A eq.delta B$ denotes that $B$ is the definition of $A$.
- $A subset B$ denotes that $A$ is a _proper_ subset of $B$. Similarly, $A supset B$ denotes that A is a proper superset of $B$.
- The power set of $A$ is denoted $cal(P)(A)$.
- $0 in NN  = omega$.
- $chi_A$ denotes the indicator function equal to 1 on $A$ and zero on $A^complement$.
- $id$ denotes the identity function and may be subscripted with its domain.
- Let $(X, tau)$ be a topological space, let $A subset.eq X$, and let $x in X$.
  - The closure of $A$ is denoted $A$ or $"Cl"(A)$.
  - The interior is denoted by $A degree$ or $"Int"(A)$.
  - The set of limit points is denoted $A'$ or $"Lim"(A)$.
  - The boundary of $A$ is denoted $partial A$ and is defined as $overline(X) without X degree$.
  - A neighbourhood of $x$ is some $U in cal(P)(X)$ such that there is some $V in cal(P)(U) inter tau$ such that $x in V$.
  - The neighbourhood system about $x$, the set of neighbourhoods of $x$, is denoted $cal(N)(x)$,
  - The open neighbourhood system about $x$, the set of open neighbourhoods of $x$, is denoted $cal(N)circ (x)$.
  - A punctured neighbourhood of $x$ is some $U without {x}$, where $U in cal(N)(x)$, and the punctured neighbourhood system is denoted $cal(N)^*(x)$.
  - The system of punctured open neighbourhoods is denoted $cal(N)^ast.circle (x)$.
  - $"Cl"$, $"Int"$, $"Lim"$, $partial$, and $cal(N)$ maybe subscripted with either $X$ or $tau$ for clarity.
- Let ${(X_lambda, tau_lambda)}_(lambda in Lambda)$ be a collection of topological spaces. Their product with the product topology is denoted $product_(lambda in Lambda) X_lambda$, while that with the box topology is denoted $square.big_(lambda in Lambda) X_lambda$.
- Let $(X, d)$ be a metric space with topology $tau$, let $x in X$, and let $epsilon > 0$.
  - The open ball centred at $x$ with radius $epsilon$ is #h(1fr)
    $ B(x, epsilon) eq.delta {y in X | d(x, y) < epsilon} $
  - Its closed counterpart is
    $ overline(B)(x, epsilon) eq.delta {y in X | d(x, y) <= epsilon} $
  - The punctured open ball is given by
    $ B^*(x, epsilon) eq.delta {y in X | d(x, y) in (0, epsilon)} $
  - $B$ may be subscripted by $X$, $d$, or $tau$ for clarity.
