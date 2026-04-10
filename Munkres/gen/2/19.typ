#import "../../preamble.typ" : *
#show: preamble

=== Section 19 -- The Product Topology
  1.
    Let #label("19.1") ${(X_lambda, tau_lambda)_(lambda in Lambda)}$ be a family of toplogical spaces, with $tau_lambda$ having basis $cal(B)_lambda$. Prove that
      $ cal(B) = {product_(lambda in Lambda) B_lambda mid(|) B_lambda in cal(B)_lambda} $
      is a basis for the box topology $tau_square$, while
      $ cal(C) = {product_(lambda in Lambda) B_lambda mid(|) B_lambda in cal(B)_lambda union {X_lambda}, abs({lambda in Lambda mid(|) B_lambda != X_lambda}) < aleph_0} $
      is one for the product topology $tau_Pi$.
    #sol[
      For $x in square.big_(lambda in Lambda) X_lambda$, for each $lambda in Lambda$ there is some $B_lambda in cal(B)_lambda$ such that $pi_lambda (x) = B_lambda$, so $x in product_(lambda in Lambda) B_lambda in cal(B)$. IF $x in B_1 inter B_2$, where $B_1, B_2 in cal(B)$, then for each $lambda in Lambda$, there is some $B_lambda$ such that
        $
          pi_lambda (x) in B_lambda
            in cal(B)_lambda inter cal(P)bp(pi_lambda (B_1) inter pi_lambda (B_2)))
        $
        so
        $
          x in product_(lambda in Lambda) B_lambda
            in cal(B) inter cal(P)(B_1 inter B_2)
        $
        making $cal(B)$ a basis for $tau_square$.

      $product_(lambda in Lambda) X_lambda in cal(C)$, meaning that each $x in X$ is trivially in some $C in cal(C)$. Suppose that $x in C_1 inter C_2$, where $C_1, C_2 in cal(C)$.For $lambda in Lambda$, let
        $
          C_lambda = cases(
            cal(B)_lambda inter cal(P) bp(pi_lambda (C_1) inter pi_lambda (C_2)) quad& pi_lambda (C_1)\, pi_lambda (C_2) in cal(B)_2,
            pi_lambda (C_1) quad& pi_lambda (C_1) in cal(B)_lambda "and" pi_lambda (C_2) = X_lambda ,
            pi_lambda (C_2) quad& "otherwise"
          )
        $
      Then
        $
          x in product_(lambda in Lambda) C_lambda
            in cal(C) inter cal(P)(C_1 inter C_2)
        $
        so $cal(C)$ is a basis for $tau_Pi$. #qed
    ]
  2.
    Let ${(X_lambda, tau_lambda)}_(lambda in Lambda)$ be a collection of topological spaces, and for $lambda in Lambda$ let $(A_lambda, tau_(A, lambda))$ be a subspace of $X_lambda$. Prove that $product_(lambda in Lambda) A_lambda$ is a subspace of $product_(lambda in Lambda) X_lambda$ while $square.big_(lambda in Lambda) A_lambda$ is a subspace of $square.big_(lambda in Lambda) X_lambda$.
    #sol[
      For $U in tau_(square A)$, each $pi_lambda (U) in tau_(A, lambda)$, so letting $V_lambda in tau_lambda$ such that $U_lambda = V_lambda inter A_lambda$ yields $V := product_(lambda in Lambda) V_lambda in tau_square$ with $U = V inter product_(lambda in Lambda) A_lambda$, so $U$ is also open in the subspace topology

      For $V in tau_square$ and $U := V inter product_(lambda in Lambda) A_lambda$, each $pi_lambda (U) = pi_lambda (V) inter A_lambda in tau_(A, lambda)$, since $pi_lambda (V) in tau_lambda$, meaning that $U in tau_(square A)$ as well.

      Analogous reasoning shows that $square.big_(lambda in Lambda) A_lambda$ is a subspace of $square.big_(lambda in Lambda) X_lambda$. #qed
    ]
  3.
    Show that if ${(X_lambda, tau_lambda)}$ is a family of Hausdorff spaces, then $product_(lambda in Lambda) X_lambda$ and $square.big_(lambda in Lambda) X_lambda$ are as well.
    #sol[
      Let $x, y in product_(lambda in Lambda) X_lambda$, and for each $lambda in Lambda$, let $U_lambda in cal(N)_lambda bp(pi_lambda (x))$ and $V_lambda in cal(N)_lambda bp(pi_lambda (y))$ be disjoint. Then $product_(lambda in Lambda) U_lambda$ and $product_(lambda in Lambda) V_lambda$ are respectively disjoint neighbourhoods of $x$ and $y$ in both the box and product topologies, making both spaces Hausdorff. #qed
    ]
  #pagebreak()
  4.
    For a set ${(X_k, tau_k)}_(k = 1)^n$ of topological spaces, show that $(product_(k = 1)^(n - 1) X_k) times X_n$ is homeomorphic with $product_(k = 1)^n X_k$.
    #sol[
      Let
        $
          f: product_(k = 1)^n X_k &arrow (product_(k = 1)^(n - 1) X_k) times X_n \
          x &mapsto (bp(pi_k (x))_(k = 1)^(n - 1), pi_n (x))
        $
      For $U$ open in $"codom"(f)$, each $pi_k (U)$ is open in $X_k$, making $product_(k = 1)^(n - 1) pi_k (U)$ and $pi_n (U)$ open as well, so their product too is open. Simiiarly, for $V$ open in $"dom"(f)$, each $pi_k compose pi_1 (V)$ and $pi_2 (V)$ is open, so their product is as well. $f$ is thus bicontinuous and trivially bijective, making it a homeomorphism. #qed
    ]
  5.
    Identify which direction of implication holds:
    #shadowed(inset: 4pt)[
      Let ${(A, tau_A)} union {(X_lambda, tau_lambda)}_(lambda in Lambda)$ be a family of topological spaces, and let $f: A arrow square.big_(lambda in Lambda) X_lambda$. Then $f$ is continuous if and only if each $f_lambda$ is continuous.
    ]
    #sol[
      Projection maps are continuous, so if $f$ is continuous then so too is each $f_lambda$ by Theorem 18.2.

      Consider the function
        $
          f: RR &arrow square.big_(n in NN) RR \
            x &mapsto (x^n)_(n in NN)
        $
      For $epsilon in (0, 1)$ preimage of the open set $U := product_(n in NN) (-epsilon, epsilon)$ is ${0}$, which is not open, so despite each component function being continuous, $f$ is not.

    ]
  6.
    Let ${(X_lambda, tau_lambda)}_(lambda in Lambda)$ be a family of topological spaces, and let $(x_n)_(n in NN) in (product_(lambda in Lambda) X_lambda)^NN$. Show that this sequence converges to $x in product_(lambda in Lambda) X_lambda$ if and only each $x_(n, lambda) arrow x_lambda$.
    #sol[
      If $x_n arrow x in product_(lambda in Lambda) X_lambda$, then for any $lambda in Lambda$ and $U in cal(N)_lambda (x_lambda)$, $pi^(-1)(U)$ is a neighbourhood of $x$, so there is some $N in NN$ such that for $n in ZZ_(>= N)$, $x_n in pi^(-1)(U)$ and thus $x_(n, lambda) in U$, so $x_(n, lambda) arrow x_lambda$.

      Suppose conversely that each $x_(n, lambda) arrow x_lambda$, and without loss of generality let $V in cal(N)_Pi (x)$ be a subbasis element, such that only finitely many $V_lambda$ are not $X_lambda$. Let $S = {lambda in Lambda mid(|) V_lambda != X_lambda}$. For $alpha in S$, let $N_alpha in NN$ such that $x_(n, alpha) in pi_alpha (V)$ for $n in ZZ_(>= N_alpha)$, and let $N = max{N_alpha mid(|) alpha in S}$. Then for $n in ZZ_(>= N)$, $x_n in V$, so $x_n arrow x_lambda$, as required. #qed
    ]
  7.
    Let
      $
        RR^infinity = {x in RR^omega mid(|) exists N < omega, forall n in ZZ_(>= N), x_n = 0}
      $
    Find the closures of $RR^infinity$ in the product $tau_Pi$ and box $tau_square$ topologies on $RR^omega$.
    #sol[

    ]
  8.
