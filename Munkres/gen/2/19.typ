#import "../../preamble.typ" : *
#show: preamble

=== Section 19 -- The Product Topology
  1.
    Let ${(X_lambda, tau_lambda)_(lambda in Lambda)}$ be a family of toplogical spaces, with $tau_lambda$ having basis $cal(B)_lambda$. Prove that
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
            cal(B)_lambda inter cal(P) bp(pi_lambda (C_1) inter pi_lambda (C_2)) quad& pi_lambda (C_1)\, pi_lambda (C_2) in cal(B)_2 \
            pi_lambda (C_1) quad& pi_lambda (C_1) in cal(B)_lambda "and" pi_lambda (C_2) = X_lambda \
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
    Let ${(X_lambda, tau_lambda)}_(lambda in Lambda)$ be a collection of topological spaces, and for $lambda in Lambda$ let $(A_lambda, tau_(lambda, A))$ be a subspace of $X_lambda$. Prove that $product_(lambda in Lambda) A_lambda$ is a subspace of $product_(lambda in Lambda) X_lambda$ while $square.big_(lambda in Lambda) A_lambda$ is a subspace of $square.big_(lambda in Lambda) X_lambda$.
  3.
    Show that if ${(X_lambda, tau_lambda)}$ is a family of Hausdorff spaces, then $product_(lambda in Lambda) X_lambda$ and $square.big_(lambda in Lambda) X_lambda$ are as well.
