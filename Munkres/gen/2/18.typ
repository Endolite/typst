#import "../../preamble.typ": *
#show: preamble

=== Section 18 -- Continuous Functions
  1.
    Show that the topological and $epsilon$-$delta$ definition of continuity on for $RR^RR$ are equivalent.
    #sol[
      Let $f: RR -> RR$ be continuous in the topological sense, and let $x in RR$ and $delta > 0$. Since $B(x, epsilon)$ is open, so is its preimage under $f$, so by Lemma 13.1, let ${I_lambda}_(lambda in Lambda)$ be a collection of open intervals such that
        $ f^(-1)bp(B(x, epsilon)) = union.big_(lambda in Lambda) I_lambda $
      Let $alpha in Lambda$ such that $x in I_alpha$, and let
        $ delta = min{ x- inf(I_alpha), sup(I_alpha) - x} $
      Then $B(x, delta) subset.eq I_lambda subset.eq f^(-1)bp(B(x, epsilon))$, so $f bp(B(x, delta)) subset.eq B(x, epsilon)$, making $f$ continuous in the $epsilon$-$delta$ sense.

      Let $g: RR -> RR$ be continuous in the $epsilon$-$delta$ sense, and let $U subset.eq RR$ be open. By Lemma 13.1, let ${I_lambda}_(lambda in Lambda)$ be a colletion of open sets such that
        $ U = union.big_(lambda in Lambda) I_lambda $
      For each $x in f^(-1)(U)$, there is some $alpha_x in Lambda$ such that $f(x) in I_alpha_x$ and thus some $epsilon_x > 0$ such that $B lr((f(x), epsilon_x), size: #115%) subset.eq I_alpha_x$ and some corresponding $delta_x > 0$ such that $f bp(B(x, delta_x)) subset.eq B lr((f(x), epsilon_x), size: #115%)$, so
        $ f^(-1)(U) = union.big_(x in f^(-1)(U)) B(x, delta_x) $
        is open, making $f$ topological continuous. #qed
    ]
  2.
    Let $f: X -> Y$ be a continuous function between spaces $(X, tau_X)$ and $(Y, tau_Y)$. If $x$ is a limit point of $A subset.eq X$, is $f(x)$ a limit point of $f(A)$?
    #sol[
      Suppose that $Y$ is $T_1$. Let $U in tau_X$, let $y in Y$, and let
        $
          f: X &-> Y \
            x &mapsto y
        $
      This is trivially continuous, but ${y}$ is a singleton and thus closed, meaning that it contains all of its limit points by Corollary 17.7, but since no neighbourhood of $y$ can intersect ${y}$ nontrivially, the set lacks limit points altogether.

    ]
  3.
    Let $X$ be a set in topologies $tau$ and $tau'$ and let $iota: X -> X$ be the identity function from $(X, tau')$ to $(X, tau)$, where these are the respective subspace topologies.
    #set enum(numbering: "(a)")
    1.
      Show that $iota$ is continuous if and only if $tau' supset.eq tau$.
      #sol[
        Suppose that $iota$ is continuous. Then for every $U in tau$, $iota^(-1)(U) = U in tau'$, so $tau' supset.eq tau$.

        Suppose conversely that $tau' supset.eq tau$. Then for $U in tau$, $iota^(-1)(U) = U in tau'_X$, making $iota$ continuous. #qed
      ]
    2.
      Show that $iota$ is a homeomorphism if and only if $tau' = tau$.
      #sol[
        Suppose that $iota$ is a homeomorphism. Then $U in tau$ if and only if $iota^(-1)(U) = U in tau'$, so $tau = tau'$.

        Suppose conversely that $tau' = tau$. Then $U in tau$ if and only if $U = iota^(-1) in tau'$, so $iota$ is a homeomorphism.\ #qed
      ]
  4.
