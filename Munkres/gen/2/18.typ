#import "../../preamble.typ": *
#show: preamble

=== Section 18 -- Continuous Functions
  1.
    Show that the topological and $epsilon$-$delta$ definitions of continuity on for $RR^RR$ are equivalent.
    #sol[
      Let $f: RR arrow RR$ be continuous in the topological sense, and let $x in RR$ and $delta > 0$. Since $B(x, epsilon)$ is open, so is its preimage under $f$, so by Lemma 13.1, let ${I_lambda}_(lambda in Lambda)$ be a collection of open intervals such that
        $ f^(-1)bp(B(x, epsilon)) = union.big_(lambda in Lambda) I_lambda $
      Let $alpha in Lambda$ such that $x in I_alpha$, and let
        $ delta = min{ x- inf(I_alpha), sup(I_alpha) - x} $
      Then $B(x, delta) subset.eq I_lambda subset.eq f^(-1)bp(B(x, epsilon))$, so $f bp(B(x, delta)) subset.eq B(x, epsilon)$, making $f$ continuous in the $epsilon$-$delta$ sense.

      Let $g: RR arrow RR$ be continuous in the $epsilon$-$delta$ sense, and let $U subset.eq RR$ be open. By Lemma 13.1, let ${I_lambda}_(lambda in Lambda)$ be a collection of open sets such that
        $ U = union.big_(lambda in Lambda) I_lambda $
      For each $x in g^(-1)(U)$, there is some $alpha_x in Lambda$ such that $g(x) in I_alpha_x$ and thus some $epsilon_x > 0$ such that $B bp((g(x), epsilon_x)) subset.eq I_alpha_x$ and some corresponding $delta_x > 0$ such that $g bp(B(x, delta_x)) subset.eq B bp(g(x)\, epsilon_x)$, so
        $ g^(-1)(U) = union.big_(x in g^(-1)(U)) B(x, delta_x) $
        is open, making $g$ topologically continuous. #qed
    ]
  2.
    Let $f: X arrow Y$ be a continuous function between spaces $(X, tau_X)$ and $(Y, tau_Y)$. If $x$ is a limit point of $A subset.eq X$, is $f(x)$ a limit point of $f(A)$?
    #sol[
      Suppose that $Y$ is $T_1$. Let $U in tau_X$, let $y in Y$, and let
        $
          f: X &arrow Y \
            x &mapsto y
        $
      This is trivially continuous, but ${y}$ is a singleton and thus closed, meaning that it contains all of its limit points by Corollary 17.7, but since no neighbourhood of $y$ can intersect ${y}$ nontrivially, the set lacks limit points altogether.

    ]
  3.
    Let $X$ be a set in topologies $tau$ and $tau'$ and let $iota: X arrow X$ be the identity function from $(X, tau')$ to $(X, tau)$, where these are the respective subspace topologies.
    #set enum(numbering: "(a)")
    1.
      Show that $iota$ is continuous if and only if $tau' supset.eq tau$.
      #sol[
        Suppose that $iota$ is continuous. Then for every $U in tau$, $iota^(-1)(U) = U in tau'$, so $tau' supset.eq tau$.

        Suppose conversely that $tau' supset.eq tau$. Then for $U in tau$, $iota^(-1)(U) = U in tau'_X$, making $iota$ continuous. #qed
      ]
    2.
      Show #label("18.3.b") that $iota$ is a homeomorphism if and only if $tau' = tau$.
      #sol[
        Suppose that $iota$ is a homeomorphism. Then $U in tau$ if and only if $iota^(-1)(U) = U in tau'$, so $tau = tau'$.

        Suppose conversely that $tau' = tau$. Then $U in tau$ if and only if $U = iota^(-1) in tau'$, so $iota$ is a homeomorphism.\ #qed
      ]
  4.
    Let $(X, tau_X)$ and $(Y, tau_Y)$ be topological spaces, and let $x_0 in X$ and $y_0 in Y$. Show that
      $
        f: X &arrow X times Y quad "and" quad&
            g: Y &arrow x times Y \
          x &mapsto (x, y_0) &
              y &mapsto (x_0, y)
      $
      are embeddings into the product space $(X times Y, tau_(X times Y))$.
    #sol[
      By #link(label("18.3.b"), [3.(b)]), $f_1$ and $g_2$ are are continuous, and both are clearly surjective, so $f$ and $g$ are surjective as well; and by Theroem 18.2.(a), $f_2$ and $g_1$ are also continuous, making $f$ and $g$ continuous by Theorem 18.4.

      Let $(f(X), tau_(f(X)))$ and $(g(Y), tau_(g(Y)))$ denote the subspace on $f(X) = X times {y_0}$ and $g(Y) = {x_0} times Y$, and let $A in tau_(f(X))$. Let $B in tau_(X times Y)$ such that $A = f(X) inter B$. Then since $f$ is continuous, $f^(-1)(B) in tau_X$, so
        $
          f^(-1)(A) = f^(-1)bp(f(X) inter B)
            = X inter f^(-1)(B)
            in tau_X
        $
      For $C in tau_X$,
        $
          f(C) = C times {y_0}
            = f(X) inter (C times Y)
            in tau_(f(X))
        $
        making $f$ in embedding. Similarly for $D in tau_(g(Y))$ and $E in tau_(X times Y)$ with $D = g(Y) inter E$,
        $
          g^(-1)(D) = g^(-1)bp(g(Y) inter E)
            = Y inter g^(-1)(E)
            in tau_Y
        $
        while for $F in tau_Y$,
        $
          g(F) = {x_0} times F
            = g(Y) inter (X times F)
            in tau_(g(Y))
        $
        so $g$ is also an embedding. #qed
    ]
  5.
    Show that $(a, b), (0, 1) subset.eq RR$ are homeomorphic, as are $[a, b], [0, 1] subset.eq RR$, for $a < b in RR$, with the standard topology.
    #sol[
      Let
        $
          f: [a, b] &arrow [0, 1] \
            x &mapsto frac(x - a, b - a)
        $
      This is clearly a bijection, as is
        $
          g: (a, b) &arrow (0, 1) \
            x &mapsto f(x)
        $
      Let $U$ be open in $[0, 1]$, and let $V$ be open in $RR$ with $U = [0, 1] inter V$. By Lemma 13.1, let ${(c_lambda, d_lambda)}_(lambda in Lambda)$ be a collection of open intervals such that
        $
          V = union.big_(lambda in Lambda) (c_lambda, d_lambda)
        $
      Then
        $
          U = [0, 1] inter union.big_(lambda in Lambda) (c_lambda, d_lambda)
            = union.big_(lambda in Lambda) bpp([0, 1] inter (c_lambda, d_lambda)])
        $
      For $alpha in Lambda$,
        $
          f^(-1)bp([0, 1] inter (c_alpha, d_alpha)) = cases(
            [a, b] quad& c_alpha\, d_alpha in.not [0, 1],
            (f^(-1)(c_alpha), b] = (f^(-1)(c_alpha), b + 1) inter [a, b] quad& c_alpha in [0, 1]\,  d_alpha > 1,
            bpp([a, f^(-1)(b))) = bp(a - 1\, f^(-1)(b)) inter [a, b] & c_alpha < 0\, d_alpha in [0, 1],
            bp(f^(-1)(c_alpha)\, f^(-1)(d_alpha)) quad& c_alpha\, d_alpha in [0, 1] ,
          )
        $
        so
        $
          f^(-1)(U) = f^(-1)(union.big_(lambda in Lambda) bpp([[0, 1] inter (c_lambda, d_lambda)]))
            = union.big_(lambda in Lambda) f^(-1)bp([0, 1] inter (c_lambda, d_lambda))
        $
        is open in $[a, b]$. Similarly, let $U'$ be open in $[a, b]$, let $V'$ be open in $RR$ with $U' = [a, b] inter V$, and by Lemma 13.1 let ${(c'_lambda, d'_lambda)}_(lambda in Lambda)$ such that
        $
          U' = [a, b] inter V
            = [a, b] inter union.big_(lambda in Lambda) (c'_lambda, d'_lambda)
              = union.big_(lambda in Lambda) bpp([[a, b] inter (c'_lambda, d'_lambda)])
        $
      Then for $alpha in Lambda$,
        $
          f bp([a, b] inter (c'_alpha, d'_alpha)) = cases(
            [0, 1] quad& c'_alpha\, d'_alpha in.not [a, b],
            bpp((f(c'_alpha), 1]) = bp(f(c'_alpha)\, 2)inter [0, 1] quad& c'_alpha in [a, b]\, d'_alpha > 1 ,
            bpp([0, f(d'_alpha))) = bp(-1\, f(d'_alpha)) inter [0, 1] quad& c'_alpha < a\, d'_alpha in [a, b] \
            bp(f(c'_alpha)\, f(d'_alpha)) quad& c'_alpha\, d'_alpha in [a, b]
          )
        $
        meaning that
        $
          f(U') = f(union.big_(lambda in Lambda) bpp([[a, b] inter (c'_lambda, d'_lambda)]))
            = union.big_(lambda in Lambda) f bp([a, b] inter (c'_lambda, d'_lambda))
        $
        is open in $[a, b]$, making $f$ a homeomorphism.

      Let $A$ be open in $(0, 1)$. Then by Lemmas 16.1 and 13.1, let ${(e_lambda, f_lambda)}_(lambda in Lambda) subset.eq cal(P)bp((0, 1))$ such that
        $
          A = union.big_(lambda in Lambda) (e_lambda, f_lambda)
        $
      For $alpha in Lambda$,
        $
          g^(-1)bp((e_alpha, f_alpha)) = (g^(-1)(e_alpha)\, g^(-1)(f_alpha))
        $
        yielding that
        $
          g^(-1)(A) = g^(-1)(union.big_(lambda in Lambda) (e_alpha, f_alpha))
            = union.big_(lambda in Lambda) (g^(-1)(e_alpha), g^(-1)(f_alpha))
        $
        is open in $(a, b)$. Analogously, let $B$ be open in $(a, b)$, and by Lemmas 16.1 and 13.1, let ${(e'_lambda, f'_lambda)}_(lambda in Lambda) subset.eq cal(P)bp((a, b))$ with
        $
          B = union.big_(lambda in Lambda) (e'_lambda, f'_lambda)
        $
      Then for $alpha in Lambda$,
        $
          g bp((e'_lambda, f'_lambda)) = bp(g(e'_lambda)\, g(f'_lambda))
        $
        so
        $
          g(B) = g(union.big_(lambda in Lambda) (e'_lambda, f'_lambda))
            = union.big_(lambda in Lambda) g bp((e'_lambda, f'_lambda))
        $
        is open in $(0, 1)$, making $g$ a homeomorphism as well. #qed
    ]
  9.
    Let ${A_lambda}_(lambda in Lambda)$ be a collection of subsets of $(X, tau_X)$ such that $X = union.big_(lambda in Lambda) A_lambda$, let $(Y, tau_Y)$ be a topological space, and let $f: X arrow Y$ such that each $f|_A_alpha$ is continuous.
    #set enum(numbering: "(a)")
    1.
      Show that if ${A_lambda}_(lambda in Lambda)$ is finite and each $A_lambda$ is closed, then $f$ is continuous.
      #sol[
        Let $U subset.eq Y$ be closed. Then by Theorem 18.1, each $f|^(-1)_A_lambda #h(-0.5mm) (U)$ is closed in $A_lambda$, and by theorem 17.3 also in $X$, so
          $ f^(-1)(U) = union.big_(lambda in Lambda) f|^(-1)_A_lambda #h(-0.5mm) (U) $
          is closed in $X$ by Theorem 17.1.(c), making $f$ continuous. #qed
      ]
    2.
      Find an example where the collection of closed subsets is countable but $f$ is not continuous.
      #sol[
        For $n in NN$, let
          $ A_n = [frac(1, 2^n) - 1, 1 - frac(1, 2^n)] $
          and consider $chi_((0, 1)): [0, 1] arrow$
      ]
