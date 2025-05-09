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
      Show #label("18.9.a") that if ${A_lambda}_(lambda in Lambda)$ is finite and each $A_lambda$ is closed, then $f$ is continuous.
      #sol[
        Let $U subset.eq Y$ be closed. Then by Theorem 18.1, each $f|^(-1)_A_lambda #h(-0.5mm) (U)$ is closed in $A_lambda$, and by theorem 17.3 also in $X$, so
          $ f^(-1)(U) = union.big_(lambda in Lambda) f|^(-1)_A_lambda #h(-0.5mm) (U) $
          is closed in $X$ by Theorem 17.1.(c), making $f$ continuous. #qed
      ]
    2.
      Find an example where the collection of closed subsets is countable but $f$ is not continuous.
      #sol[
        For $n in NN$, let $ I_n = overline(B)_RR (0, 1 - 2^(-n))$, let $A = RR without (0, 1)$, consider $chi_((0, 1)): RR arrow RR$. This is constant on each $I_n$ and $A$ and thus continuous by Theorem 18.2.(a), but it is discontinuous on
          $ A union union.big_(n in NN) I_n = RR $
          since the preimage of the open set $(-1, 1)$ is the closed set ${0, 1}$.

      ]
    3.
      A collection ${A_lambda}_(lambda in Lambda)$ of subsets of $(X, tau)$ is _locally finite_ when each $x in X$ has some $U in cal(N)(x)$ that intersects only finitely many $A_lambda$.

      Show that if ${A_lambda}_(lambda in Lambda)$ is locally finite and each element closed, then $f$ is continuous.
      #sol[
        Let $x in X$ and let $U_x in cal(N)_X (x)$ such that for $lambda$ in some finite $Lambda_x$, $U_x inter A_lambda != emptyset$. By Theorem 17.2, each $U_x inter A_lambda$ is closed in $U_x$. Furthermore,
          $
            U_x &= U_x inter union.big_(lambda in Lambda) A_lambda
                = union.big_(lambda in Lambda) [U_x inter A_lambda]
                = union.big_(lambda in Lambda_x)  [U_x inter A_lambda] union union.big_(lambda in Lambda without Lambda_x) [U_x inter A_lambda] \
              &= union.big_(lambda in Lambda_x) [U_x inter A_x] union emptyset
                = union.big_(lambda in Lambda_x) [U_x inter A_x]
          $
          so by #link(label("18.9.a"))[18.9.(a)], $f|_(U_x)$ is continuous, meaning that by Theorem 18.2.(f), $f$ is continuous. #qed
      ]
  10.
    Let $(A, tau_A)$, $(B, tau_B)$, $(C, tau_C)$, and $(D, tau_D)$ be topological spaces, let $f: A arrow B$ and $g: C arrow D$ be continuous. Show that
      $
        f times g: A times C &arrow B times D \
          (a, c) &mapsto bp(f(a)\, g(c))
      $
      is continuous in the product topologies $tau_(A times C)$ and $tau_(B times D)$.
    #sol[
      For $U in tau_B$,
        $
          (f times g)_1^(-1)(U) &= {(a, c) in A times C mid(|) f(a) in U} \
            &= {a in A mid(|) f(a) in U} times C \
            &= f^(-1)(U) times C
              in tau_A times tau_C
              subset.eq tau_(A times C)
        $
        and similarly,
        $
          (f times g)_2^(-1)(V) = A times g^(-1)(V)
            in tau_A times tau_C
              subset.eq tau_(A times C)
        $
        making both component functions and thus, by Theorem 18.4 $f times g$ continuous. #qed
    ]
  11.
    Let $(X, tau_X)$, $(Y, tau_Y)$, and $(Z, tau_Z)$ be topological spaces. $F: X times Y arrow Z$ is _continuous in each variable separately_ when for $y_0 in Y$,
      $
        h: X &arrow Z \
          x &mapsto F(x, y_0)
      $
      and for $x_0 in X$,
      $
        k: Y &arrow Z \
          y &mapsto F(x_0, y)
      $
      are continuous. Show that continuity implies continuity in each variable separately.
    #sol[
      Let $F: X times Y arrow Z$ be continuous, $U in tau_Z$, $x_0 in X$, and $y_0 in Y$. By Lemma 13.1, let ${(A_lambda, B_lambda)}_(lambda in Lambda) subset.eq tau_X times tau_Y$ with
        $ f^(-1)(U) = union.big_(lambda in Lambda) [A_lambda times B_lambda] $
      Then
        $
          h^(-1)(U) &= {x in X mid(|) F(x, y_0) in U}
              = {(x, y) in F^(-1)(U) mid(|) y = y_0} \
            &= pi_1(F^(-1)(U) inter (X times {y_0}))
              = pi_1(F^(-1)(U)) inter pi_1(X times {y_0}) \
            &= pi_1(union.big_(lambda in Lambda) [A_lambda times B_lambda]) inter X
              = union.big_(lambda in Lambda) pi_1(A_lambda times B_lambda)
              = union.big_(lambda in Lambda) A_lambda
              in tau_X
        $
      Analogously,
        $
          k^(-1)(U) = pi_2(F^(-1)(V))
            in tau_Y
        $
        making $F$ continuous in each variable separately. #qed
    ]
  13.
    Let $(A, tau_A)$ be a subspace of $(X, tau_X)$, let $(Y, tau_Y)$ be Hausdorff, and let $f: A arrow Y$ be continuous. Show that if $f$ can be extended to some continuous $g: overline(A) arrow Y$, then $g$ is uniquely determined by $f$.
    #sol[
      Let $g, h in Y^(overline(A))$ with $f = g|_A = h|_A$. Suppose that $A != overline(A)$; that is, $A$ is not closed. By Theorem 17.6, $overline(A) without A = A' without A$, so let $x in A' without A$. Suppose further that $g(x) != h(x)$. Since $Y$ is Hausdorff, let $U in cal(N)circ_Y bp(g(x)) without cal(N)circ_Y bp(h(x))$ and $V in cal(N)circ_Y bp(h(x)) without cal(N)circ_Y bp(g(x))$. Since $U inter V = emptyset$ and $g$ and $h$ may only differ on $A' without A$, $f^(-1)(U) inter f^(-1)(V) = emptyset$, but $g^(-1)(U) inter h^(-1)(V) in cal(N)circ_overline(A) (x)$, so there must be some
        $
          x in (g^(-1)(U) inter h^(-1)(V) ) inter A
            = g|^(-1)_A #h(-0.5mm) (U) inter h|^(-1)_A #h(-0.5mm) (V)
            = f^(-1)(U) inter f^(-1)(V)
            = emptyset
        $
        which is impossible. It must be the case that $g$ and $h$ coincide; that is, that the continuous extension of $f$ be unique. #qed
    ]
