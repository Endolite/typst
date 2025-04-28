#import "../../preamble.typ": *
#show: preamble

=== Section 17 -- Closed Sets and Limit Points
  1.
    Let $cal(C) subset.eq cal(P)(X)$ with $nothing, X in cal(C)$ be closed under finite unions and arbitrary intersections. Show that
      $ tau = {X without C mid(|) C in cal(C)} $
      is a topology.
    #sol[
      $X without nothing = X$ while $X without X = nothing$, so both are in $tau$. For ${U_lambda}_(lambda in Lambda), {V_i}_(i = 1)^n subset.eq tau$,
        $
          union.big_(lambda in Lambda) U_lambda = X without inter.big_(lambda in Lambda) [X without U_lambda]
            in tau
        $
        by closure under intersections and
        $
          inter.big_(i = 1)^n V_i = X without union.big_(i = 1)^n [X without V_i]
            in tau
        $
        by closure under finite intersections, making $tau$ a topology. #qed
    ]
  2.
    Show that if $A$ is closed in a subspace $(Y, tau_Y)$ which is itself closed in $(X, tau)$, then $A$ is closed in $X$.
    #sol[
      By Theorem 17.2, $A = C inter Y$ for some closed $C subset.eq X$, making $A$ the intersection of two closed sets and hence itself closed. #qed
    ]
  3.
    Show that if $A$ is closed in $(X, tau_X)$ and $B$ is closed in $(Y, tau_Y)$, then $A times B$ is closed in the product space $(X times Y, tau_(X times Y))$.
    #sol[
      Since $A$ and $B$ are closed, $X without A$ and $Y without B$ are both open, so their product is a basis element of $tau_(X times Y)$, making
        $ A times B = (X times Y) without bp((X without A) times (X without B)) $
        closed. #qed
    ]
  4.
    Show that if $U$ and $A$ are respectively open and closed in $(X, tau)$, then $U without A$ is open while $A without U$ is closed.
    #sol[
      By closure under finite intersections,
        $
          U without A = U inter (X without A) in tau
        $
        while by Theorem 17.1,
        $ A without U = A inter (X without U) $
        is closed. #qed
    ]
  5.
    Show that in the order topology $tau$ on $(X, <)$, $overline((a, b)) subset.eq [a, b]$ for $a < b in X$, and determine when equality holds.
    #sol[
      For $x < a$, $(-infinity, a)$ is a neighbourhood that does not intersect $(a, b)$, while for $y > b$, $(b, infinity)$ suffices. As such, neither may be limit points of $(a, b)$, so $overline((a, b)) subset.eq [a, b]$. Equality holds when $a$ and $b$ are themselves limit points of $X$. #qed
    ]
  6.
    Let $(X, tau)$ be a topological space and let ${A, B} union {A_lambda}_(lambda in Lambda) subset.eq cal(P)(X)$, and prove the following:
    #set enum(numbering: "(a)")
    1. If $A subset.eq B$, then $overline(A) subset.eq overline(B)$
      #sol[
        Let $x in A'$. Then for all $U in cal(N)^* (x) $, $U inter A subset.eq U inter B$ is nonempty, so $x in B'$. Since $A subset.eq B subset.eq overline(A)$,
          $
            overline(A) = A union A'
              subset.eq B union B'
              = overline(B)
          $
          by Theorem 17.6. #qed
      ]
    2.
      $overline(A union B) = overline(A) union overline(B)$.
      #sol[
        By Theorem 17.6, $overline(A union B) = (A union B) union (A union B)'$, $overline(A) = A union A'$, and $overline(B) = B union B'$. If $x in A union B$, then clearly $x in overline(A) union overline(B)$. Let $x in (A union B)'$. Then for all $U in cal(N)^* (x)$, $U inter (A union B)$ is nonempty, so either $U inter A$ or $U inter B$ is nonempty, making $x$ a limit point of either $A$ or $B$ and thus an element of $overline(A) union overline(B)$. By proxy, $overline(A union B) subset.eq overline(A) union overline(B)$.

        If $x in A$ or $x in B$, then $x in A union B$ by definition. If $x in A'$, then for each $U in cal(N)^*(x)$, $U inter A != emptyset$, so $U inter (A union B) != emptyset$; that is, $x in (A union B)'$, so $overline(A union B) = overline(A) union overline(B)$ #qed
      ]
    3.
      $overline(union.big_(lambda in Lambda) A_lambda) supset.eq union.big_(lambda in Lambda) overline(A_lambda)$, and equality may not hold.
      #sol[
        By Theorem 17.6, $overline(A_alpha) = A_alpha union A'_alpha$ for each $alpha in Lambda$ and
        $ overline(union.big_(lambda in Lambda) A_lambda) = union.big_(lambda in Lambda) A_lambda union (union.big_(lambda in Lambda) A_lambda)' $
        Let $alpha in Lambda$. If $x in A_alpha$ then clearly $x in overline(union.big_(lambda in Lambda) A_lambda)$. If $x in A'_alpha$, then for each $U in cal(N)^*(x)$, $U inter A_alpha != emptyset$, so $U inter union.big_(lambda in Lambda) A_lambda$ is also nonempty; that is, $union.big_(lambda in Lambda) overline(A_lambda) subset.eq overline(union.big_(lambda in Lambda) A_lambda)$.

        Let $B_n = [2^(-n), 1]$ for $n in NN$. Then in the standard topology on $RR$, each $B_n$ is closed and thus contains all of its limit points, but
          $
            B = union.big_(n in NN) B_n
              = (0, 1]
          $
          is not, having 0 as a limit point, meaning that $overline(B) supset union.big_(n in NN) overline(B_n)$. #qed
      ]
  9.
    Let $A$ and $B$ be subsets of $(X, tau_X)$ and $(Y, tau_Y)$ respectively. Show that in the product space $(X times Y, tau_(X times Y))$, $"Cl"_(X times Y)(A times B) = "Cl"_X (A) times "Cl"_Y (B)$.
    #sol[
      By Theorem 17.6,
        $
          "Cl"_(X times Y)(A times B) &= (A times B) union "Lim"_(X times Y)(A times B) \
          "Cl"_X (A) &= A union "Lim"_X (A) \
          "Cl"_Y (B) &= B union "Lim"_Y (B)
        $
      For $(x, y) in "Lim"_(X times Y)(A times B) $, $U in cal(N)^*_X (x)$, and $V in cal(N)^*_Y (x)$, $U times V$ is a punctured neighbourhood of $(x, y)$ and thus intersects $A times B$, meaning that $A inter U$ and $B inter V$ must be nonempty, as if either were empty, the product $(A inter U) times (B inter Y) = (A times B) inter (U times Y)$ would be as well. This implies that $"Cl"_(X times Y)(A times B) subset.eq "Cl"_X (A) times "Cl"_Y (B)$.

      If $x in "Lim"_X (A)$, $y in "Lim"_Y (B)$, and $U in cal(N)^*_(X times Y)bp((x, y))$, then by Lemma 13.1, there are some ${(C_lambda, D_lambda)}_(lambda in Lambda) subset.eq tau_X times tau_Y$ such that
        $ U = union.big_(lambda in Lambda) [C_lambda times D_lambda] $
      Each $C_lambda$ and $D_lambda$ is respectively a punctured neighbourhood of $x$ and $y$ and therefore respectively intersect $A$ and $B$, meaning that their product intersects $A$ and $B$, as does $U$ by proxy. As such, $"Cl"_(X times Y)(A times B) = "Cl"_X (A) times "Cl"_Y (B)$. #qed
    ]
  11.
    Show that the product of two Hausdorff spaces is Hausdorff.
    #sol[
      Let $(X, tau_X)$ and $(Y, tau_Y)$ be Hausdorff spaces, let $(X times Y, tau_(X times Y))$ denote their product, and let $x != y in X times Y$. If $pi_1(x) != pi_1(y)$, let $U in cal(N)circ_X bp(pi_1(x))$ and $V in cal(N)circ_X bp(pi_1(y))$ to obtain disjoint $U times Y in cal(N)circ_(X times Y) (x)$ and $V times Y in cal(N)circ_(X times Y) (y)$; otherwise, let $U in cal(N)circ_X bp(pi_2(x))$ and $V in cal(N)circ_Y bp(pi_2(y))$ for disjoint $X times U in cal(N)circ_(X times Y) (x)$ and $X times V in cal(N)circ_(X times Y) (y)$. In either case, the existence of such neighbourhoods makes the product space Hausdorff. #qed
    ]
  12.
    Show that a subspace of a Hausdorff space is Hausdorff.
    #sol[
      Let $(A, tau_A)$ be a subspace of a Hausdorff space $(X, tau)$, and let $x != y in A$. If $U in cal(N)circ_X (x)$ and $V in cal(N)circ_X (y)$ are disjoint, then so are $U inter A in cal(N)circ_A (x)$ and $V inter A in cal(N)circ_A (y)$, making $A$ Hausdorff. #qed
    ]
  13.
    Show that $(X, tau)$ is Hausdorff if and only if the *diagonal*
      $
        Delta eq.delta {(x, x) mid(|) x in X}
      $
      is closed in the product space $(X times X, tau_2)$.
    #sol[
      Suppose that $(X, tau)$ is Hausdorff, and let $x != y in X$. Let $U in cal(N)degree (x)$ and $V in cal(N)degree (y)$ be disjoint. Then since $U times V in cal(N)circ_2 bp((x, y))$ does not intersect $Delta$, since neither set contains a duplicate from the other, $(x, y)$ is not a limit point of $Delta$, which therefore contains all of its is limit points and is thusly closed by Corollary 17.7.

      Suppose conversely that $Delta$ is closed in the product space, and let $x != y in X$. Then by Corollary 17.7, it contains all of its limit points, so $(x, y) in.not "Lim"_2(Delta)$; that is, there is some $U in cal(N)circ_2 bp((x, y))$ disjoint from $Delta$. By Lemma 13.1, let ${(A_lambda, B_lambda)}_(lambda in Lambda) in tau times tau$ such that
        $ U = union.big_(lambda in Lambda) [A_lambda times B_lambda] $
      Then
        $
          x in pi_1(U)
            = pi_1(union.big_(lambda in Lambda) [A_lambda times B_lambda])
            = union.big_(lambda in Lambda) A_lambda
            in cal(N)degree (x)
        $
        and similarly, $pi_2(U) in cal(N)degree (y)$, separating $x$ and $y$ and making $X$ Hausdorff. #qed
    ]
  15.
    Show that the $T_1$ axioms is equivalent to the condition that all distinct pairs of points have a neighbourhood not containing the other.
    #sol[
      Suppose that $(X, tau)$ is a $T_1$-space, and let $x != y in X$. Then $X without {y} in cal(N)degree (x)$ and $X without {x} in cal(N)degree (y)$ are neighbourhoods not containing the other point.

      Suppose conversely that for all $x != y in X$, there are some $U in cal(N)degree (x)$ and $V in cal(N)degree (y)$ such that neither point is in the other's neighbourhood. Let $x in X$ and for $y in X without {x}$, let $U_y in cal(N)degree (y)$ such that $x in.not U_y$. Then
        $ union.big_(y in X without {x}) U_Y = X without {x} in tau $
        so ${x}$ is closed; that is, singletons are closed, so $X$ is $T_1$. #qed
    ]
