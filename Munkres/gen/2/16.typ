#import "../../preamble.typ": *
#show: preamble
=== Section 16 -- The Subspace Topology
  1. Show that a subset of a subspace inherits the same topology from both the subspace and the parent space.
    #sol[
      Let $(Y, tau_Y)$ be a subspace of $(X, tau)$ and let $A subset Y$ inherit topologies $tau_A$ from $Y$ and $tau_A'$ from $X$. Then
        $
          tau_A &= {Z inter U mid(|) U in tau_Y}
              = {Z inter (U inter V) mid(|) V in tau} \
            &= {Z inter U mid(|) U in tau}
        $
        by closure under finite unions. #qed
    ]
  2. Let $tau$ and $tau'$ be topologies on $X$ with the latter strictly finer than the former. How do their subspace topologies on $Y subset.eq X$ compare?
    #sol[
      Let $tau_Y$ and $tau'_Y$ respectively denote the subspace topologies induced by $tau$ and $tau'$. Then
        $
          tau_Y = {Z inter U (|) U in tau}
            subset.eq {Z inter U (|) U in tau'}
        $
        the former is coarser than the latter. If there is some $U in cal(P)(Y) inter (tau' without tau)$, then clearly this relation is strict.

      Consider $X = {1, 2, 3}$, $tau = {nothing, {1}, X}$, $tau' = {nothing, {1}, {2}, {1, 2}, X}$, and $Y = {1}$. Then despite $tau$ being strictly coarser than $tau'$, $tau_Y = tau'_Y$.

    ]
  4.
    A map $f: X -> Y$ between topological spaces $(X, tau_X)$ and $(Y, tau_Y)$ is an *open map* when it carries open sets to open sets. Show that the projection maps from $X times Y$ with the product topology $tau_(X times Y)$ are open maps.
    #sol[
      Let $U in tau_(X times Y)$. By Lemma 13.1, let ${(A_lambda, B_lambda)}_(lambda in Lambda) subset.eq tau_X times tau_Y$ such that
        $ U = union.big_(lambda in Lambda) [A_lambda times B_lambda] $
      Then
        $
          pi_1(U) = pi_1(union.big_(lambda in Lambda) [A_lambda times B_lambda])
            = union.big_(lambda in Lambda) pi_1(A_lambda times B_lambda)
            = union.big_(lambda in Lambda) A_lambda
            in tau_X
        $
        making $pi_1$ an open map. Similarly, $pi_2$ is as well. #qed
    ]
  5.
   Let $tau_X$ and $tau'_X$ be topologies on $X$, let $tau_Y$ and $tau'_Y$ be topologies on $Y$, and let $tau_(X times Y)$ and $tau'_(X times Y)$ denote respectively the product topologies induced by the paris $tau_X$ and $tau_Y$ and $tau'_X$ and $tau'_Y$.
    #set enum(numbering: "(a)")
    1.
      Show that if $tau'_X$ and $tau'_Y$ are respectively finer than $tau_X$ and $tau_Y$, $tau_(X times Y) subset.eq tau'_(X times Y)$
      #sol[
        Let $U in tau_(X times Y)$. Then by Lemma 13.1, some ${(A_lambda, B_lambda)}_(lambda in Lambda) subset.eq tau_X times tau_Y$,
          $ U = union.big_(lambda in Lambda) [A_lambda times B_lambda] $
      ]
      $U$ is a union of basis elements of $tau'_(X times Y)$ and thus one of its elements by closure under unions. As such, $tau_(X times Y) subset.eq tau'_(X times Y)$. #qed
    2.
      Suppose conversely that $tau_(X times Y) subset.eq tau'_(X times Y)$, and determine whether it must be the case that $tau_X subset.eq tau'_X$ and $tau_Y subset.eq tau'_Y$.
      #sol[
        Let $U in tau_X$ and $V in tau_Y$. Then $U times V in tau'_(X times Y)$, so by Lemma 13.1, let ${(A_lambda, B_lambda)}_(lambda in Lambda) subset.eq tau'_X times tau'_Y$ such that
          $
            U times V = union.big_(lambda in Lambda) [A_lambda times B_lambda]
          $
          Clearly, $U = union.big_(lambda in Lambda) A_lambda in tau'_X$ and $V = union.big_(lambda in Lambda) B_lambda in tau'_Y$, making them respectively finer than $tau_X$ and $tau_Y$. #qed
      ]
6.
  Show that
    $ cal(B) = {(a, b) times (c, d) mid(|) a < b in QQ, c < d in QQ} $
    is a basis for the standard topology $tau_2$ on $RR^2$.
    #sol[
      Let $U in tau_2$ and let $x in U$. By Lemma 13.1, let ${(A_lambda, B_lambda)}_(lambda in Lambda) subset.eq tau times tau$ such that
        $ U = union.big_(lambda in Lambda) [A_lambda times B_lambda] $
        and let $alpha in Lambda$ such that $a in A_alpha times B_alpha$.
      By #outlink(label("8a"), "13.8.(a)"),
        $ cal(C) = {(a, b) mid(|) a < b in QQ} $
        is a basis for the standard topology $tau$ on $RR$, so by Lemma 13.1, let ${C_n}_(n in N), {D_n}_(n in N) subset.eq cal(C)$ such that
        $
          A_alpha = union.big_(n in NN) C_n quad "and" quad
            B_alpha = union.big_(n in NN) D_n
        $
      For some $n in NN$, $x in C_n times D_n in cal(B) inter cal(P)(U)$, making $cal(B)$ a basis for $(RR_2, tau_2)$ by Lemma 13.2. #qed
    ]
7. Are all convex strict subsets of an ordered set necessarily either intervals or rays?
  #sol[
    Consider
      $ Y = {x in QQ mid(|) x^2 < 2} $
      with the usual order. This is cleary convex, but as it lacks a supremum in $QQ$, it is neither an interval nor a ray.
  ]
