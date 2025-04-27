#import "../preamble.typ": *
#show: preamble
= Section 16 -- The Subspace Topology
  1. Show that a subset of a subspace inherits the same topology from both the subspace and the parent space.
    #sol[
      Let $(Y, tau_Y)$ be a subspace of $(X, tau)$ and let $A subset Y$ inherit topologies $tau_A$ from $Y$ and $tau_A'$ from $X$. Then
        $
          tau_A &= {Z inter U | U in tau_Y}
              = {Z inter (U inter V) | V in tau} \
            &= {Z inter U | U in tau}
        $
        by closure under finite unions. #qed
    ]
  2. Let $tau$ and $tau'$ be topologies on $X$ with the latter strictly finer than the former. How do their subspace topologies on $Y subset.eq X$ compare?
    #sol[
      Let $tau_Y$ and $tau'_Y$ respectively denote the subspace topologies induced by $tau$ and $tau'$. Then
        $
          tau_Y = {Z inter U | U in tau}
            subset.eq {Z inter U | U in tau'}
        $
        the former is coarser than the latter. If there is some $U in cal(P)(Y) inter (tau' without tau)$, then clearly this relation is strict.

      Consider $X = {1, 2, 3}$, $tau = {diameter, {1}, X}$, $tau' = {diameter, {1}, {2}, {1, 2}, X}$, and $Y = {1}$. Then despite $tau$ being strictly coarser than $tau'$, $tau_Y = tau'_Y$.
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
