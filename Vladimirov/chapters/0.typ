#import "../preamble.typ": *
#show: preamble

= Chapter 0 -- Preliminaries
  1.
    Given a Boolean algebra $X$, prove the equivalence of the following propositions:
    #set enum(numbering: "(a)")
    1.
      $X$ is finite.
    2.
      $X$ is isomorphic to $2^Q$ for some finite $Q$.
    3.
      Every family of pairwise disjoint elements in $X$ is finite.
    4.
      Every quasimeasure on $X$ is totally additive.
    #sol[
      #clist([$("a") arrow.double ("b")$], [
        Let
          $ Q = {x in X mid(|) forall y in X, y < x arrow.double y = bb(0)} $
          and
          $
            Phi: 2^Q &arrow X \
              B &mapsto sup(B)
          $
        Clearly, $Phi bp(bb(0)) = emptyset$ and $Phi bp({q}) = q$ for $q in Q$, since $inf(Q) = bb(0)$ by construction. For $x in X$, let
          $
            B_x = {y in X mid(|) y < x}
          $
          and for $n in NN$, let
          $
            X_n = {x in X mid(|) abs(B_x) = n}
          $
        Suppose that for some $n in ZZ^+$, $X_n != emptyset$ and that
          $ union.big_(i = 1)^(n - 1) X_i subset.eq Phi(2^Q) $
        For each $x in X_n$ and $y in B_x$, $y < x$ and must therefore be in $X_i$ for some $i in {i}_(i = 0)^(n - 1)$, meaning that there is some $Q_y in Phi^(-1)({y})$, yielding
          $
            Phi(union.big_(y in B_x) Q_y) = or.big_(y in B_x) Phi(Q_y)
              = or.big B_x
              = x
          $
          since by construction $Phi(Q_y) = y$ and $sup(B_x) = x$. Since the fibre of every $q in Q$ is a singleton, this means that for each $x in X$, there is some subset of $Q$ with supremum $x$; that is, $Phi$ is surjective. Since $inf(Q) = bb(0)$, adding or removing any elements from a subset of $Q$ yields a different supremum, so $Phi$ is bijective.

        Let $U, V subset.eq Q$ with $U subset.eq V$. Then
          $
            Phi(U) = sup(U)
              <= sup(V)
              = Phi(V)
          $
        but if $U subset.eq.not V$, then
        $
          Phi(U) = sup(U)
            lt.eq.not sup(V)
            = Phi(V)
        $
        making $Phi$ an order isomorphism.
      ])
      #clist([$("b") arrow.double ("a")$], [
        $abs(X) <= 2^(abs(Q)) < aleph_0$.
      ])
      #clist([$("a") arrow.double ("c")$], [
        For each $Y subset.eq X$, $abs(Y) <= abs(X) <= aleph_0$.
      ])
      #clist([$("c") arrow.double ("d")$], [
        A quasimeasure is additive, and if there are no finite disjoint subsets, additivity and total additivity are equivalent.
      ])
      #clist([$"(d)" arrow.double ("c")$], [
        Let
          $
            psi: X &arrow [0, infinity] \
              x &mapsto 1
          $
        This is trivially additive and thus a quasimeasure, but if $X$ has any infinite disjoint subset $E$, $psi(E) = infinity$, violating total additivity, necessitating that $X$ lacks any such subset.
      ])
      #clist([$"(c)" arrow.double ("a")$], [
        Suppose that $X$ is infinite, and let ${x_n}_(n in NN) subset.eq X$. For $n in NN$, let
          $ y_n = x_n and and.big_(i = 0)^(n - 1) not x_i $
        Then for $m < n in NN$,
          $
            y_m and y_n = x_m and and.big_(i = 0)^(m - 1) not x_i and x_n and and.big_(i = 0)^(n - 1) not x_i
                = x_n and x_m and and.big_(i = 0)^(m - 1) x_i and not x_m and and.big_(i = m + 1)^(n - 1) not x_i
                = bb(0)
          $
          making ${y_n}_(n in NN)$ an infinite disjoint collection. #qed
      ])
    ]
