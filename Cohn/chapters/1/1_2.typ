#import "../../preamble.typ": *
#show: preamble
== 1.2 -- Measures
1.
  Let $mu$ be a finite measure on $(X, scr(A))$.
  #set enum(numbering: "(a)")
  1.
    Show that for $A, B in scr(A)$,
      $
        mu(A union B) = mu(A) + mu(B) - mu(A inter B)
      $
    #sol[
      $A without B = A without (A inter B) subset.eq A$ and $B$ are disjoint, so
        $
          mu(A union B) = mu bp(A without (A inter B)) + mu(B)
            = mu(A) + mu(B) - mu(A inter B)
        $
        #qed
    ]
  2.
    Show that for $A, B, C in scr(A)$,
      $
        mu(A union B union C) = mu(A) + mu(B) + mu(C) - mu(A inter B) - mu(A inter C) - mu(B inter C) + mu(A inter B inter C)
      $
    #sol[
      $
        mu(A union B union C) &= mu(A union B) + mu(C) - mu(bp(A union B) inter C) \
          &= mu(A) + mu(B) - mu(A inter B) + mu(C) - mu bp((A inter C) union (B inter C)) \
          &= mu(A) + mu(B) + mu(C) - mu(A inter B) - bp(mu(A inter C) + mu(B inter C) - mu(A inter B inter C)) \
          &= mu(A) + mu(B) + mu(C) - mu(A inter B) - mu(A inter C) - mu(B inter C) + mu(A inter B inter C)
      $
      #qed
    ]
  3.
    Find and prove a corresponding formula for ${A_k}_(k = 1)^n subset.eq scr(A)$.
    #sol[
      Suppose that for some $n in NN$,
        $
          mu(union.big_(k = 1)^n A_k) = sum_(ell = 1)^n (-1)^(ell + 1) sum_(S in binom(n, ell)) mu(inter.big_(j in S) A_j)
        $
        for all ${A_k}_(k = 1)^n subset.eq scr(S)$. Then for ${A_k}_(k = 1)^(n + 1)$
        $
          mu(union.big_(k = 1)^(n + 1) A_k) &= mu(union.big_(k = 1)^n A_k union A_(n + 1))
              = mu(union.big_(k = 1)^n A_k) + mu(A_(n + 1)) - mu(union.big_(k = 1)^n A_k inter A_(n + 1)) \
              &= sum_(ell = 1)^n (-1)^(ell + 1) sum_(S in binom(n, ell)) mu(inter.big_(j in S) A_j) + mu(A_(n + 1)) - mu(union.big_(k = 1)^n [A_k inter A_(n + 1)]) \
              &= sum_(ell = 1)^n (-1)^(ell + 1) sum_(S in binom(n, ell)) mu(inter.big_(j in S) A_j) + mu(A_(n + 1)) - sum_(ell = 1)^n (-1)^(ell + 1) sum_(S in binom(n, ell)) mu(inter.big_(j in S) [A_j inter A_(n + 1)]) \
              &= sum_(ell = 1)^n (-1)^(ell + 1) sum_(S in binom(n, ell)) [mu(inter.big_(j in S) A_j) - mu(inter.big_(j in S) [A_j inter A_(n + 1)])] + mu(A_(n + 1)) \
              &= sum_(ell = 1)^(n + 1) (-1)^(ell + 1) sum_(S in binom(n + 1, ell)) mu(inter.big_(j in S) A_j)
        $
      The last line is justified by the fact that choosing $ell$ of $n$ elements and then taking the intersection with $A_(n + 1)$ is the same as choosing $ell + 1$ elements to begin with from $n + 1$ instead where one is forced to be $n + 1$. This interseection is done for every size of subset, so it can be simply included by allowing $n + 1$ to be chosen at any point. #qed
    ]
2.
  Show that
    $
      mu: scr(B)(RR) &arrow [0, infinity] \
        A &mapsto cases(
          abs(A inter QQ) quad& abs(A inter QQ) < aleph_0 ,
          infinity & abs(A inter QQ) >= aleph_0
        )
    $
    is a $sigma$-finite Borel measure on $RR$ under which each open interval has infinite measure.
    #sol[
      Let $a < b in RR$, and by the density of $QQ$ in $RR$, let $c < d in (a, b)$. Then since $QQ$ is closed under addition,
        $
          (a, b) supset (c, d) in.rev {c + frac(d - c, n)}_(n = 2)^infinity
        $
        so $mu bp((a, b)) = infinity$. Furthermore,
        $
          RR = (RR without QQ) union union.big_(q in QQ) {q}
        $
        is a countable union of sets with measure 0 and 1, making $mu$ $sigma$-finite. #qed
    ]
3.
  Find a decreasing sequence $(A_n)_(n in NN) in cal(P)(NN)^NN$ with
    $
      \#(inter.big_(n in NN) A_n) != lim_(n arrow infinity) \#(A_n)
    $
  #sol[
    For $n in NN$, let
    $
      A_n = NN without union.big_(m = 2)^(n + 2) m NN
    $
    Then the intersection of all $A_n$ is ${1}$, since $0 in 2NN$ and for any $k in ZZ_(>= 2)$, $k in k NN$ implies that $k in.not A_k$. For any given $n in NN$, though, $\#(A_n) = aleph_0$ by the infinitude of primes.
  ]

4.
  Let $(X, cal(A))$ be a measurable space.
  #set enum(numbering: "(a)")
  1.
    Let #label("1.2.4.a") $mu: cal(A) arrow [0, infinity]$ be countably additive. Show that if $mu(A)$ is finite for some $A in cal(A)$, then $mu(emptyset) = 0$, making $mu$ a measure.
    #sol[
      For all $n in NN$,
        $
          mu(A) = mu(A union.sq union.sq.big_(k = 0)^n emptyset) = mu(A) + (n + 1)mu(emptyset)
        $
      For this to be finite, it must be the case that $mu(emptyset) = 0$. #qed
    ]
  2.
    Show by example that a nonnegative function may be countably additive without being a measure.
    #sol[
      Consider
        $
          nu: cal(A) &arrow [0, infinity] \
            A &mapsto infinity
        $
      This is trivially countably additive, yet $mu(emptyset) = infinity != 0$. #qed
    ]
5.
  Let $(X, cal(A))$ be a measurable space and let $x, y in X$. Show that $delta_x = delta_y$ precisely when for all $A in cal(A)$, $x in A$ if and only if $y in A$.
  #sol[
    Suppose that $delta_x = delta_y$, and let $A in cal(A)$. Then $x in A$ if and only if $delta_y (A) = delta_x (A) = 1$, which is true if and only if $y in A$ as well. #qed
  ]
6.
  Let $(mu_n)_(n in NN)$ be a sequence of measures measurable space $(X, cal(A))$.
  #set enum(numbering: "(a)")
  1.
    Show #label("1.2.6.a") that if $(m_n)_(n in NN)$ is increasing, then
      $
        mu: cal(A) &arrow RR \
          A &mapsto lim_(n arrow infinity) mu_n (A)
      $
      is a measure.
    #sol[
      For pairwise disjoint ${A_n}_(n in NN) subset.eq cal(A)$,
        $
          mu(union.big.sq_(n in NN) A_n)
            &= lim_(k arrow infinity) mu_k (union.big.sq_(n in NN) A_n)
              = lim_(k arrow infinity) sum_(n in NN) mu_k (A_n) \
            &<= lim_(k arrow infinity) sum_(n in NN) mu (A_n) = sum_(n in NN) mu(A_n)
        $
      For all $N in NN$,
        $
          sum_(n = 0)^N mu(A_n)
            = sum_(n = 0)^N lim_(k arrow infinity) mu_k (A_n)
              = lim_(k arrow infinity) sum_(n = 0)^N mu_k (A_n)
              <= lim_(k arrow infinity) sum_(n in NN) mu_k (A_n)
              = mu(union.sq.big_(n in NN) A_n)
        $
        so
        $
          sum_(n in NN) mu(A_n) <= mu(union.sq.big_(n in NN) A_n )
        $
        making them equal by antisymmetry. Furthermore,
        $
          mu(emptyset)
            = lim_(n arrow infinity) mu_k(emptyset)
              = lim_(n arrow infinity) 0
              = 0
        $
        making $mu$ a measure by #link(label("1.2.4.a"))[4(a)]. #qed
    ]
  2.
    Show that
      $
        mu: cal(A) &arrow RR \
          A &mapsto sum_(n in NN) mu_n (A)
      $
      is a measure.
    #sol[
      For all $N in NN$ and pairwise disjoint ${A_n}_(n in NN) subset.eq cal(A)$,
        $
          sum_(k = 0)^N mu_k (union.sq.big_(n in NN) A_n)
            = sum_(k = 0)^N sum_(n in NN) mu_k (A_n)
              = sum_(n in NN) sum_(k = 0)^N mu_k (A_n)
        $
        and
        $
          sum_(k = 0)^N mu_k (emptyset)
            = sum_(k = 0)^N 0
              = 0
        $
        making the sequence of partial sums an increasing sequence of measures by #link(label("1.2.4.a"))[4(a)] and $mu$ a measure by #link(label("1.2.6.a"))[(a)]. #qed
    ]
7.
  Let $(x_n)_(n in NN) in RR^NN$ and consider the Borel measure
    $
      mu = sum_(n in NN) delta_(x_n)
    $
  #set enum(numbering: "(a)")
  1.
    Show that $mu$ maps bounded intervals to finite values if and only if #h(1fr)
      $
        lim_(n arrow infinity) abs(x_n) = infinity
      $
    #sol[
      If $abs(x_n) arrow infinity$, then for all $R > 0$, there is some $N in NN$ such that $abs(x_n) > R$ for all $n in ZZ_(>= N)$, so
        $
          mu bp((-R, R))
            = sum_(n in NN) delta_(x_n) bp((-R, R))
              < N
              < infinity
        $
        meaning that $mu$ maps bounded intervals to finite values.

      Suppose conversely that there is some $R > 0$ with $mu bp((-R, R)) = infinity$. Then there are infinitely many terms $x_n$ with $abs(x_n) < R$, so for all $M > R$ and $N in NN$, there is some $n in ZZ_(>= N)$ with $abs(x_n) < M$; that is, $abs(x_n) arrow.not infinity$. #qed
    ]
  2.
    Determine what sequences $(x_n)_(n in NN) in RR^NN$ make $mu$ $sigma$-finite.
    #sol[
      If no value is repeated infinitely many times in the sequence, then
        $ RR
            = (RR without {x_n}_(n in NN)) union.sq {x_n}_(n in NN)
        $
        making $mu$ $sigma$-finite. Otherwise, any Borel set containing the infinitely-repeated value will have infinite measure, and $mu$ will not be $sigma$-finite.
    ]
8.
  Let $(X, cal(A), mu)$ be a measure space and let
    $
      mu^bullet: cal(A) &arrow [0, infinity] \
        A &mapsto sup{mu(B) mid(|) B in cal(P)(A) inter cal(A) "and" mu(B) < infinity}
    $
  #set enum(numbering: "(a)")
  1.
    Show that $mu^bullet$ is a measure on $(X, cal(A))$.
    #sol[
      Trivially,
        $
          mu^bullet (emptyset)
            = sup{mu(B) mid(|) B in cal(P)(emptyset) inter cal(A) "and" mu(B) < infinity}
              = sup{mu(emptyset)}
              = 0
        $
      For pairwise disjoint ${A_n}_(n in NN) in cal(A)$,
        $
          mu^bullet (union.sq.big_(n in NN) A_n)
            &= sup{mu(B) mid(|) B in cal(P)(union.sq.big_(n in NN) A_n) inter cal(A) "and" mu(B) < infinity} \
            &= sup{mu(union.sq.big_(n in NN) B_n) mid(|) forall n in NN, B_n in cal(P)(A_n) inter cal(A) "and" mu(union.sq.big_(n in NN) B_n) < infinity} \
            &= sup{sum_(n in NN) mu(B_n) mid(|) forall n in NN, B_n in cal(P)(A_n) inter cal(A) "and" sum_(n in NN) mu(B_n) < infinity} \
            &<= sup{sum_(n in NN) mu(B_n) mid(|) forall n in NN, B_n in cal(P) (A_n) inter cal(A) "and" mu(B_n) < infinity} \
            &<= sum_(n in NN) sup{mu(B_n) mid(|) B_n in cal(P)(A_n) inter cal(A) "and" mu(B_n) < infinity}
              = sum_(n in NN) mu^bullet (A_n)
        $
      Let $epsilon > 0$ and for $n in NN$, let $B_n in cal(P)(A_n) inter cal(A)$ such that $mu(B_n) >= mu^bullet (A_n) - 2^(-n - 1)epsilon$. If any $B_n$ has infinite measure, then clearly $mu^bullet (union.sq.big_(n in NN) A_n) = infinity$ as well, so suppose that each $mu(B_n)$ is finite. Then
        $
          sum_(n in NN) mu^bullet (A_n)
            <= sum_(n in NN) [mu(B_n) - 2^(-n - 1)epsilon]
              = sum_(n in NN) mu(B_n) - epsilon
              = mu(union.sq.big_(n in NN) B_n) - epsilon
              <= mu^bullet (union.big_(n in NN) A_n)
        $
        making $mu^bullet$ additive by reflexivity and thus a measure by #link(label("1.2.4.a"))[4(a)]. #qed
    ]
  2.
    Show that if $mu$ is $sigma$-finite, then $mu^bullet = mu$.
    #sol[
      Let ${A_n}_(n in NN) subset.eq cal(A)$ be a partition of $X$ with each $mu(A_n) < infinity$, and let $B in cal(A)$. Then
        $
          mu^bullet (B)
            &= mu^bullet (union.sq.big_(n in NN) [B inter A_n])
              = sum_(n in NN) mu^bullet (B inter A_n)
              = sum_(n in NN) mu(B)
        $
        since each $mu(B inter A_n) < mu(A_n) < infinity$ by subadditivity. #qed
    ]
  3.
    Find $mu^bullet$ if $X$ is nonempty and
      $
        mu(A)
          = cases(
            0 quad& A = emptyset,
            infinity quad& A != emptyset
          )
      $
    #sol[
      For $A in cal(A) without emptyset$,
        $
          mu^bullet (A)
            &= sup{mu(B) mid(|) B in cal(P)(A) inter cal(A) "and" mu(B) < infinity} \
            &= sup{mu(B) mid(|) B in cal(P)(A) inter cal(A) "and" mu(B) = 0}
              = 0
        $
    ]
9.
  Let $mu$ be a measure on $(X, cal(A))$ and let $(A_n)_(n in NN) in cal(A)^NN$ with $sum_(n in NN) mu(A_n) < infinity$. Show that
    $
      B = {x in X mid(|) abs({n in NN mid(|) x in A_n}) = aleph_0}
    $
    has measure zero.
  #sol[

  ]
