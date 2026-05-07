#import "../preamble.typ": *
#show: preamble
#align(center, [== 1 -- Type Theory])
1.
  Given functions $f: A arrow B$ and $g: B arrow C$, define their *composite* $g compose f: A arrow C$.
  Show that $compose$ is associative.
  #sol[
    The composition operation can be defined as
      $
        compose: product_(A, B, C: cal(U)) [(A arrow B) arrow (B arrow C) arrow (A &arrow C)] \
          g compose f(x) &:equiv g bp(f(x))
      $
    For $f: A arrow B$, $g: B arrow C$, and $h: C arrow D$,
      $
        h compose (g compose f)
          &equiv^(arrow.l^eta) lambda x. h compose (g compose f)(x)
            equiv lambda x. h bp(g compose f(x))
            equiv lambda x. h bp(g bp(f(x))) \
          &equiv lambda x. h compose g bp(f(x))
            equiv lambda x. (h compose g) compose f(x)
            equiv^(arrow^eta) (h compose g) compose f
      $
      #qed
  ]
2.
  Derive the recursion principles for products and dependent pairs using only projections.
  Verify the equalities
    $
      rec_(A times B)bp(C, f, (a, b)) &equiv f(a)(b) #h(3em) "and" #h(3em)
        rec_(sum_(x: A) B(x)) bp(C, f, (a, b)) = f(a)(b)
    $
  #sol[
    Let
      $
        rec_(A times B)
          &:equiv lambda (C: cal(U)). lambda (f: A arrow B arrow C). lambda (p: A times B). f bp(pi_1 (p)) bp(pi_2(p)) \
        rec_(sum_(x: A) B(x))
          &:equiv lambda (C: cal(U)). lambda (f: product_(x: A) [B(x) arrow C]). lambda (p: sum_(x: A) B(x)). f bp(pi_1 (p)) bp(pi_2 (p))
      $
    With this,
      $
        rec_(A times B) bp(C, f, (a, b))
          &equiv f bp(pi_1 bp((a, b))) bp(pi_2 bp((a, b)))
            equiv f(a)(b) \
        rec_(sum_(x: A) B(x)) bp(C, f, (a, b))
          &equiv f bp(pi_1 bp((a, b))) bp(pi_2 bp((a, b)))
            equiv f(a)(b)
      $

  ]
#colbreak()
3.
  Derive the induction principle for products using only projections and the propositonal uniqueness principle $uniq_(A times B)$, verifying that
    $
      ind_(A times B)bp(C, f, (a, b))
        equiv f(a)(b)
    $
  Generalize $uniq_(A times B)$ to $Sigma$-types.
  #sol[
    Let
      $
        D
          &:equiv lambda (C: A times B arrow cal(U)).  \
            &#h(2em) lambda (p: A times B) \
              &#h(3em) lambda (x: A times B). \
                &#h(4em) lambda (w: x =_(A times B) p). \
                  &#h(5em) C(x) \
          &: product_(C: A times B arrow cal(U)) product_(p: A times B) product_(x: A times B) [(x =_(A times B) p) arrow cal(U)]
      $
    For a family $C$ on $A times B$ and fixed $p: A times B$,
      $
        D bp(C, p) bp(bp(pi_1 (p), pi_2 (p)), uniq_(A times B) (p))
          &equiv C bp(bp(pi_1 (p), pi_2 (p)))  \
        D(C, p) bp(p, uniq_(A times B) (p))
          &equiv C(p)
      $
      so this provides a way of converting a family $C$ and $p$ into a dependent family compatible with the hypotheses of Based Path Induction, making
      $
        ind_(A times B)
          &:equiv lambda (C: A times B arrow cal(U)). #h(25em) \
            &#h(2em) lambda (f: product_(x: A) product_(y: B) C bp((x, y))).  \
              &#h(3em) lambda (p: A times B).  \
                &#h(4em) ind'_(=_(A times B))(
                  #flushr[(Based Path Induction on $=_(A times B)$ at $p$)]  \
                  &#h(5em) bp(pi_1 (p), pi_2 (p)), \
                  &#h(5em) D(C, p),
                    #flushr[$("dependent family on " product_(z: A times B) [p =_A z])$] \
                  &#h(5em) f bp(pi_1 (p))bp(pi_2 (p)),
                    #flushr[(result on equality)] \
                  &#h(5em) p, \
                  &#h(5em) uniq_(A times B) (p)
                    #flushr[($refl_p$, a witness to propositional equality)] \
                &#h(4em)) \
          &: product_(C: A times B arrow cal(U)) [product_(x: A) product_(y: B) [C bp((x, y))] arrow product_(p: A times B) C(p)]
      $
      well-typed with
      $
        ind_(A times B) bp(C, f, (a, b))
          &equiv f bp(pi_1 bp((a, b))) bp(pi_2 bp((a, b)))
            equiv f(a)(b)
      $
      as required.
    // TODO $Sigma$-types after chapter 2
  ]
#colbreak()
4.
  Given the _iterator_
    $
      sf("iter"): product_(C: cal(U)) [C arrow (C arrow C) arrow NN &arrow C] \
        sf("iter")(C, c_0, c_s, 0) &:equiv c_0 \
        sf("iter")bp(C, c_0, c_s, succt(n)) &:equiv c_s bp(sf("iter")(C, c_0, c_s, n))
    $
    derive a function with the same type as $rec_NN$;
      show that the defining equations of the recursor hold propositionally for this function, using the induction principle on $NN$.
    #sol[
      Let
        $
          D
            &:equiv lambda (C: cal(U)). \
              &#h(2em) lambda (c_0: C). \
                &#h(3em) lambda (c_s: NN arrow C arrow C). \
                  &#h(4em) lambda (n: NN) \
                    &#h(5em) #sf("iter")\( \
                      &#h(6em) NN times C, \
                      &#h(6em) (0, c_0), \
                      &#h(6em) lambda (p: NN times C). \
                        &#h(7em) bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), \
                      &#h(6em) n \
                    &#h(5em)\) \
            &: product_(C: cal(U)) [C arrow (NN arrow C arrow C) arrow NN arrow NN times C]
        $
        and let
        $
          rec_NN
            &:equiv lambda (C: cal(U)). lambda (c_0: C). lambda (c_s: NN arrow C arrow C). lambda (n: NN). pi_2 bp(D (C, c_0, c_s, n)) \
            &: product_(C: cal(U)) [C arrow (NN arrow C arrow C) arrow NN arrow C]
        $
      Then for $C: cal(U)$, $c_0: C$, $c_s: NN arrow C arrow C$, and $n: NN$,
        $
          rec_(NN) (C, c_0, c_s, 0)
            &equiv pi_2 bp(D(C, c_0, c_s, 0))
            &equiv pi_2 bp(sf("iter")bp(NN times C, (0, c_0), lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), 0)) \
            &equiv pi_2 bp((0, c_0))
              equiv c_0 \
        $
      Note that
        $
          pi_1 bp(D(C, c_0, c_s, 0)), c_s bp(pi_1 (p), pi_2 (p))), 0))
            equiv 0
              =_NN 0
        $
        and if $n: NN$ with $pi_1 bp(D(C, c_0, c_s, n)) =_NN n$, then
        $
          pi_1 bp(D bp(C, c_0, c_s, succt(n)))
            &equiv pi_1 bp(sf("iter")bp(NN times C, (0, c_0), lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), succt(n))) \
            &equiv pi_1 bp(bp(lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p)))) bp(  \
              &#h(2em) sf("iter")bp(NN times C, (0, c_0), lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), n))) \
            &equiv^(gets_eta) succt bp(pi_1 bp(sf("iter")bp(NN times C, (0, c_0), lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), n))) \
            &equiv succt(pi_1 bp(D(C, c_0, c_s, n)))
              =_NN succt(n)
        $
      #colbreak()
      The Induction Principle thusly gives that $pi_1 bp(D (C, c_0, c_s, n)) =_NN n$ holds for all $n: NN$, so
        $
          rec_(NN) bp(C, c_0, c_s, succt(n))
            &equiv pi_2 bp(D bp(C, c_0, c_s, succt(n))) \
            &equiv pi_2 bp(sf("iter")bp(NN times C, (0, c_0), lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), sf("succ")(n))) \
            &equiv pi_2 bp(bp(lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))))  \
              &#h(2em) sf("iter")bp(NN times C, (0, c_0), lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), n)) \
            &equiv^(gets_eta) bp(lambda p. c_s bp(pi_1 (p), pi_2 (p))bp( \
              &#h(3em)sf("iter")bp(NN times C, (0, c_0), lambda p. bp(succt bp(pi_1 (p)), c_s bp(pi_1 (p), pi_2 (p))), n))) \
            &=_NN c_s bp(n, rec_NN (C, c_0, c_s, n))
        $
        yielding the desired propositional equality. #qed
    ]
5.
  Show that defining $A + B :equiv sum_(x : sf(2)) rec_sf(2) (cal(U), A, B, x)$, where $inl(x) :equiv (0_sf(2), x)$ and $inr(y) :equiv (1_sf(2), y)$, yields a definition of $ind_(A + B)$ such that
    $
      ind_(A + B): product_(C: (A + B) arrow cal(U)) [product_(x: A) [C bp(inl(x))] arrow product_(y: B) [C bp(inr(y))] &arrow product_(z: A + B) C(z)] \
        ind_(A + B) bp(C, g_0, g_1, inl(x)) &equiv g_0 (x) \
        ind_(A + B) bp(C, g_0, g_1, inr(y)) &equiv g_1 (y)
    $
  #sol[
    For $C: (A + B) arrow cal(U)$, $g_0: product_(x: A) C bp(inl(x))$, $g_1: product_(y: B) C bp(inr(y))$, $g: product_(p: A + B) C(p)$ with $g bp(inl(x)) :equiv g_0 (x)$ and $g bp(inr(y)) :equiv g_1 (y)$, $x: A$, and $y: B$,
    $
      ind_(A + B) bp(C, g_0, g_1, inl(x))
        &equiv ind_(sum_(x: sf(2)) rec_2 (cal(U), A, B, x)) bp(C, g, (0_sf(2), x))
          equiv g(0_sf(2))(x)
          equiv g_0 (x) \
      ind_(A + B) bp(C, g_0, g_1, inl(y))
        &equiv ind_(sum_(x: sf(2)) rec_2 (cal(U), A, B, x)) bp(C, g, (1_sf(2), y))
          equiv g(1_sf(2))(y)
          equiv g_1 (y)
    $
    #qed
  ]
6.
  Show that defining $A times B :equiv product_(x: sf(2)) rec_sf(2)(cal(U), A, B, x)$ yields a definition of $ind_(A times B)$ such that
    $
      ind_(A times B): product_(C: (A times B) arrow cal(U)) [product_(x: A) product_(y: B) [C bp((x, y))] &arrow product_(z: A times B) C(z)] \
      ind_(A times B) bp(C, f, (x, y)) &=_(C bp((x, y))) f(x)(y)
    $
  //  TODO after §2.7
7.
  Give a derivation of $ind'_(=_A)$ from $ind_(=_A)$ without using universes.
  // TODO eventually
#colbreak()
8.
  Define multiplication and exponentiation on $NN$ using $rec_NN$. Verify that $(NN, +, 0, times, 1)$ is a semiring using only $ind_NN$.
  #sol[
    Let
      $
        sf("mul") &:equiv rec_NN bp(NN arrow NN, lambda (n: NN). 0, lambda (m : NN). lambda (g: NN arrow NN). lambda (n: NN), n + g(n)) \
        sf("exp") &:equiv rec_NN bp(NN arrow NN, lambda (n: NN). 1, lambda (m: NN). lambda (g: NN arrow NN). lambda (n: NN). n dot g(n))
      $
      with the notation $m dot n :equiv sf("mul")(m, n)$ and $m^n :equiv sf("exp")(n, m)$. Then
      $
        m^0
          &equiv (lambda n. 1)(m)
            equiv 1 \
        m^(succt(n))
          &equiv bp(lambda m. lambda g. lambda n. n dot g(n))bp(n, sf("exp")(n), m)
            equiv n dot m^n
      $
      and
      $
        0 dot n
          &equiv (lambda n. 0)(n)
            equiv 0 \
        succt(m) dot n
          &equiv bp(lambda m. lambda g. lambda n. n + g(n))bp(m, sf("mul")(m), n)
            = m + (m dot n)
      $
      so these behave as expected.

    The axioms for a semiring $(A, +, 0_A, dot, 1_A)$ are given in predicate logic are proven inductively as follows:
    #set enum(numbering: "(1)")
    1. $forall a: NN, 0 + a = 0 + a = n$. <1.8.1>
      -
        $0 + 0 = 0 + 0 = 0$ by the definition of the recursor.
      -
        If $0 + a = a + 0 = a$, then
          $
            0 + succt(a)
              &= succt(a) #flushr[(by definition)] \
              &= succt(a + 0) #flushr[(by hypothesis)] \
              &= succt(a) + 0 #flushr[(by definition)] \
          $
    2. $forall a, b, c: NN, a + (b + c) = (a + b) + c$. <1.8.2>
      -
        For $b, c: NN$
        $
          0 + (b + c)
            &= b + c #flushr[(by #link(<1.8.1>)[(1)])] \
            &= (0 + b) + c #flushr[(by #link(<1.8.1>)[(1)])] \
        $
      -
        If $a + (b + c) = (a + b) + c$ for all $a, b: NN$, then
          $
            succt(a) + (b + c)
              &= succt bp(a + (b + c)) #flushr[(by definition)] \
              &= succt bp((a + b) + c #flushr[(by hypothesis)]) \
              &= succt(a + b) + c #flushr[(by definition)] \
              &= bp(succt(a) + b) + c #flushr[(by definition)] \
          $
    3. $forall a, b: NN, a + b = b + a$.
      - $forall b: NN, 1 + b = b + 1$. <1.8.3.a>
        -
          If $1 + b = b + 1$, then
            $
              1 + succt(b)
                &= 1 + (1 + b) #flushr[(by definition)] \
                  &= 1 + (b + 1) #flushr[(by hypothesis)] \
                  &= (1 + b) + 1 #flushr[(by #link(<1.8.2>)[(2)])]] \
                  &= succt(b) + 1 #flushr[(by definition)] \
            $
      -
        If $a + b = b + a$ for all $b: NN$, then
        $
          succt(a) + b
            &= (1 + a) + b #flushr[(by definition)] \
            &= 1 + (a + b) #flushr[(by #link(<1.8.2>)[(2)])] \
            &= 1 + (b + a) #flushr[(by hypothesis)] \
            &= (b + a) + 1 #flushr[(by #link(<1.8.3.a>)[base])] \
            &= b + (a + 1) #flushr[(by #link(<1.8.2>)[(2)])] \
            &= b + (1 + a) #flushr[(by #link(<1.8.3.a>)[base])] \
            &= b + succt(a) #flushr[(by definition)]
        $
    4. $forall a: NN$, $1 dot a = a dot 1 = a$. <1.8.4>
      #clist(markers: ([(4')], []), [
        1. $forall a: NN, 0 dot a = a dot 0 = 0$. <1.8.4.a>
          -
            By definition, $0 dot 0 = 0$.
          -
            If $0 dot a = a dot 0 = 0$, then
              $
                0 dot succt(a)
                  &= 0 + (0 dot a) #flushr[(by #link(<1.8.1>)[(1)])] \
                  &= 0 + 0 #flushr[(by definition)] \
                  &= 0 #flushr[(by #link(<1.8.1>)[(1)])] \
                  &= succt(a) dot 0 #flushr[(by definition)] \
              $
        -
          $1 dot 0 = 0 = 0 dot 1$ by #link(<1.8.4.a>)[(4')]
        -
          If $1 dot a = a dot 1 = a$, then
            $
              1 dot succt(a)
                &= 1 + (1 dot a) #flushr[(by definition)] \
                &= 1 + a #flushr[(by base)] \
                &= succt(a) #flushr[(by definition)]
            $
      ])
    5. $forall a, b, c: NN, a dot (b + c) = (a dot b) + (a dot c)$.
    -
      $
        a dot (0 + c)
          equiv a dot c
          equiv 0 + (a dot c)
          equiv 0 +
      $
    -
      If $a dot (b + c) equiv $
    - $forall a, b, c: NN$, $a dot (b dot c) = (a dot b) dot c$.
      -
        $
          (a dot 0) dot c
            &= 0 dot c
              = 0
              = a dot 0
              = a dot (0 dot c)
        $
      -
        If $(a dot b) dot c = a dot (b dot c)$ for all $a, c: NN$, then
          $

          $
    - $forall a, b, c: NN, (a + b) dot c = (a dot c) + (b dot c)$.
    - $forall a, b: NN$, $a dot b = b dot a$.
      - $0 dot b = 0 = b dot 0$.
      -
        If $a dot b = b dot a$, then
          $
            succt(a) dot b =
          $

  ]
9.
  Define the type family $sf("Fin"): NN arrow cal(U)$ of finite sets and the dependent function $sf("fmax"): product_(n: NN) sf("Fin")(n + 1)$ that returns the largest element of each nonempty finite type.
10.
  Show that the _Ackermann function_ $sf("ack"): NN arrow NN arrow NN$, which satisfies
    $
      sf("ack")(0, n) &equiv succt(n) \
      sf("ack")bp(succt(m), 0) &equiv sf("ack")(m, 1) \
      sf("ack")bp(succt(m), succt(n)) &equiv sf("ack")bp(m, sf("ack")bp(succt(m), n))
    $
    is definable using only $rec_NN$.
11.
  Show that for $A: cal(U)$, $not not not A arrow not A$ is inhabited.
12.
  Using the propositions-as-types interpretation, derive the following tautologies:
  #set enum(numbering: "(i)")
  1.
    $A arrow.r.double (B arrow.r.double A)$.
    #sol[
      Consider $bp(lambda (a: A). lambda (b: B). a): A arrow B arrow A$. #qed
    ]
  2.
    $A arrow.r.double not not A$.
    #sol[
      $not not A equiv (not A) arrow sf(0) equiv (A arrow sf(0)) arrow sf(0)$, so consider
        $
          bp(lambda (a: A). lambda (f: A arrow 0). f(a)): A arrow (A arrow sf(0)) arrow sf(0)
        $
        #qed
    ]
  3.
    $(not A or not B) arrow.r.double not(A and B)$.
13.
  Using propositions-as-types, derive $not not (P or not P)$.
14.
  Why is the function
    $
      f: product_(x: A) product_(p: x =_A x) &[p =_A refl_x] \
        f(x, refl_x) &:equiv refl_(refl_x)
    $
    not definable using the induction principles for identity types?
15.
  Show that the Indiscernability of Identicals follows from Path Induction.
16.
  Show that addition is commutative on $NN$.
