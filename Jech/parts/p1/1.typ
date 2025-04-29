#import "../../preamble.typ": *
#show: preamble
== Chapter 1 -- Axioms of Set Theory
  Prove the following statements.
  1.
    $(a, b) = (c, d)$ if and only if $a = c$ and $b = d$.
    #sol[
      If $(a, b) = (c, d)$, then
        $
          (a, b) = {{a}, {a, b}} = {{c}, {c, d}} = (c, d)
        $
        so ${a} in {{c}, {c, d}}$. By the Axiom of Extensionality, either $a = c$ or $a = c = d$. By the same token, either $b = d$ or $b = c = d$.

      The reverse implication is trivial. #qed
    ]
  2.
    There is no set $X$ with $cal(P)(X) subset.eq X$.
    #sol[
      Suppose that $cal(P)(X) subset.eq X$. Then $X in cal(P)(X) subset.eq X$, violating the Axiom of Regularity. #qed
    ]
  3.
    Let
      $
        NN = inter.big {X mid(|) X "is inductive"}
      $
      be the smallest inductive set, and let $0 = emptyset in NN$, and for $n in NN$, let $n + 1 = n union {n}$. Let
      $
        "<" = {(m, n) in NN times NN mid(|) m in n}
      $
    $T$ is _transitive_ when $x in T$ implies that $x subset.eq T$.

    If $X$ is inductive, then
      $ Y = {x in X mid(|) x subset.eq X} $
      is also inductive. This shows that $NN$ is transitive and that for each $n in NN$, $n = {m in NN mid(|) m < n}$.
    #sol[
      Since $X$ is inductive, $emptyset in X$, and $emptyset subset.eq cal(P)(X)$ vacuously, so $emptyset in Y$. If $x in Y$, then $x in X$, so $x union {x} in X$ by induction, and since $x, {x} in cal(P)(X)$, $x union {x} in cal(P)(X)$ as well, meaning that $x union {x} in Y$, making $Y$ inductive. #qed
    ]
  4.
    If #label("1.4") $X$ is inductive, then
      $ Y = {x in X mid(|) x "is transitive"} $
      is inductive. This implies that each $n in NN$ is itself transitive.
    #sol[
      Since $X$ is inductive, $emptyset in X$, and since $emptyset$ is vacuously transitive, $emptyset in Y$. If $x in Y$, then for each $y in x$, $y subset.eq x subset.eq x union {x}$, and by induction, $x union {x} in X$. Furthermore, $x in x union {x}$ as well, meaning that for each $y in x union {x}$, $y subset.eq x union {x}$; that is, $x union {x}$ is transitive, making $Y$ inductive. #qed
    ]
  5.
    If $X$ is inductive, then
      $ Y = {x in X mid(|) x in.not x "is transitive"} $
      is inductive. This proves that for $n in NN$, $n in.not n$, so $n != n + 1$.
    #sol[
      Since $X$ is inductive, $emptyset in X$, and since there are definitionally no elements within $emptyset$, it is vacuously transitive and in $Y$. If $x in Y$, then by #link(label("1.4"))[4.], $x union {x}$ is inductive. Suppose that $x union {x} in x union {x}$. Then either $x union {x} in x$, in which case $x union {x} subset.eq x$ by transitivity, which means that $x in x$, a contradiction; or $x union {x} in {x}$, in which case $x union {x} = x$, so $x in x$, another contradiction. It must therefore be the case that $x union {x} in.not x union {x}$; that is, that $x union {x} in Y$, making $Y$ transitive. #qed
    ]
  6.
    If $X$ is inductive, then
      $ Y = {x in X mid(|) x "is transitive and every" emptyset != z subset.eq x "has an" in #h(0mm)"-minimal element" } $
      is inductive.
    #sol[
      Since $X$ is inductive, $emptyset in X$, so vacuously, $emptyset in Y$. Let $x in Y$ and let $emptyset != z subset.eq x union {x}$. If $z subset.eq x$, then it has an $in$-minimal element, since $x in Y$, so assume that $z subset.eq.not x$; that is, that $x in z$. Then $z' = z without {x} subset.eq x$, so it has some $in$-minimal $t in z'$. If this $t$ is not $in$-minimal in $z$, then it must be the case that $x in t$, so by transitivity, $t subset.eq x$, meaning that $x in x$,
    ]
  7. Every $emptyset != X subset.eq NN$ has an $in$-minimal element.
