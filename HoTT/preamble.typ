// Packages
  #import "@preview/cetz:0.3.4" // diagrams
  #import "@preview/intextual:0.1.1": * // equation tags
  #import "@preview/physica:0.9.5": * // differentials

// Proofs
  #let sol(text, label: [_Solution_]) = [
    #parbreak() #label: #text \
  ]
  #let qed = [
    #h(1fr) $square$ #parbreak()
  ]


// Utilities
  #let bp(..args) = {
    let body = args.pos().join[$,$]
    $lr((body), size: #115%)$
  }
  #let bpp(math) = (
    $lr(math, size: #115%)$
  )
  #let cal(it) = math.class("normal", context {
    show math.equation: set text(font: "Garamond-Math", stylistic-set: 3)

    let scaling = 100% * (1em.to-absolute() / text.size)
    let wrapper = if scaling < 60% { math.sscript }
                  else if scaling < 100% { math.script }
                  else { it => it }
    box(text(top-edge: "bounds", $wrapper(math.cal(it))$))
  })

  #let clist(body, markers: ($arrow.double$, $arrow.double.l$)) = {
    set enum(numbering: n => markers.at(calc.rem-euclid(n - 1, markers.len())))
    body
  }

  #let dfrac(num, dem) = [
    #math.display(math.frac(num, dem))
  ]

  #let outlink(lab, display) = [
    #context {
      let matches = query(lab)
      if matches.len() == 0 {
        [#display]
      } else {
        link(matches.first().location())[#display]
      }
    }
  ]

  #let rm = math.upright

  #let sf(it) = text(font: (
    "CMU Sans Serif"
  ), it)

  #let sp(math) = $lr((#math), size: #85%)$
  #let spp(math) = $lr(#math, size: #85%)$

  #let toc(sub) = [
    #context (
      if query(<toc>).len() == 0 or counter(page).at(query(<toc>).first().location()) == counter(page).get() {
        [#pagebreak() #outline(target: if sub {selector(heading).after(heading, inclusive: false)} else {selector(heading)}) <toc> #pagebreak()]
      }
    )
  ]

  #let vb(text) = {
    math.bold(rm(text))
  }

// Symbols
  #let circ = [
    $degree #h(-2mm)$
  ]
  #let ev(..args) = {
    let body = args.pos().join[$,$]
    $lr(chevron.l body chevron.r)$
  }
    #let sev(..args) = $spp(ev(args))$
  #let gets = math.arrow.l
  #let ind = math.op(sf("ind"))
  #let inl = math.op(sf("inl"))
  #let inr = math.op(sf("inr"))
  #let ldots = $#h(0cm) dots$
  #let rec = math.op(sf("rec"))
  #let refl = math.op(sf("refl"))
  #let snorm(text) = $spp(norm(#text))$
  #let span = math.op("span", limits: true)
  #let succt = math.op(sf("succ"))
  #let tsp = $sans(upright(T))$
  #let uniq = math.op(sf("uniq"))
  #let TT = $bb(T)$

// Preamble
#let preamble(doc) = [
  #set text(font: "New Computer Modern", size: 11pt)
  #set par(justify: true)
  #set page(
    header: {
      context (
        if (query(<root>), query(<part>), query(<chapter>)).flatten().filter((s) => counter(page).at(s.location()) == counter(page).get()).len() == 0 {
          grid(
            columns: (1fr, 1fr),
            align: (left, right),
            context {
              let sections = query(
                heading.where(
                  level: 2
                )
              ).filter((s) => counter(page).at(s.location()) <= counter(page).get())
              if sections.len() == 0 {
                ""
              } else {
                sections.last().body
              }
            },
            [Arnav Patri],
            "",
            grid.hline(),
          )
        }
      )
    },
    footer: {
      context (
        if (query(<root>), query(<part>), query(<chapter>)).flatten().filter((s) => counter(page).at(s.location()) == counter(page).get()).len() == 0 {
          align(center, counter(page).display())
        }
      )
    },
    margin: 1.5cm
  )

  #show math.equation: set text(features: ("cv01",))
  #set math.mat(delim: "[")
  #show: intertext-rule
  #show math.eq: math.scripts
  #show math.arrow: math.scripts
  #show math.arrow.l: math.scripts

  #doc
]
