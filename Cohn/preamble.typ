// Packages
  #import "@preview/cetz:0.3.4"
  #import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
  #import "@preview/physica:0.9.5": *

// Proofs
  #let sol(text) = [
    #parbreak() _Solution_: #text \
  ]
  #let qed = [
    #h(1fr) $square$ #parbreak()
  ]


// Utilities
  #let bp(math) = (
    $lr((math), size: #115%)$
  )
  #let bpp(math) = (
    $lr(math, size: #115%)$
  )
  #let circ = [
    $degree #h(-2mm)$
  ]
  #let clist(m, body) = [
    #list(
      marker: m,
      body
    )
  ]
  #let dfrac(num, dem) = [
    #math.display(math.frac(num, dem))
  ]
  #let ev(math) = (
    $lr(angle.l math angle.r)$
  )
  #let ldots = $#h(0cm) dots$
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
  #let scr(it) = text(
    features: ("ss01",),
    box($cal(it)$)
  )
  #let cal(it) = math.class("normal", box({
    show math.equation: set text(font: "Garamond-Math", stylistic-set: 3)
    $#math.cal(it)$
  }) + h(0pt))
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

  #let wp = $℘$

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
                  level: 1
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
  #set math.vec(delim: "[")
  #doc
]
