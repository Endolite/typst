#import "@preview/ctheorems:1.1.3": * // Proofs

// Proofs
  #let sol(text) = [
    #parbreak() _Solution:_ #text \
  ]
  #let qed = [
    #h(1fr) $square$ #parbreak()
  ]


// Utilities
  #let bp(math) = (
    $lr((math), size: #115%)$
  )
  #let circ = [
    $degree #h(-2mm)$
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
  #let scr(it) = text(
    features: ("ss01",),
    box($cal(it)$),
  )
  #let toc(sub) = [
    #context (
      if query(<toc>).len() == 0 or counter(page).at(query(<toc>).first().location()) == counter(page).get() {
        [#outline(target: if sub {selector(heading).after(heading, inclusive: false)} else {selector(heading)}) <toc>]
      }
    )
  ]

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
                  level: 3
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

  #show: thmrules.with(qed-symbol: $square$)
  #show math.equation: set text(features: ("cv01",))
  #doc
]
