#import "@preview/ctheorems:1.1.3": *
#import "@preview/delimitizer:0.1.0"
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee"))
#let corollary = thmbox("corollary", "Corollary", fill: rgb("#eeffee"))
#let proof = thmproof("proof", "Proof").with(numbering: none)
#let sol = thmplain("solution", "Solution", rgb("#eeffee")).with(numbering: none)
#let qed = [
  #h(1fr) $square$ #parbreak()
]

#let preamble(doc) = [
  #set text(font: "New Computer Modern")
  #set par(justify: true)
  #set page(
    header: {
      context (
        if query(<no-header>).filter((s) => counter(page).at(s.location()) == counter(page).get()).len() == 0 {
          grid(
            // this grid fills the whole width of the header
            columns: (1fr, 1fr),
            // the left and right content are aligned correctly
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
            // under the first and only row, there's a line
            //,
            "",
            grid.hline(),
          )
        }
      )
    },
    footer: {
      context (
        if query(<no-header>).filter((s) => counter(page).at(s.location()) == counter(page).get()).len() == 0 {
          align(center, counter(page).display())
        }
      )
    },
    margin: 2cm
  )


  #show: thmrules.with(qed-symbol: $square$)
  #doc
]
