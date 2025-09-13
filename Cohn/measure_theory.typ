#import "../../preamble.typ": *
#show: preamble

#align(center + horizon, [#text(20pt)[Measure Theory -- Cohn \ \ Selected Exercise Solutions by Arnav Patri]]) <root>
  #toc(false)
  #include "notation.typ"
  #for n in (1, ) {
    include "chapters/" + str(n) + "ch" + str(n) + ".typ"
  }
