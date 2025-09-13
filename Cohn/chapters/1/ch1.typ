#import "../../preamble.typ": *
#show: preamble

#align(center + horizon, text(14pt)[== Chapter 1 -- Measures]) <chapter>
  #toc(true)
  #for n in (1, ) {
    include "1_" + str(n) + ".typ"
  }
