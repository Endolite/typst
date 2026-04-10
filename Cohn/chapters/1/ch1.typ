#import "../../preamble.typ": *
#show: preamble

#align(center + horizon, text(14pt)[== Chapter 1 -- Measures]) <chapter>
  #toc(true)
  #for n in range(1, 3) {
    include "1_" + str(n) + ".typ"
  }
