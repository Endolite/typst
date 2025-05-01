#import "../../preamble.typ": *

#show: preamble

#align(center + horizon, text(14pt)[== Chapter 2 -- Topological Spaces and Continuous Functions]) <chapter>
  #toc(true)
  #for n in (13, 16, 17, 18, 19) {
    include str(n) + ".typ"
  }
