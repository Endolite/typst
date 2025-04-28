#import "../preamble.typ": *

#show: preamble

#align(center + horizon, text(16pt)[= Part I -- General Topology]) <part>
  #toc(true)
  #for n in (2,) {
    include str(n) + "/ch" + str(n) + ".typ"
  }
