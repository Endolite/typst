#import "../../preamble.typ": *
#show: preamble
#align(center + horizon, text(16pt)[= Part I -- Basic Set Theory]) <part>
  #toc(true)
  #for n in (1,) {
    include(str(n) + ".typ")
  }
