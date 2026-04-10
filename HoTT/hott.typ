#import "./preamble.typ": *
#show: preamble
#set document(title: "Set Theory — Jech")
#align(center + horizon, [#text(20pt)[Homotopy Type Theory] \ \ Selected Exercise Solutions by Arnav Patri]) <root>
  #toc(false)
  // #include("notation.typ")
  #for n in (1,) {
    include("chapters/c" + str(n) + ".typ")
  }
