#import "./preamble.typ": *
#show: preamble
#set document(title: "Set Theory — Jech")
#align(center + horizon, [#text(20pt)[Set Theory -- Jech] \ \ Selected Exercise Solutions by Arnav Patri]) <root>
  #toc(false)
  #include("notation.typ")
  #for n in (1,) {
    include("parts/p" + str(n) +"/p" + str(n) + ".typ")
  }
