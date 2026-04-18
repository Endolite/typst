#import "./preamble.typ": *
#show: preamble
#set document(title: "Homotopy Type Theory")
#align(center + horizon, [#text(20pt)[Homotopy Type Theory \ _Univalent Foundations of Mathematics_] \ \ Selected Exercise Solutions by Arnav Patri]) <root>
  #toc(false)
  #include("notation.typ")
  #for n in (1,) {
    include("chapters/c" + str(n) + ".typ")
  }
