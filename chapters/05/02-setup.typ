#import "../../macros.typ": *
#import "../../generated/setup.typ": *

== Experimental Setup <sec:results-setup>
This section outlines the hardware, toolchain versions, and measurement protocol used to evaluate performance. Ensuring a fixed and reproducible environment is essential for accurately comparing verification times. @tbl:results-setup details the pinned toolchain and the machine used for the evaluation.

Both verifiers are run single-threaded, and the reported time for each program is the minimum of three runs to account for system noise. Helium is invoked as a fresh process per file. Silicon is run via a warmed-up ViperServer instance over HTTP (`--numberOfParallelVerifiers 1`, `-Xss512m -Xmx4g`) to eliminate JVM startup overhead, with entity caching disabled, and its reported time is the server's own internal verification time.

#figure(
  caption: [The pinned toolchain and the machine used for evaluation.],
  {
    set par(justify: false)
    set text(size: 0.9em)
    grid(
      columns: 2,
      gutter: 4em,
      table(
        columns: (auto, auto),
        align: (left, left),
        stroke: none,
        table.hline(stroke: 1pt + luma(40%)),
        table.header([*Toolchain*], [*Version / Commit*]),
        table.hline(stroke: 0.5pt + luma(88%)),
        [Helium], raw("0147de4d6"),
        [Prusti], raw("f5d1a965c"),
        [Silicon / Silver], raw("26.08-RC"),
        [Z3], [4.15.1],
        table.hline(stroke: 1pt + luma(40%)),
      ),
      table(
        columns: (auto, auto),
        align: (left, left),
        stroke: none,
        table.hline(stroke: 1pt + luma(40%)),
        table.header([*Platform*], [*Details*]),
        table.hline(stroke: 0.5pt + luma(88%)),
        [CPU], [Intel Core i7-10750H],
        [Kernel], [Linux 6.13.1],
        [JDK], [OpenJDK 25.0.1],
        [Rust], [1.95.0-nightly],
        table.hline(stroke: 1pt + luma(40%)),
      )
    )
  },
) <tbl:results-setup>
