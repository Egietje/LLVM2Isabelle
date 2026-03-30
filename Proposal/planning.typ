#import "@preview/gantty:0.5.1": gantt
#import "functions.typ": fig

= Planning
<sec-planning>

Much of the minimum viable product has already been implemented without a clear planning.
The remaining work will be implemented according to the GANTT chart shown in @fig-planning.
Furthermore, it shows the extra features to be implemented on top of the MVP, along with rough estimates on how long they will take to complete and when they might be implemented.
In addition to that, it shows roughly when work on the tool itself will conclude, and the accumulated work and research will be gathered and written into the final thesis document.
The current aimed-for date to complete the thesis is the 19th of June, which can be extended if necessary.


== Risk Mitigation
<sec-risk-mitigation>

With any project, especially of the size of a thesis, risks are present that might endanger its feasibility and completion.
For the completion of this project, running out of time before implementing all proposed features is the biggest risk due to uncertain development time and complexity.
For this reason, a minimum viable product was defined (`SG1-4`) which represents the core goal of the research: creating a deductive verifier for a subset of LLVM-IR in Isabelle.
When this core goal is achieved, additional features (`EG1-4`) can be implemented that are not strictly necessary for the functionality of the tool, but do extend its usefulness.
Given that a large part of the MVP has already been implemented, there is only a low risk that it cannot be completed before the deadline.
The extension goals have been formulated in an open-ended way so their scope can scale to the time left for their implementation, or some can be left out entirely if others are deemed more important.
Currently, `EG2` and `EG3` are deemed most important for the usefulness of the final tool, so the initial time after completing `SG1-4` will be spent on them.

#fig(
  [#gantt(yaml("planning.yaml"))],
  [GANTT Chart of Project Planning]
)<fig-planning>

