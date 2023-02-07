Comments on PrimRec

Line numbers are from the Latex file.

111
in addition to citing Kleene, possibly mention him in the
text. Did he originate primitive recursion?

114-115
citation needed for Knuth's uparrow and Conway's arrow

116
"System T" --> "Godel's System T"
and cite Godel's paper in addition to the one cited

124
"generalise to functions over words, ..." -->
"generalises from natural numbers to words, ..."

130
It's not clear whether PR1-IND is an existing concept
or a new one. You cite two papers, but say both are
"subtly different" from PR1-IND. (Are they also subtly
different from each other, or identical?) Can you cite
any paper that defines something exactly equivalent to
PR1-IND? Or can you explain how it differs from these
other papers, and why the different concept is the
more interesting one?

158
"Finally, we extend PR1-IND with exponentials to PR-IND"
--> "Finally, we extend PR1-IND with exponentials to yield PR-IND"
or "we add exponentials to PR1-IND to yield PR-IND"
(I'm slightly concerned readers may mix up PR1-IND and
PR-IND. I wonder if PR-FO and PR-HO would be better names?)

160
"surprising to the authors who are not category theorists"
I'd drop this. The result is in no way surprising---it is
a folk theorem. What is surprising is that no one has written
down the simple elementary proof before!

169
Am I correct in thinking that not only are all the proofs in the
paper in Agda, but also the paper itself is a literate Agda script?
You need to make that point explicit in the introduction. Also
warn the reader that they may need to know Agda to read the paper,
and perhaps point them at a textbook or two if they want to brush
up on Agda to read the paper.

169
By the end of the introduction, it's still not clear what is the
contribution of the paper. Is this all well-known, but this is a new
presentation? If so, what is new about the presentation and why is it
better than the others? You half-imply that what is new and better is
the application of category theory. Has no one has written these
definitions out categorically before? I'm pretty sure I've seen
categorical descriptions of PR-NAT, but I'm less sure about PR1-IND
and PR-IND. If categorical description of PR1-IND and PR-IND are new,
say so explicitly. But I suspect that there are categorical
descriptions out there already---you should cite them if so. Perhaps
what is new is that you give an elementary description accessible to
those with no knowledge of category theory.  Again, if that is so,
say it explicitly. If you had to give a bullet-point list of
contributions, what would it be?

If the contribution of the paper is a new presentation rather then new
theory, then perhaps it is best sold as a pearl? FSCD doesn't have a
pearl category for submission, but ICFP does.

177
"The set of primitive recursive functions is the smallest family PR of functions"
-->
"The set of primitive recursive functions PR is the smallest family of functions"

177
When I first read the definition, it looked (grammatically) like you
were stating that PR contained certain basic functions and that the
statement "PR is closed" was a property that followed from the
definition rather than part of the definition. One way to fix this
is to change: "PR is closed" to "and is closed".

224
"In programming languages terminology, primitive recursive functions
are given by a domain-specific language where a sentence of the
language specifies a total function of type ${ℕ}^n \to {ℕ}$ in a
pointfree style." I find this sentence confusing. The definition that
appears before this statement is *not* pointfree. Did you mean to
refer to the next definition? --> "We will sharpen up the definition
by applying standard programming languages techniques, presenting
PR-IND as a a domain-specific language where a sentence of the
language specifies a total function of type ${ℕ}^n \to {ℕ}$ in a
pointfree style." Add a sentence to clarify why using pointfree makes
the definition better/simpler/easier to read/whatever.


239
PRNAT
I'm not sure why you write `zero`, `suc zero`, `suc (suc n)` and so on in
the code. Wouldn't `0`, `1`, `2+n` be clearer? If you make the change,
explain why we use `2+n` rather than `n+2`.

In the file, there is also a combinator F that is not in the paper.
I presume the source files are being made available in case someone wants
to read the whole proof. In that case, either delete F or explain why
it is in the file but not the paper.




