


Line numbers are from the Latex file.

56
"semantics of PR-Nat in Agda"
The capitalization is different here, "PR-Nat" instead of "PR-NAT".
Is that intentional?

64
"Finally, we extend PR-FO with exponentials to PR-HO"
add a verb like "form", "create", or "define"
"Finally, we extend PR-FO with exponentials to define PR-HO"

66
"obsolete as it derivable in a bicartesian closed category"
missing "is"
"obsolete as it is derivable in a bicartesian closed category"

77
"All definitions, results, and proofs are mechanized using Agda [?]"
broken citation

119
Using σ for successor is a bit unusual. I caught myself getting confused
later in the paper regarding the meaning of σ.

208
PR-FO syntax also differs from PR-NAT in switching from n-ary
functions to unary functions. Perhaps that is worth commenting on?

226
Where is ⇐ defined? Ahh, looking at the agda code I see that it is
single substitution. Perhaps that syntax should be introduced in
section 3.1?

298
Why is the recursion "eval (P h)" 
inside
"fmap G (λ v → eval (P h) ...)"
ok?

The other recursion "eval h ..." of course is just structural recursion,
so that is obviously ok.

408
Say that function types are interpretated as Agda's function type.

448
Remark that "theta" is the uncurry operation.

479
"which allows the definition of primitive recursive"
change "allows" to "enables"
"which enables the definition of primitive recursive"

481
"The embedding of PR-NAT in PR-FO"
change "in" to "into"
"The embedding of PR-NAT into PR-FO"

