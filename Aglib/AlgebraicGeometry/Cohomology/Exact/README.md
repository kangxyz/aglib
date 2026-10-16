# Long exactness and low-degree Euler consequences

[Modules](Modules.lean) gives the native long exact sequence over any
specified structural ring map `α : R →+* Γ(X, ⊤)`.
`moduleCohomologyConnectingOfHom` is the original additive `Sheaf.H.δ`,
linear for the existing structural scalar actions. The three adjacent
exactness statements retain `moduleCohomologyMapOfHom`; naturality is with
respect to an actual morphism of short exact module-sheaf sequences.
`moduleH0MapOfHom_injective` applies to every coefficient monomorphism.
These results require no quasicoherence, flatness or finiteness.

[LongExact](LongExact.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact`, retains `Scheme.Cohomology.moduleCohomologyConnecting` and the existing field-linear APIs as specializations of [Modules](Modules.lean). Its underlying map is literally native `Sheaf.H.δ`. `moduleCohomologyMap_exact` and the connecting exactness results concern the original coefficient maps and actual short exact module-sheaf sequence. `moduleH0Map_injective` handles an arbitrary coefficient monomorphism; `moduleH0Map_injective_of_shortExact` is the distinct short-exact specialization. No finite-dimensional premise belongs to generic exactness.

[Euler](Euler.lean) gives low-degree dimension consequences. `moduleEuler_of_shortExact` uses finite H0/H1 of the first and middle sheaves, finite H0 of the quotient and zero H1 of the quotient; then `dim H0 - dim H1` of the middle is that of the first plus quotient H0 dimension. The quotient formula retains finite middle H0/H1, finite quotient H0 and quotient H1 vanishing.

`moduleEuler_of_finiteClosedSupport` specializes to a quotient with actual zero stalks outside finitely many distinct closed points, finite-dimensional structural-field stalks there, and finite H0/H1 of the first sheaf. The extra term is the sum of those stalk dimensions. No properness, genus or unconditional curve product formula is asserted.

[Finite extension/transfer](../Finiteness/ExactSequences.lean) is owned separately by Finiteness; [finite support](../Support/README.md) supplies its actual cohomology comparisons. The source conditions and universe-`u+1` original objects are preserved.
