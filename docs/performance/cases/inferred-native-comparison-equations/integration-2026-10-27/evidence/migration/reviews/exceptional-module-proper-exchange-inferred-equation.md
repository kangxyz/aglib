# R4 inferred component equation: independent ordinary review

**Accepted on the identified native mathematical and source-correspondence scope.** No mathematical gap was found in the fixed two-file change. Current thin-R4 integration remains pending. This is not an established-status verdict.

| Fixed source | SHA-256 |
| --- | --- |
| `Exceptional/Derived/ProperBaseChange.lean` | `7f7ddd67dbab5b61f062332dc01e99b4d6c4a9c8d6531a465ab08f554bddf9f4` |
| `Adjunction/Mates/UnitIsomorphism.lean` | `f2b0fba00d9c04af59cebfd655491a9af2084e0c9baf437e25ec48883efb9933` |

Native HEAD is `54d6974ace11bf7d197aa925cb8cade86db8a24f`, Lean `4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Both fixed afterimages and their supplied beforeimages match. All fifteen dependency hashes itemized by the prior accepted R4 review still match; the new report preserves that old review read-only at its actual `4eaeb3d9…` basis. The archive baseline remains `f71393b9…`.

**CT#isIso_of_component_equation — accepted.** For a functor `F:C→D`, original arrow `β:M→N`, and actual equation `u ≫ a ≫ v = s ≫ F.map β ≫ t`, with all five displayed arrows `a,u,v,s,t` invertible and `F` reflecting isomorphisms, `β` is invertible. The proof first obtains invertibility of the right composite from the left composite, cancels the invertible `s` and `t` using the native composition lemmas, then reflects only invertibility through `F`. It uses two categories and the actual morphisms; no faithfulness, equality reflection, exactness, adjunction or new comparison record is required.

**R4#properModuleDerivedBaseChange_isIso_of_torsion_homology — accepted.** For arbitrary `Ring Λ : Type (u+1)`, the original Cartesian square `sq : IsPullback g′ f′ f g` with `f` proper, four independently supplied module-derived realizations, and the given `K : D+(ModuleSheaf X Λ)` whose native homology is internally torsion in every integer degree, the literal original component `(moduleDerivedBaseChangeMap Λ f f′ g g′ sq.w.symm).app K` is an isomorphism.

The source obtains `hcube` directly by the unannotated `have hcube := moduleDerivedBaseChangeMap_underlying ... K`. It passes that exact inferred equation to the complete generic helper. There is no manual restatement/conversion of a native equation and no independent cube-equation premise in R4. The implicit middle abelian arrow is inferred from the producer itself. The actual specialization is:

| Helper input | Original selected morphism |
| --- | --- |
| `F` | `moduleDerivedUnderlying Λ S′` |
| `β` | the stated module exchange at `K` |
| `a` | the original abelian exchange at `(moduleDerivedUnderlying Λ X).obj K` |
| `u` | `derivedInverseImage g` applied to the direct-image underlying comparison at `K` |
| `v` | `derivedDirectImage f′` applied to the inverse inverse-image underlying comparison for `g′` at `K` |
| `s` | the inverse inverse-image underlying comparison for `g` at `moduleDerivedDirectImage Λ f K` |
| `t` | the direct-image underlying comparison for `f′` at `moduleDerivedInverseImage Λ g′ K` |

All endpoints agree with the original `HorizontalMateCubeEquation`. Its six transformations are the native comparisons and the two original exchange maps. The unchanged producer proves that equation from the actual coefficient-level comparison cube, exact-source comparisons and mate pasting; it assumes neither proper base change nor exchange invertibility.

The original `moduleTorsionCohomologyPlus_iff_underlying` transfers exactly `hK` to that same underlying `K`, by the actual exact-forgetting homology isomorphism. The original abelian proper-base-change theorem therefore proves invertibility of `a` at that object. Each other edge is a component of the actual native natural isomorphism or its functor image. The original conservative right-derived underlying functor then reflects the resulting invertibility of `F.map β`. There is no uniform annihilator, upper cohomology bound, dimension bound or additional geometric condition.

The direct-image underlying comparison retains its original relative acyclicity proof: underlying module injectives have the required represented Ext vanishing and hence higher direct-image acyclicity. It does not assert that forgetting scalars preserves injectivity. The conservative derived-functor proof uses exactness, the original homology comparison and original homology detection; equality is not reflected through forgetting.

**R4#selected-data-and-local-dictionary — accepted.** The four module `HasDerivedCategory` inputs remain public and independent; they specify the actual `K`, its homology and the conclusion's map. The four respective auxiliary abelian categories each receive one standard realization only inside the public proof. No auxiliary abelian realization escapes its statement, and no alternate-model equivalence or endpoint identification is constructed.

The added local attribute selects the existing theorem `abWEqualsLocallyBijectiveStandard`, whose result is a `Prop`-valued class. It changes only that proof argument to the same native `SheafOfModules` abelian constructor. At fixed topology and coefficient category, those proofs are definitionally proof-irrelevant; the supplied sheafification, ring, underlying category and derived localization data are unchanged. This argument does **not** treat `Abelian` itself as a proposition: its constructor has data, and it remains the same constructor with the same non-proof inputs. `HasDerivedCategory` is genuine localization data; the source neither reselects nor transports the four module instances.

**G0#isIso_map_unit_of_iso_mate — unchanged source coverage retained.** The existing framework unit theorem's statement and entire proof are byte-identical. The new generic helper's binders and proof are identical to the complete helper in the frozen `5d7d253d…` Scheme file after only the privacy/name change. The final R4 public declaration and proof are byte-identical to the prior accepted `4eaeb3d9…` public declaration/proof. The changed private argument, actual inferred equation, all comparison inputs and local proof dictionary were reviewed here; relocation is not inferred merely from the author's correspondence claim.

The identical R4 interface and reviewed same-map conclusion permit retention of prior unchanged R8/U2/U4 uses after the principal checks their source/application correspondence. This report adds no blanket coverage of those consumers' other arguments, changed bytes, imports or runtime.

The full fixed two-file derivations and nontrivial prose were read, together with the complete frozen `5d7d` argument, original archive proof, actual changed native applications and the local-dictionary foundations. The ordinary abelian proper-base-change family is an identified accepted prerequisite at its actual torsion-homology interface; no full-family or global-library re-audit is claimed. The JSON records exact supplier identities and the reused versus newly inspected scope.

Execution evidence is separate. The supplied closed frozen-context diagnostic `remote-2e13005a9ced49f9957f5f02c7754e8a` passed the complete `5d7d253d…` source in 6.536 seconds, at provider `65bc75bd…`, setup `922034a0…`, default budgets and no input drift. Its controlled phase source is `71aa2228…`; it is not a current-N pass for thin `7f7ddd67…`. The framework `f2b0fba0…` has its own inspected source-matching current-N closed pass `remote-274bb8825e4046c88f4f9d65569bd948`, source `c9814ed3…`, exit zero and no drift. That run compiled only the framework target, not R4 or its P6 consumers.

No mathematical or source-correspondence gap remains for this fixed change. The actual current-N thin R4 and affected consumer chain still await their assigned integration through current imports; no success is inferred from either retained run. No compiler, tests, lint, axiom audit, replay or client check was started. Read-only Git guards confirmed the fixed sources and pins. Only these two new review reports were written; old reports, source files and other contributors' work remain unchanged.
