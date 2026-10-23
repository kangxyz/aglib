# Torsion sheaves on a site

This family develops internal torsion for abelian sheaves on an arbitrary
Grothendieck site. Torsion is local and sectionwise: each original section is
annihilated on a covering sieve by some positive integer, which may vary with
the section and the cover. No single global annihilator is assumed.

| Source | Reusable construction |
| --- | --- |
| [Basic](Basic.lean), [points](Points.lean), [sheaves](Sheaf.lean) | Local torsion sieves, coefficient naturality, and the equivalence with torsion in a chosen small conservative family of original point fibres. |
| [Annihilators](Annihilator/Basic.lean) and [section comparison](Annihilator.lean) | The native kernel subsheaf of multiplication by `n`, its literal inclusion, and its original section-level kernel comparison. |
| [Factorial diagram](Annihilator/Diagram.lean) and [colimit](Colimit.lean) | The positive stages killed by `(n+1)!` and the actual filtered-colimit presentation, with the original inclusions and coefficient naturality. |
| [Devissage](Devissage.lean) | The native short exact annihilator/quotient sequence and the stated bounded-torsion prime-devissage property theorem. Its property theorem retains its zero-object, prime-killed, and short-exact-extension hypotheses. |
| [Property reduction](Reduction.lean) | An isomorphism-invariant property of abelian sheaves reduces from internally torsion to prime-annihilated objects, assuming it contains zero objects and is stable under actual short-exact extensions and the displayed `ℕ`-colimits. The module-coefficient form uses prime `ZMod p` sheaves and retains `[UnivLE.{max u v, w}]`. |
| [ZMod modules](ZMod/Basic.lean) | Conversion of a sheaf killed by the literal scalar identity into a genuine `ZMod n`-module sheaf while retaining its original sections, restriction maps, coefficient arrows, and underlying-sheaf isomorphism. |
| [ZMod injectives](ZMod/Injectives.lean) | Genuine `ZMod n`-valued sheaves on the standard-sized site have enough injectives and `HasExt`, for every `n`, including zero. This is a result in the module-valued sheaf category. |

For torsion sheaves, the factorial annihilator stages present the original sheaf
as a filtered colimit through the actual kernel inclusions. The result is an
objectwise torsion presentation; it does not assert cohomological continuity,
constructible finite cogenerators, a local criterion, or proper base change.

The `ZMod` conversion includes `n = 0`, with the canonical native `Int` module
structure. Its generic site statement uses the displayed `HasSheafCompose`
premise; native preservation supplies it under `UnivLE.{max u v, w}`, including
the standard coefficient universe. In that genuine module-valued sheaf category,
[ZMod injectives](ZMod/Injectives.lean) supplies enough injectives and `HasExt`
in the standard universe for every modulus, including zero. This does not
identify it with ringed sheaves of modules or assert that a module-sheaf
injective is injective after forgetting to abelian sheaves; no Ext or cohomology
comparison is included.


## Native validation

The admitted fifteen-source C4 family passed its scoped native checks. In the
initial thirteen-source batch, cached compilation was fully reused, generated
entries and text style passed, and the pinned 208-declaration audit found only
the standard three foundations. Its declaration-lint pass reported ten
repairable findings. After the prescribed name and simp-attribute repairs,
`remote-a10c066b1f364e5ea36b41f84ff0077c` compiled with nine frontends and passed
all fifteen declaration linters; the compatible entries and audit results were
retained.

The two additional leaves passed build, entries, style, lint, and their
149-declaration audit in `remote-28b1b2a7ebbb4443991dddd079742bb7`; that audit
overlaps the original 208-declaration scope. After narrowing `Reduction.lean`
to import its actual `ZMod.Sheaf` provider,
`remote-4d07168b428f4dfe8e0c1a922af9da8d` passed its incremental build, style,
and declaration lint. Final source guards passed in
`run-35d42ec65a584c4f92730591ee49208c` across 4,778 production modules and 399
positive checks. This validation does not establish cohomological continuity,
a local criterion, or proper base change.
