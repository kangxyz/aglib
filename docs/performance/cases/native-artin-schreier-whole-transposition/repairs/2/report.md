# AS coefficient universe-binder repair 2

The closed run `remote-46f990d7142a45009bf5d38b0a93e41e` rejected the two alias declarations because their explicit universe parameter lists redeclared ambient `w,r,v,u`. This repair changes only those aliases to fresh declaration-local `w′,r′,v′,u′`, keeping fully typed C/R parameters and the explicit lift/ring/Hom/object application order. Existing calls at `.{w}` keep their exact original lift world.

The alias bodies remain precisely the same original native additive-lift functor and native Sheaf pair with the same supplied proof. All map/proof bodies, independent worlds, native values/unit and both fixed wrappers are unchanged. No flag, suppression, model, record, hypothesis or source placeholder is introduced. The unknown-alias, kernel-metavariable and generated-sorry diagnostics belonged to the rejected-declaration input; they are not relabelled as mathematical gaps.

Exact failed input, repaired output, delta and closed-run provenance are preserved here. Initial reviewed R3 and repair 1 remain fixed. Only the granted lower native file was changed, with HEAD/status/hash guards; other ten owned native paths are held. No compiler/probe, Git/index, registry, README or network mutation was performed by this author.

READY/HOLD for the root's immediate retry of only the same lower leaf and two changed wrappers plus necessary dependencies. This repaired hash remains uncompiled, and no untouched AS consumer is a build target.
