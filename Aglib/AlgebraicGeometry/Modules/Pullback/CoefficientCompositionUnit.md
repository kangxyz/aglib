# Composed coefficient-unit values

`pullback_coefficient_comp_unit_app_top` evaluates the complete original
coefficient composite along an arbitrary commutative scheme triangle.
It takes arbitrary schemes, their original maps p, q, r and h : r = q ≫ p,
arbitrary coefficients E, F, G and original arrows a : p*E → F and b : q*F → G.
The result derives the two successive unit values; it assumes no desired
coefficient square, quasicoherence, flatness or finiteness.

The sole import is UnitValues, whose existing equality, composition and
naturality equations supply the proof. No new adjunction or mate backend is
introduced. AffineSheafCompositionUnit is the native affine consumer.

Current source `5d3ff3eb` passed its whole native check, own215: 7.1 s leaf,
10.865 s total, exit 0, no aggregate guard, owned process group gone. This
accepts this generic law only, not its affine supplier or composition consumer,
and establishes no remedy for their kernel-memory failures.

## First native check and accepted explicit value application

The original 2196 source reached an ordinary rewrite error in own214: the
first equality/composition unit rewrites succeeded, but reverse naturality
rewriting failed at the displayed original nested unit values. The log also
reported an implicit-transparency carrier check failure for that rewrite;
it does not identify a kernel-memory cause.

The accepted repair instantiates the existing naturality value law with the
same q, a and original p-unit section, then applies the same b.app top by
congruence to its symmetric equality. Statement, imports, actions and options
are unchanged. The subsequent affine supplier `9819c679` failed its kernel
check in own216; composition source `ab608ceb` was not run under the pass gate.
