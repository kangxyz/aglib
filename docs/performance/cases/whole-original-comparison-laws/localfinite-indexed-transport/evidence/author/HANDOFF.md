# Integrated transport consumer on the original Ext comparison

This is the one coherent lower/native candidate requested after the actual
ordinary transport failures. It changes the exposed construction boundary;
it does not claim a diagnosed kernel cause or a performance improvement.

The accepted input pair is Values b62f08cb and native 655b2ec9. The fixed
uncompiled output pair is:

```text
e1d0a92737405aec68ed643078b79eaf9bcbbab736d82ea9aa429caed14a133d  OriginalComparisonValues.lean
0997517ed89eba60a57505a6665d1fc722afec046cf6afaa726ff8e4462d6988  LocalFiniteComparison.lean
```

The preliminary lower hash e3d6b658 is superseded only by removal of two duplicate
blank lines before this fixed handback. No run used that preliminary hash.

## The complete generic consumer

The added theorem
`Adjunction.originalExtSourceComparison_bijective_of_transport_values` retains
the existing four abelian categories, four independent HasExt worlds, original
exact adjunctions, original source isomorphisms and original pullback families.
It has its own indexed source inputs:

```text
K : I → C₀ ⥤ C₃,  h : i = j
c₀ : K i ≅ G ⋙ L',  d₁ : K j ≅ L ⋙ H
s : ∀ k, U₃ ⟶ (K k).obj U₀
hleft  : s i ≫ c₀.hom.app U₀ = e'.inv ≫ L'.map sG
hright : s j ≫ d₁.hom.app U₀ = sH ≫ H.map e.inv.
```

Only the selected `K i` needs the same additivity/exactness requirements as the
old selected composite `L₀`. There is no exactness assumption on every K, no new
category realization and no additional Ext world.

Inside this generic theorem, equality induction on h gives

```text
ht : s i ≫ (eqToIso (congrArg K h) ≪≫ d₁).hom.app U₀ =
       sH ≫ H.map e.inv.
```

At h = rfl, this is hright after `eqToIso_refl` and `Iso.refl_trans`. The theorem
immediately passes ht to the unchanged
`originalExtSourceComparison_bijective_of_mate_values`, with

```text
L₀ = K i,
c = c₀,
d = eqToIso (congrArg K h) ≪≫ d₁,
s₀ = s i.
```

That existing factory constructs the same original comparisons E/E', derives
the original mate square and returns bijectivity of the supplied original pH.
The new theorem has no old `L₀`, d or transported-ht input. The section's old
`include hs ht in` commands are local to their earlier declarations and do not
apply to this theorem. Its source premises are hleft and hright above.

The whole mate input uses precisely
`(c₀.symm ≪≫ eqToIso (congrArg K h) ≪≫ d₁).hom`. The old native hMate is its
same defining equality after unfolding the local d. No wanted cohomology square,
reference equivalence or transported source equation is assumed.

## The native instance

The native file keeps the original whole-map definition helper, hSquare, hMate,
hs, finite-component invertibility and all original comparison values. It
retains the inferred original input

```lean
have hSourceComp := inverseImageComp_constant_inv f g' A
```

and removes the native `have ht`. The new factory receives

```text
K(k) = inverseImage k,  h = h.w.symm,
c₀ = inverseImageComp g f',  d₁ = inverseImageComp f g',
s(k) = ((inverseImageConstantIso k).app A).inv,
hleft = hs,  hright = hSourceComp.
```

The whole pG/pH families are still the literal original `cohomologyPullback g`
and `cohomologyPullback g'`, identified by the same existing whole defining
equalities. The final native output is directly the original `pH F q`.

The transported concrete Eq is neither a native theorem statement nor a named
native proof input. Its derivation and conversion into the consumer's source
slot are completed before Scheme, constant-sheaf, F and degree substitution.
This is the distinction from both failed standalone source-transport wrappers.

A named `sourceTransportComposite` value or defining Prop was considered but is
not added: its conversion back into the old consumer could reproduce the same
native expanded equality. The integrated consumer already performs that
conversion in the generic context, so it is the smaller complete implementation.

## Preserved scope and retirement

All three public native theorem headers, their four independent HasExt inputs,
arbitrary abelian coefficient F, all natural degrees, original maps and the two
corollary bodies are byte-preserved. `HasExt.standard` stays after the first
generic theorem. No geometry, torsion, dimension, exactness or size premise was
added to a public header.

The five earlier Values declarations are byte-preserved. The old
`Functor.sourceInverse_composite_transport` declaration is removed because its
only current consumer is the replaced native ht. The primary supplied the exact
sole-use graph over N/Aglib: one declaration, one native use, and Values imported
only by this native module. No completed outside consumer is reopened. The
stable `OriginalComparison` and `SourceSection` sources are unchanged.

No source code was written to N or P, and no Git, options, budgets, pins, guards
or axiom settings were changed. All edits are in the assigned continuation
scratch directory. No run was launched by this worker.

## Evidence boundary and next action

- Normal P34 formation passed in 7f2c. That did not prove P.
- Native 655b failed in C4e0c2743 while generic b62f passed.
- The exact current ordinary proof fe592 failed normally in f94 on SOURCEa690,
  without HasExt/F/q.
- The smaller literal ordinary proof 86fe failed normally in e2d8b8ce on the same
  SOURCEa690 at its native theorem. Shrinking that proof telescope alone did not
  fix the exposed native equation. No emitted generic error is not a claim of
  a separately checked generic certificate.
- Neither old ordinary result is evidence for this new integrated candidate.

The remaining obligation is the primary's ordinary incremental compile-and-repair
of this fixed two-module candidate on its retained coherent providers. There is
no additional standalone formation or cancellation-helper gate. The primary owns
integration, lane collision coordination, CPP and delivery of any actual native
pass to the downstream broker. No native closure or performance result is claimed
by this staged source handback.
