# One provisional map-equality transport candidate

This is R-only preparation pending the corrected CLOSED diagnostic. N3 and the fixed probe/request remain unchanged. It is neither a selected production repair nor a pass.

The exact existing private lemma at AssociatedBundle498–504 is moved verbatim, preserving its AssociatedBundle namespace, before the generic section-family helper. The candidate replaces eager `change` by a named, fully typed hview at the actual rawPresheaf/pullHom endpoints, and finishes by `hview.trans hrestrict`. The original ChartRelations/self-unit simplification remains inside hrestrict.

The bridge is literal: rawPresheaf X M is `(Etale.forget X).op ⋙ lineBundles.presheafHom M (unitObject X)`. At f:U→V in the opposite étale site, its map is the same native presheafHom map along `((Etale.forget X).map f.unop).op`. The original lemma applies with S=X, M=M, N=unitObject X, arrow=f.unop and g=c⟨U.unop,s⟩. Only the existing functor-composition/opposite-map layer needs definitional normalization; no new map, module category, raw frame, cover or global frame is introduced. F, M₁, M₂ and both source structure arrows are pinned in the two equations.

No desired naturality is assumed: the first equality is the existing rfl lemma; the second is still proved from actual hr and hu. Whether this avoids the measured bottleneck is pending the corrected profiler result. The terminated trust-override run56a9 and zero-frontend setupb85 are not correct-settings probe evidence.
