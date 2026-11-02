/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Tactic.Algebraize

/-!
# Detecting original stalk vanishing by flat pullback

These two general proofs are extracted unchanged from
`Modules/Coherent/Support/FinitePushforward`. They concern arbitrary module
sheaves, with their original additive and module-valued stalks. A flat local
stalk map is faithfully flat, so vanishing of the actual pulled-back sheaf
forces vanishing of the original stalk at the image point. No coherence,
finiteness, Noetherianity, or small-model choice is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The original module and additive stalks detect the same zero object. -/
lemma moduleStalk_zero_iff {X : Scheme.{u}} (M : X.Modules) (x : X) :
    IsZero ((moduleStalk X x).obj M) ↔ IsZero ((stalkFunctor X x).obj M) := by
  rw [ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  rfl

/-- Vanishing after the actual flat pullback forces the original stalk at
every image point to vanish, by the original faithfully flat local stalk map. -/
theorem stalk_isZero_of_flat_pullback {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (M : X.Modules) (hM : IsZero ((Scheme.Modules.pullback f).obj M)) (z : Z) :
    IsZero ((stalkFunctor X (f z)).obj M) := by
  let φ : X.presheaf.stalk (f z) →+* Z.presheaf.stalk z := (f.stalkMap z).hom
  have hφ : φ.FaithfullyFlat := by
    change (f.stalkMap z).hom.FaithfullyFlat
    algebraize [(f.stalkMap z).hom]
    exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f z) (f.toLRSHom.prop z)
  have := ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hφ
  let N := (moduleStalk X (f z)).obj M
  have hz := (moduleStalk Z z).map_isZero hM
  have ht : IsZero ((ModuleCat.extendScalars φ).obj N) :=
    hz.of_iso ((pullbackModuleStalkIso f z).app M).symm
  have : IsIso ((ModuleCat.extendScalars φ).map (0 : N ⟶ N)) := ht.isIso ht _
  have : IsIso (0 : N ⟶ N) := isIso_of_reflects_iso _ (ModuleCat.extendScalars φ)
  exact (moduleStalk_zero_iff M (f z)).mp
    ((isIsoZero_iff_source_target_isZero N N).mp inferInstance).1

end AlgebraicGeometry.Scheme.Modules
