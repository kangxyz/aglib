/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteRepresentedRestriction
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-! Restriction to a surjective etale chart detects actual sheaf isomorphisms. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u
variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] [Surjective f]

theorem coversTop_surjectiveEtale :
    (Scheme.smallEtaleTopology X).CoversTop (fun _ : Unit => Scheme.Etale.mk f) := by
  intro U
  change Sieve.ofObjects (fun _ : Unit => Scheme.Etale.mk f) U ∈
    X.smallGrothendieckTopology @Etale U
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  obtain ⟨s, hs⟩ := f.surjective (U.hom x)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback s x hs
  let V : X.Etale := Scheme.Etale.mk (pullback.snd f U.hom ≫ U.hom)
  let a : V ⟶ U := MorphismProperty.Over.homMk (pullback.snd f U.hom) rfl (by trivial)
  let b : V ⟶ Scheme.Etale.mk f :=
    MorphismProperty.Over.homMk (pullback.fst f U.hom) pullback.condition (by trivial)
  exact ⟨V, a, z, ⟨(), ⟨b⟩⟩, inferInstance, hz₂⟩

theorem isIso_of_setEtaleRestriction_map {F G : Scheme.EtaleH1.SetSheaf X} (m : F ⟶ G)
    [IsIso ((Scheme.EtaleH1.setEtaleRestriction f).map m)] : IsIso m := by
  apply Sheaf.isIso_of_coversTop (coversTop_surjectiveEtale f)
  intro i
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  let V : S.Etale := Scheme.Etale.mk W.unop.hom.left
  let e : (Scheme.EtaleH1.siteEtalePostcompose f).obj V ≅ W.unop.left :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      simpa [V] using (MorphismProperty.Over.w W.unop.hom).symm)
  have hm : IsIso (m.hom.app (op ((Scheme.EtaleH1.siteEtalePostcompose f).obj V))) :=
    (NatTrans.isIso_iff_isIso_app ((Scheme.EtaleH1.setEtaleRestriction f).map m).hom).1
      inferInstance (op V)
  change IsIso (m.hom.app (op W.unop.left))
  have h : IsIso (F.obj.map e.hom.op ≫ m.hom.app (op ((Scheme.EtaleH1.siteEtalePostcompose f).obj
    V))) :=
    inferInstance
  rw [m.hom.naturality] at h
  exact IsIso.of_isIso_comp_right (m.hom.app (op W.unop.left)) (G.obj.map e.hom.op)

theorem setEtaleRestrictionReflectsIsomorphisms : (Scheme.EtaleH1.setEtaleRestriction
  f).ReflectsIsomorphisms :=
  ⟨fun {_F _G} m _ => isIso_of_setEtaleRestriction_map f m⟩

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5993e82d916c4a5d729146fe80ce8fb758da9f0e348cf5cfb7ee2f2b34992712.
Definitions, hypotheses and universes are retained modulo native names. -/
