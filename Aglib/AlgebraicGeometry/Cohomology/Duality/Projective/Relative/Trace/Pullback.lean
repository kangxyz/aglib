/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.AffineModel.Identity

/-!
# Canonical pullbacks and identity normalization for relative trace

The original higher-image comparison for a chosen pullback agrees with its
comparison on any Cartesian open square, followed by the native identity-base
normalization. A categorical cancellation lemma retains the same normalization
when comparing trace morphisms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

/-- The canonical pullback comparison is the original comparison followed by the
original identity-normalized comparison; no projective model occurs here. -/
theorem relativeHigherRestrictionIso_canonical
    {X W Y Z : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (n : ℕ) (N : Y.Modules) :
    let E := H.isoPullback
    let q' := pullback.snd p j
    let HE : IsPullback E.inv q' q (𝟙 Z) :=
      IsPullback.of_horiz_isIso
        ⟨H.isoPullback_inv_snd.trans (Category.comp_id q').symm⟩
    (relativeHigherRestrictionIso p (pullback.fst p j) q' j
      (IsPullback.of_hasPullback p j) n).hom.app N =
      (relativeHigherRestrictionIso p i q j H n).hom.app N ≫
        (identityHigherModelIso q E.inv q' HE n).hom.app (N.restrict j) := by
  let E := H.isoPullback
  let i' := pullback.fst p j
  let q' := pullback.snd p j
  let HE : IsPullback E.inv q' q (𝟙 Z) :=
    IsPullback.of_horiz_isIso
      ⟨H.isoPullback_inv_snd.trans (Category.comp_id q').symm⟩
  let F₀ := relativeHigherFunctor p n
  let F₁ := relativeHigherFunctor q n
  let F₂ := relativeHigherFunctor q' n
  let J := Modules.restrictFunctor j
  let K := Modules.restrictFunctor (𝟙 Z)
  let u := restrictFunctorId (X := Z)
  let α := (relativeHigherRestrictionIso p i q j H n).hom.app N
  let m := relativeHigherRestrictionIso q E.inv q' (𝟙 Z) HE n
  let C := relativeHigherRestrictionIso p i' q' j (IsPullback.of_hasPullback p j) n
  have hc := relativeHigherRestrictionIso_comp p q q' i j E.inv (𝟙 Z) H HE
    (HE.paste_horiz H) n N
  rw [relativeHigherRestrictionIso_congr p q' (E.inv ≫ i) i' (𝟙 Z ≫ j) j
    (HE.paste_horiz H) (IsPullback.of_hasPullback p j) H.isoPullback_inv_fst
      (Category.id_comp j) n N] at hc
  have hL := congrArg F₂.map (restrictCompLeftUnit_inv j N)
  simp only [Functor.map_comp] at hL
  simp only [Category.assoc] at hc
  rw [restrictCompLeftUnit_hom_assoc, hL] at hc
  let U₀ := u.app (J.obj (F₀.obj N))
  let U₁ := F₂.mapIso (u.app (J.obj N))
  change U₀.hom ≫ C.hom.app N ≫ U₁.inv =
    K.map α ≫ m.hom.app (J.obj N) at hc
  have hcn := congrArg
    (fun z : K.obj (J.obj (F₀.obj N)) ⟶ F₂.obj (K.obj (J.obj N)) =>
      U₀.inv ≫ z ≫ U₁.hom) hc
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at hcn
  have hu : α ≫ u.inv.app (F₁.obj (J.obj N)) = U₀.inv ≫ K.map α :=
    u.inv.naturality (X := J.obj (F₀.obj N)) (Y := F₁.obj (J.obj N)) α
  rw [← reassoc_of% hu] at hcn
  simpa only [identityHigherModelIso, U₀, U₁, F₀, F₁, F₂, J, K, u, α, m, C,
    E, i', q', Functor.comp_obj, Functor.id_obj, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Category.assoc] using hcn

/-- Trace compatibility with identity restriction, together with coefficient
naturality, removes the original identity-normalized comparison. -/
theorem traceIdentityNormalization
    {C : Type*} [Category* C] (F G K : C ⥤ C) (u : K ≅ 𝟭 C)
    (β : F ⋙ K ≅ K ⋙ G) (N : C)
    (t : F.obj N ⟶ N) (t' : G.obj N ⟶ N) (tK : G.obj (K.obj N) ⟶ K.obj N)
    (hopen : β.hom.app N ≫ tK = K.map t)
    (hnat : G.map (u.hom.app N) ≫ t' = tK ≫ u.hom.app N) :
    (u.inv.app (F.obj N) ≫ β.hom.app N ≫ G.map (u.hom.app N)) ≫ t' = t := by
  have hu : t ≫ u.inv.app N = u.inv.app (F.obj N) ≫ K.map t :=
    u.inv.naturality (X := F.obj N) (Y := N) t
  simp only [Category.assoc]
  rw [hnat, ← Category.assoc (β.hom.app N), hopen,
    ← Category.assoc, ← hu, Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.id_obj, Category.comp_id]

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
