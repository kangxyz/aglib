/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Sheafification
/-!
# Exterior powers and actual open-immersion restriction

The original inverse section-ring isomorphisms of an open immersion
compare the native pointwise exterior powers. The forward map is the
original semilinear exterior map; its inverse uses the same ring
isomorphism and the original inverse semilinear map. The existing
restriction/sheafification comparison then gives an isomorphism between
the original sheaf exterior power of the restriction and the restriction
of the original exterior power.

Both maps retain the literal original wedges on every open, and the
comparison is natural for the original coefficient morphisms. No
quasicoherence, local freeness, rank, finiteness or condition on the base
is required. Degree zero, empty sources and zero rings are included.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u v₁ v₂ w₁ w₂
namespace AlgebraicGeometry.Scheme.Modules

private def scalarIdentity {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars φ).obj M →ₛₗ[φ] M where
  toFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private def inverseScalarIdentity {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} S) :
    M →ₛₗ[e.symm.toRingHom] (ModuleCat.restrictScalars e.toRingHom).obj M where
  toFun := id
  map_add' := fun _ _ => rfl
  map_smul' s m := by
    change s • m = e (e.symm s) • m
    rw [e.apply_symm_apply]

private theorem scalarExterior_left {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} S) (n : ℕ)
    (x : ((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n) :
    exteriorPower.mapSemilinear n (inverseScalarIdentity e M)
      (exteriorPower.mapSemilinear n (scalarIdentity e.toRingHom M) x) = x := by
  let : RingHomCompTriple e.toRingHom e.symm.toRingHom (RingHom.id R) :=
    ⟨by ext r; exact e.symm_apply_apply r⟩
  have h : (inverseScalarIdentity e M).comp (scalarIdentity e.toRingHom M) =
      (LinearMap.id (R := R) (M := (ModuleCat.restrictScalars e.toRingHom).obj M)) := by
    ext x
    rfl
  have H := exteriorPower.mapSemilinear_comp n (scalarIdentity e.toRingHom M)
    (inverseScalarIdentity e M)
  rw [h, exteriorPower.mapSemilinear_id] at H
  exact (LinearMap.congr_fun H x).symm

private theorem scalarExterior_right {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} S) (n : ℕ) (x : M.exteriorPower n) :
    exteriorPower.mapSemilinear n (scalarIdentity e.toRingHom M)
      (exteriorPower.mapSemilinear n (inverseScalarIdentity e M) x) = x := by
  let : RingHomCompTriple e.symm.toRingHom e.toRingHom (RingHom.id S) :=
    ⟨by ext s; exact e.apply_symm_apply s⟩
  have h : (scalarIdentity e.toRingHom M).comp (inverseScalarIdentity e M) =
      (LinearMap.id (R := S) (M := M)) := by
    ext x
    rfl
  have H := exteriorPower.mapSemilinear_comp n (inverseScalarIdentity e M)
    (scalarIdentity e.toRingHom M)
  rw [h, exteriorPower.mapSemilinear_id] at H
  exact (LinearMap.congr_fun H x).symm

private def scalarExteriorHom {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} S) (n : ℕ) :
    ((ModuleCat.restrictScalars φ).obj M).exteriorPower n ⟶
      (ModuleCat.restrictScalars φ).obj (M.exteriorPower n) :=
  ModuleCat.semilinearMapAddEquiv φ _ _
    (exteriorPower.mapSemilinear n (scalarIdentity φ M))

private def scalarExteriorInv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} S) (n : ℕ) :
    (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n) ⟶
      ((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n := by
  let g := exteriorPower.mapSemilinear n (inverseScalarIdentity e M)
  exact ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n))
    (Y := ((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n)
    { toFun := g
      map_add' := g.map_add
      map_smul' r x := by
        change g (e r • x) = r • g x
        exact (g.map_smulₛₗ (e r) x).trans
          (congrArg (fun t => t • g x) (e.symm_apply_apply r)) }

private def scalarExteriorIso {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} S) (n : ℕ) :
    ((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n) where
  hom := scalarExteriorHom e.toRingHom M n
  inv := scalarExteriorInv e M n
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact scalarExterior_left e M n x
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact scalarExterior_right e M n x


private theorem scalarExteriorHom_mk {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} S) (n : ℕ)
    (v : Fin n → (ModuleCat.restrictScalars φ).obj M) :
    scalarExteriorHom φ M n (ModuleCat.exteriorPower.mk
      (R := R) (M := (ModuleCat.restrictScalars φ).obj M) v) =
      ModuleCat.exteriorPower.mk (R := S) (M := M) v :=
  exteriorPower.mapSemilinear_apply_ιMulti n (scalarIdentity φ M) v

section Presheaf
variable {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D] {F : C ⥤ D}
  {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}

private def exteriorPushforwardHom
    (φ : S₀ ⟶ F.op ⋙ R₀) (P : PresheafOfModulesOfCommRing.{u} R₀) (n : ℕ) :
    PresheafOfModulesOfCommRing.exteriorPower
      ((PresheafOfModulesOfCommRing.pushforward φ).obj P) n ⟶
    (PresheafOfModulesOfCommRing.pushforward φ).obj
      (PresheafOfModulesOfCommRing.exteriorPower P n) where
  app U := scalarExteriorHom (φ.app U).hom
    (P.obj (F.op.obj U)) n
  naturality {U V} f := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro v
    change scalarExteriorHom (φ.app V).hom
        (P.obj (F.op.obj V)) n
        ((PresheafOfModulesOfCommRing.exteriorPower
          ((PresheafOfModulesOfCommRing.pushforward φ).obj P) n).map f
          (ModuleCat.exteriorPower.mk (R := S₀.obj U)
            (M := ((PresheafOfModulesOfCommRing.pushforward
              φ).obj P).obj U) v)) =
      (PresheafOfModulesOfCommRing.exteriorPower P n).map (F.op.map f)
        (scalarExteriorHom (φ.app U).hom
          (P.obj (F.op.obj U)) n
          (ModuleCat.exteriorPower.mk (R := S₀.obj U)
            (M := ((PresheafOfModulesOfCommRing.pushforward
              φ).obj P).obj U) v))
    let PU := P.obj (F.op.obj U)
    let PV := P.obj (F.op.obj V)
    let vU : Fin n → PU := v
    let vV : Fin n → PV := fun i => P.map (F.op.map f) (vU i)
    have h1 := congrArg (scalarExteriorHom (φ.app V).hom PV n)
      (PresheafOfModulesOfCommRing.exteriorPower_map_mk
        ((PresheafOfModulesOfCommRing.pushforward φ).obj P) n f v)
    have h2 := scalarExteriorHom_mk (φ.app V).hom PV n vV
    have h3 := PresheafOfModulesOfCommRing.exteriorPower_map_mk P n (F.op.map f) vU
    have h4 := congrArg ((PresheafOfModulesOfCommRing.exteriorPower P n).map (F.op.map f))
      (scalarExteriorHom_mk (φ.app U).hom PU n vU).symm
    exact h1.trans (h2.trans (h3.symm.trans h4))

private def exteriorPushforwardIso
    (φ : S₀ ⟶ F.op ⋙ R₀) (hφ : IsIso φ)
    (P : PresheafOfModulesOfCommRing.{u} R₀) (n : ℕ) :
    PresheafOfModulesOfCommRing.exteriorPower
      ((PresheafOfModulesOfCommRing.pushforward φ).obj P) n ≅
    (PresheafOfModulesOfCommRing.pushforward φ).obj
      (PresheafOfModulesOfCommRing.exteriorPower P n) := by
  letI := hφ
  have h (U : Cᵒᵖ) : IsIso ((exteriorPushforwardHom φ P n).app U) := by
    change IsIso (scalarExteriorHom (φ.app U).hom
      (P.obj (F.op.obj U)) n)
    exact (scalarExteriorIso ((asIso (φ.app U)).commRingCatIsoToRingEquiv)
      (P.obj (F.op.obj U)) n).isIso_hom
  exact PresheafOfModules.isoMk
    (fun U => asIso ((exteriorPushforwardHom φ P n).app U))
    (fun {_ _} f => (exteriorPushforwardHom φ P n).naturality f)

end Presheaf

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

private def moduleExteriorPowerRestrictionIsoImpl (M : Y.Modules) (n : ℕ) :
    moduleExteriorPower X (M.restrict j) n ≅ (moduleExteriorPower Y M n).restrict j := by
  exact (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).mapIso
    (exteriorPushforwardIso (F := j.opensFunctor) (R₀ := Y.sheaf.obj) (S₀ := X.sheaf.obj)
      (restrictionRingHom j).hom (restrictionRingHom_isIso j) M.val n) ≪≫
      (restrictionSheafificationIso j).app
        (PresheafOfModulesOfCommRing.exteriorPower M.val n)

/-- The actual exterior power commutes with the original restriction along any open immersion. -/
def moduleExteriorPowerRestrictionIso (M : Y.Modules) (n : ℕ) :
    moduleExteriorPower X (M.restrict j) n ≅ (moduleExteriorPower Y M n).restrict j :=
  private_decl% (moduleExteriorPowerRestrictionIsoImpl j M n)

private abbrev pointModule (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :
    Module (X.sheaf.obj.obj (Opposite.op U)) (M.val.obj (Opposite.op U)) := by
  change Module (X.ringCatSheaf.obj.obj (Opposite.op U)) (M.val.obj (Opposite.op U))
  infer_instance

private theorem moduleExteriorPowerRestrictionIso_unit (M : Y.Modules) (n : ℕ) :
    (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
        (PresheafOfModulesOfCommRing.exteriorPower (M.restrict j).val n) ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map
        (moduleExteriorPowerRestrictionIso j M n).hom =
    exteriorPushforwardHom (restrictionRingHom j).hom M.val n ≫
      (PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
        ((SheafOfModulesOfCommRing.associatedSheafUnit Y.sheaf).app
          (PresheafOfModulesOfCommRing.exteriorPower M.val n)) := by
  let P := PresheafOfModulesOfCommRing.exteriorPower M.val n
  let P₀ := PresheafOfModulesOfCommRing.exteriorPower (M.restrict j).val n
  let S := SheafOfModulesOfCommRing.associatedSheaf X.sheaf
  let V := SheafOfModulesOfCommRing.toPresheaf X.sheaf
  let F := PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom
  let η := SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf
  let μ : P₀ ⟶ F.obj P := exteriorPushforwardHom (restrictionRingHom j).hom M.val n
  let t := (restrictionSheafificationIso j).hom.app P
  have hNat : η.app P₀ ≫ V.map (S.map μ) = μ ≫ η.app (F.obj P) :=
    (η.naturality μ).symm
  have hComp : η.app (F.obj P) ≫ V.map t = F.map
      ((SheafOfModulesOfCommRing.associatedSheafUnit Y.sheaf).app P) :=
    SheafOfModules.sheafificationPushforwardComparison_unit
      (F := j.opensFunctor) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y) (S := X.ringCatSheaf) (R := Y.ringCatSheaf)
      ⟨whiskerRight (restrictionRingHom j).hom (forget₂ CommRingCat RingCat)⟩ P
  change η.app P₀ ≫ V.map (S.map μ ≫ t) = _
  calc
    η.app P₀ ≫ V.map (S.map μ ≫ t) =
        η.app P₀ ≫ (V.map (S.map μ) ≫ V.map t) :=
      congrArg (fun f => η.app P₀ ≫ f) (V.map_comp (S.map μ) t)
    _ = (η.app P₀ ≫ V.map (S.map μ)) ≫ V.map t := (Category.assoc _ _ _).symm
    _ = (μ ≫ η.app (F.obj P)) ≫ V.map t := congrArg (fun f => f ≫ V.map t) hNat
    _ = μ ≫ (η.app (F.obj P) ≫ V.map t) := Category.assoc _ _ _
    _ = _ := congrArg (fun f => μ ≫ f) hComp

/-- The forward comparison preserves the same original wedge on every source open. -/
theorem moduleExteriorPowerRestrictionIso_hom_mk (M : Y.Modules) (n : ℕ) (U : X.Opens)
    (v : Fin n → (M.restrict j).val.obj (Opposite.op U)) :
    (moduleExteriorPowerRestrictionIso j M n).hom.val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf (M.restrict j) n).app
        (Opposite.op U) v) =
      (SheafOfModulesOfCommRing.exteriorPowerMk Y.sheaf M n).app
        (Opposite.op (j ''ᵁ U)) v := by
  let P := PresheafOfModulesOfCommRing.exteriorPower M.val n
  let P₀ := PresheafOfModulesOfCommRing.exteriorPower (M.restrict j).val n
  let := pointModule X (M.restrict j) U
  let x : P₀.obj (Opposite.op U) :=
    _root_.exteriorPower.ιMulti (X.sheaf.obj.obj (Opposite.op U)) n v
  have h := congrArg (fun f : P₀ ⟶ ((moduleExteriorPower Y M n).restrict j).val =>
    f.app (Opposite.op U) x) (moduleExteriorPowerRestrictionIso_unit j M n)
  have hm := scalarExteriorHom_mk
    ((restrictionRingHom j).hom.app (Opposite.op U)).hom (M.val.obj (Opposite.op (j ''ᵁ U))) n v
  change (moduleExteriorPowerRestrictionIso j M n).hom.val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf (M.restrict j) n).app
        (Opposite.op U) v) =
    (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf).app
      (Opposite.op (j ''ᵁ U))
      (scalarExteriorHom ((restrictionRingHom j).hom.app (Opposite.op U)).hom
        (M.val.obj (Opposite.op (j ''ᵁ U))) n x) at h
  exact h.trans (congrArg
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf).app
      (Opposite.op (j ''ᵁ U))) hm)

/-- The inverse comparison also preserves the same original wedge. -/
theorem moduleExteriorPowerRestrictionIso_inv_mk (M : Y.Modules) (n : ℕ) (U : X.Opens)
    (v : Fin n → (M.restrict j).val.obj (Opposite.op U)) :
    (moduleExteriorPowerRestrictionIso j M n).inv.val.app (Opposite.op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk Y.sheaf M n).app
        (Opposite.op (j ''ᵁ U)) v) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf (M.restrict j) n).app
        (Opposite.op U) v := by
  exact (congrArg ((moduleExteriorPowerRestrictionIso j M n).inv.val.app (Opposite.op U))
    (moduleExteriorPowerRestrictionIso_hom_mk j M n U v).symm).trans
      (ConcreteCategory.congr_hom
        (congrArg (fun f => f.val.app (Opposite.op U))
          (moduleExteriorPowerRestrictionIso j M n).hom_inv_id) _)


/-- The comparison is natural for the original module-sheaf morphisms. -/
theorem moduleExteriorPowerRestrictionIso_naturality {M N : Y.Modules} (f : M ⟶ N) (n : ℕ) :
    (moduleExteriorPowerFunctor X n).map ((restrictFunctor j).map f) ≫
        (moduleExteriorPowerRestrictionIso j N n).hom =
      (moduleExteriorPowerRestrictionIso j M n).hom ≫
        (restrictFunctor j).map ((moduleExteriorPowerFunctor Y n).map f) := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext X.sheaf (M.restrict j)
    ((moduleExteriorPower Y N n).restrict j) n
  intro U v
  let f' := (restrictFunctor j).map f
  let ftop := (restrictFunctor j).map ((moduleExteriorPowerFunctor Y n).map f)
  change (moduleExteriorPowerRestrictionIso j N n).hom.val.app U
      (((moduleExteriorPowerFunctor X n).map f').val.app U
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf (M.restrict j) n).app U v)) =
    ftop.val.app U ((moduleExteriorPowerRestrictionIso j M n).hom.val.app U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf (M.restrict j) n).app U v))
  have h1 := congrArg ((moduleExteriorPowerRestrictionIso j N n).hom.val.app U)
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X.sheaf f' n U v)
  have h2 := moduleExteriorPowerRestrictionIso_hom_mk j N n U.unop
    (fun i => f'.val.app U (v i))
  have h3 := SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk Y.sheaf f n
    (Opposite.op (j ''ᵁ U.unop)) v
  have h4 := congrArg (ftop.val.app U)
    (moduleExteriorPowerRestrictionIso_hom_mk j M n U.unop v).symm
  exact h1.trans (h2.trans (h3.symm.trans h4))

end AlgebraicGeometry.Scheme.Modules
