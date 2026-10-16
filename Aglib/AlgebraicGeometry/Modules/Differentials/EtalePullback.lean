/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Etale invariance of the actual canonical differential pullback map

The proof extends actual sheaf-valued derivations uniquely on affine etale charts,
glues these extensions, and applies the differential-sheaf universal property.
`differential_precompose` identifies the resulting Hom map with the canonical
adjoint map defined in `Differentials.Basic`. Its invertibility gives the canonical
`etaleDifferentialIso`, matching Stacks 04BX with the identity on the base field.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.Differentials.EtalePullback

universe u

section Ring
variable {A B M : Type u} [CommRing A] [CommRing B] [AddCommGroup M] [Module B M]

/-- Extension of an actual absolute derivation along a formally etale ring map. -/
noncomputable def extendDerivation (f : A →+* B) (hf : f.FormallyEtale)
    (D : let := Module.compHom M f; Derivation ℤ A M) : Derivation ℤ B M := by
  let := f.toAlgebra
  let := Module.compHom M f
  let : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  have : Algebra.FormallyEtale A B := hf
  exact ((D.liftKaehlerDifferential.liftBaseChange B).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B).symm.toLinearMap).compDer
      (KaehlerDifferential.D ℤ B)

/-- The extended absolute derivation agrees with the original derivation on the source ring. -/
lemma extendDerivation_apply (f : A →+* B) (hf : f.FormallyEtale)
    (D : let := Module.compHom M f; Derivation ℤ A M) (a : A) :
    extendDerivation f hf D (f a) = D a := by
  let := f.toAlgebra
  let := Module.compHom M f
  let : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  have : Algebra.FormallyEtale A B := hf
  change D.liftKaehlerDifferential.liftBaseChange B
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B).symm
        (KaehlerDifferential.D ℤ B (algebraMap A B a))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul]
  exact D.liftKaehlerDifferential_comp_D a

/-- Such an extension is uniquely determined by its values on the source ring. -/
lemma derivation_ext (f : A →+* B) (hf : f.FormallyEtale)
    (D E : Derivation ℤ B M) (h : ∀ a, D (f a) = E (f a)) : D = E := by
  let := f.toAlgebra
  let := Module.compHom M f
  let : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  have : Algebra.FormallyEtale A B := hf
  apply (KaehlerDifferential.linearMapEquivDerivation ℤ B).symm.injective
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B).surjective x
  change D.liftKaehlerDifferential
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B) x) =
      E.liftKaehlerDifferential
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B) x)
  have hres : (D.liftKaehlerDifferential.restrictScalars A).comp
      (KaehlerDifferential.map ℤ ℤ A B) =
      (E.liftKaehlerDifferential.restrictScalars A).comp
      (KaehlerDifferential.map ℤ ℤ A B) := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    simpa [RingHom.algebraMap_toAlgebra] using h a
  induction x using TensorProduct.inductionOn with
  | tmul b y =>
    change D.liftKaehlerDifferential (KaehlerDifferential.mapBaseChange ℤ A B (b ⊗ₜ y)) =
      E.liftKaehlerDifferential (KaehlerDifferential.mapBaseChange ℤ A B (b ⊗ₜ y))
    rw [KaehlerDifferential.mapBaseChange_tmul, LinearMap.map_smul, LinearMap.map_smul]
    exact congrArg (fun z => b • z) (LinearMap.congr_fun hres y)
  | add x y hx hy => simp only [map_add, hx, hy]

end Ring

section Scheme
variable {F : Type u} [Field F] {X Y : FScheme F} (f : X ⟶ Y)

/-- Target-presheaf derivations into the direct image of M, vanishing on structural field
constants. -/
abbrev OnTargetDerivation (M : X.left.Modules) :=
  PresheafOfModulesOfCommRing.Derivation'
    ((Scheme.Modules.pushforward f.left).obj M).val (constantsPresheafMap Y)

/-- The absolute target-section derivation with its values restricted to the indicated source
open. -/
noncomputable def localSourceDerivation (M : X.left.Modules) (d : OnTargetDerivation f M)
    (U : Y.left.Opens) (V : X.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U) :
    let := Module.compHom Γ(M, V) (f.left.appLE U V e).hom
    Derivation ℤ Γ(Y.left, U) Γ(M, V) := by
  let := Module.compHom Γ(M, V) (f.left.appLE U V e).hom
  refine Derivation.mk'
    (((M.val.map (homOfLE e).op).hom.toAddMonoidHom.comp (d.d (X := op U))).toIntLinearMap) ?_
  intro a b
  change (M.val.map (homOfLE e).op) (d.d (a * b)) = _
  rw [d.d_mul, map_add]
  congr 1
  · exact M.val.map_smul (homOfLE e).op (f.left.app U a) (d.d b)
  · exact M.val.map_smul (homOfLE e).op (f.left.app U b) (d.d a)

/-- Restricting the target derivation gives the displayed source-section value. -/
lemma localSourceDerivation_apply (M : X.left.Modules) (d : OnTargetDerivation f M)
    (U : Y.left.Opens) (V : X.left.Opens) (e : V ≤ f.left ⁻¹ᵁ U) (a : Γ(Y.left, U)) :
    localSourceDerivation f M d U V e a = (M.val.map (homOfLE e).op) (d.d a) := rfl

/-- The extension to source affine sections of the target derivation along the etale
affine-chart map. -/
noncomputable def localDerivation [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (U : Y.left.Opens) (hU : IsAffineOpen U)
    (V : X.left.Opens) (hV : IsAffineOpen V) (e : V ≤ f.left ⁻¹ᵁ U) :
    Derivation ℤ Γ(X.left, V) Γ(M, V) :=
  extendDerivation (f.left.appLE U V e).hom (f.left.etale_appLE hU hV e).formallyEtale
    (localSourceDerivation f M d U V e)

/-- The affine étale extension agrees with the target derivation after pullback. -/
lemma localDerivation_apply [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (U : Y.left.Opens) (hU : IsAffineOpen U)
    (V : X.left.Opens) (hV : IsAffineOpen V) (e : V ≤ f.left ⁻¹ᵁ U)
    (a : Γ(Y.left, U)) :
    localDerivation f M d U hU V hV e (f.left.appLE U V e a) =
      (M.val.map (homOfLE e).op) (d.d a) :=
  extendDerivation_apply _ _ _ a

/-- Uniqueness makes the affine-chart extensions compatible under restriction. -/
lemma localDerivation_naturality [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (U : Y.left.Opens) (hU : IsAffineOpen U)
    (V : X.left.Opens) (hV : IsAffineOpen V) (e : V ≤ f.left ⁻¹ᵁ U)
    (U' : Y.left.Opens) (hU' : IsAffineOpen U')
    (V' : X.left.Opens) (hV' : IsAffineOpen V') (e' : V' ≤ f.left ⁻¹ᵁ U')
    (hUU : U' ≤ U) (hVV : V' ≤ V) (a : Γ(X.left, V)) :
    (M.val.map (homOfLE hVV).op) (localDerivation f M d U hU V hV e a) =
      localDerivation f M d U' hU' V' hV' e'
        (X.left.presheaf.map (homOfLE hVV).op a) := by
  let r := (X.left.presheaf.map (homOfLE hVV).op).hom
  let := r.toAlgebra
  let := Module.compHom Γ(M, V') r
  let : IsScalarTower Γ(X.left, V) Γ(X.left, V') Γ(M, V') :=
    IsScalarTower.of_compHom _ _ _
  let D : Derivation ℤ Γ(X.left, V) Γ(M, V') :=
    (M.val.map (homOfLE hVV).op).hom.compDer (localDerivation f M d U hU V hV e)
  let E : Derivation ℤ Γ(X.left, V) Γ(M, V') :=
    (localDerivation f M d U' hU' V' hV' e').compAlgebraMap Γ(X.left, V)
  have heq : D = E := derivation_ext (f.left.appLE U V e).hom
    (f.left.etale_appLE hU hV e).formallyEtale D E (by
      intro b
      change (M.val.map (homOfLE hVV).op)
        (localDerivation f M d U hU V hV e (f.left.appLE U V e b)) =
          localDerivation f M d U' hU' V' hV' e'
            (X.left.presheaf.map (homOfLE hVV).op (f.left.appLE U V e b))
      rw [localDerivation_apply]
      have hc := (f.left.appLE_map e (homOfLE hVV).op).trans
        (f.left.map_appLE e' (homOfLE hUU).op).symm
      have hcb := congrArg (fun k : Γ(Y.left, U) ⟶ Γ(X.left, V') => k b) hc
      change X.left.presheaf.map (homOfLE hVV).op (f.left.appLE U V e b) =
        f.left.appLE U' V' e' (Y.left.presheaf.map (homOfLE hUU).op b) at hcb
      rw [hcb, localDerivation_apply]
      erw [d.d_map]
      change (M.val.map (homOfLE hVV).op) ((M.val.map (homOfLE e).op) (d.d b)) =
        (M.val.map (homOfLE e').op)
          ((M.val.map ((TopologicalSpace.Opens.map f.left.base).map (homOfLE hUU)).op) (d.d b))
      rw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
      rfl)
  exact Derivation.congr_fun heq a

/-- Compatible affine target and source opens inside T and W, with the source open mapping into
the target open. -/
structure Chart (W : X.left.Opens) (T : Y.left.Opens) where
  /-- The affine target open of the chart, contained in T. -/
  U : Y.left.Opens
  /-- The affine source open of the chart, contained in W and mapping into U. -/
  V : X.left.Opens
  affineU : IsAffineOpen U
  affineV : IsAffineOpen V
  leW : V ≤ W
  leT : U ≤ T
  lePull : V ≤ f.left ⁻¹ᵁ U

/-- Compatible affine source and target charts cover the indicated source open. -/
lemma chartCover (W : X.left.Opens) (T : Y.left.Opens) (hWT : W ≤ f.left ⁻¹ᵁ T) :
    W ≤ iSup (fun i : Chart f W T => i.V) := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUT⟩ :=
    Y.left.isBasis_affineOpens.exists_subset_of_mem_open (hWT hx) T.2
  have hxWU : x ∈ W ⊓ f.left ⁻¹ᵁ U := ⟨hx, hxU⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVWU⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hxWU (W ⊓ f.left ⁻¹ᵁ U).2
  let i : Chart f W T := ⟨U, V, hU, hV, hVWU.trans inf_le_left, hUT,
    hVWU.trans inf_le_right⟩
  exact (le_iSup (fun i : Chart f W T => i.V) i) hxV

/-- The actual topological abelian sheaf underlying the module sheaf M. -/
noncomputable def moduleSheaf (M : X.left.Modules) : TopCat.Sheaf Ab X.left :=
  ⟨M.presheaf, M.isSheaf⟩

/-- The extended derivation applied to the given section after restriction to the compatible
affine chart. -/
noncomputable def chartSection [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) {W : X.left.Opens} {T : Y.left.Opens}
    (i : Chart f W T) (a : Γ(X.left, W)) : Γ(M, i.V) :=
  localDerivation f M d i.U i.affineU i.V i.affineV i.lePull
    (X.left.presheaf.map (homOfLE i.leW).op a)

/-- The locally extended values agree on chart intersections, checked on affine refinements. -/
lemma chartSection_compatible [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) {W : X.left.Opens} {T : Y.left.Opens}
    (a : Γ(X.left, W)) :
    TopCat.Presheaf.IsCompatible M.presheaf (fun i : Chart f W T => i.V)
      (fun i => chartSection f M d i a) := by
  intro i j
  have hWT : i.V ⊓ j.V ≤ f.left ⁻¹ᵁ (i.U ⊓ j.U) := by
    intro x hx
    exact ⟨i.lePull hx.1, j.lePull hx.2⟩
  apply (moduleSheaf M).eq_of_locally_eq'
    (fun k : Chart f (i.V ⊓ j.V) (i.U ⊓ j.U) => k.V) (i.V ⊓ j.V)
    (fun k => homOfLE k.leW) (chartCover f _ _ hWT)
  intro k
  change (M.val.map (homOfLE k.leW).op)
      ((M.val.map (TopologicalSpace.Opens.infLELeft i.V j.V).op) (chartSection f M d i a)) =
    (M.val.map (homOfLE k.leW).op)
      ((M.val.map (TopologicalSpace.Opens.infLERight i.V j.V).op) (chartSection f M d j a))
  rw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
  unfold chartSection
  erw [localDerivation_naturality f M d i.U i.affineU i.V i.affineV i.lePull
      k.U k.affineU k.V k.affineV k.lePull (k.leT.trans inf_le_left)
        (k.leW.trans inf_le_left),
    localDerivation_naturality f M d j.U j.affineU j.V j.affineV j.lePull
      k.U k.affineU k.V k.affineV k.lePull (k.leT.trans inf_le_right)
        (k.leW.trans inf_le_right)]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The compatible chart values admit a unique glued section of the actual module sheaf. -/
lemma sectionGluingExists [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (W : X.left.Opens) (a : Γ(X.left, W)) :
    ∃! s : Γ(M, W), ∀ i : Chart f W ⊤,
      (M.val.map (homOfLE i.leW).op) s = chartSection f M d i a :=
  (moduleSheaf M).existsUnique_gluing' (fun i : Chart f W ⊤ => i.V) W
    (fun i => homOfLE i.leW) (chartCover f W ⊤ le_top)
      (fun i => chartSection f M d i a) (chartSection_compatible f M d a)

/-- The actual module-sheaf gluing of the affine-chart extensions of one section. -/
noncomputable def globalSection [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (W : X.left.Opens) (a : Γ(X.left, W)) : Γ(M, W) :=
  (sectionGluingExists f M d W a).exists.choose

/-- The glued extension restricts to its value on every compatible affine chart. -/
lemma globalSection_restrict [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) {W : X.left.Opens} {T : Y.left.Opens}
    (i : Chart f W T) (a : Γ(X.left, W)) :
    (M.val.map (homOfLE i.leW).op) (globalSection f M d W a) = chartSection f M d i a := by
  let j : Chart f W ⊤ := ⟨i.U, i.V, i.affineU, i.affineV, i.leW, le_top, i.lePull⟩
  exact (sectionGluingExists f M d W a).exists.choose_spec j

/-- The glued extension is additive on structure sections. -/
lemma globalSection_add [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (W : X.left.Opens) (a b : Γ(X.left, W)) :
    globalSection f M d W (a + b) = globalSection f M d W a + globalSection f M d W b := by
  apply (moduleSheaf M).eq_of_locally_eq' (fun i : Chart f W ⊤ => i.V) W
    (fun i => homOfLE i.leW) (chartCover f W ⊤ le_top)
  intro i
  change (M.val.map (homOfLE i.leW).op) (globalSection f M d W (a + b)) =
    (M.val.map (homOfLE i.leW).op) (globalSection f M d W a + globalSection f M d W b)
  erw [map_add, globalSection_restrict, globalSection_restrict, globalSection_restrict]
  simp [chartSection]

/-- The glued extension satisfies the Leibniz rule. -/
lemma globalSection_mul [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (W : X.left.Opens) (a b : Γ(X.left, W)) :
    globalSection f M d W (a * b) = a • globalSection f M d W b +
      b • globalSection f M d W a := by
  apply (moduleSheaf M).eq_of_locally_eq' (fun i : Chart f W ⊤ => i.V) W
    (fun i => homOfLE i.leW) (chartCover f W ⊤ le_top)
  intro i
  change (M.val.map (homOfLE i.leW).op) (globalSection f M d W (a * b)) =
    (M.val.map (homOfLE i.leW).op) (a • globalSection f M d W b + b • globalSection f M d W a)
  erw [map_add, M.val.map_smul, M.val.map_smul,
    globalSection_restrict, globalSection_restrict, globalSection_restrict]
  simp [chartSection, Derivation.leibniz]
  rfl

/-- The glued extension commutes with restriction of structure sections. -/
lemma globalSection_naturality [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (W W' : X.left.Opens) (h : W' ≤ W) (a : Γ(X.left, W)) :
    globalSection f M d W' (X.left.presheaf.map (homOfLE h).op a) =
      (M.val.map (homOfLE h).op) (globalSection f M d W a) := by
  apply (moduleSheaf M).eq_of_locally_eq' (fun i : Chart f W' ⊤ => i.V) W'
    (fun i => homOfLE i.leW) (chartCover f W' ⊤ le_top)
  intro i
  change (M.val.map (homOfLE i.leW).op)
      (globalSection f M d W' (X.left.presheaf.map (homOfLE h).op a)) =
    (M.val.map (homOfLE i.leW).op) ((M.val.map (homOfLE h).op) (globalSection f M d W a))
  rw [globalSection_restrict, ← M.val.map_comp_apply]
  let j : Chart f W ⊤ := ⟨i.U, i.V, i.affineU, i.affineV, i.leW.trans h, le_top, i.lePull⟩
  trans chartSection f M d j a
  · unfold chartSection
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · exact (globalSection_restrict f M d j a).symm

/-- The glued extension vanishes on sections from the base field. -/
lemma globalSection_constant [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) (W : X.left.Opens) (c : F) :
    globalSection f M d W (constantSection X W c) = 0 := by
  apply (moduleSheaf M).eq_of_locally_eq' (fun i : Chart f W ⊤ => i.V) W
    (fun i => homOfLE i.leW) (chartCover f W ⊤ le_top)
  intro i
  change (M.val.map (homOfLE i.leW).op) (globalSection f M d W (constantSection X W c)) = _
  rw [globalSection_restrict]
  unfold chartSection
  rw [map_constantSection]
  have hc : f.left.appLE i.U i.V i.lePull (constantSection Y i.U c) =
      constantSection X i.V c := by
    change X.left.presheaf.map (homOfLE i.lePull).op (f.left.app i.U (constantSection Y i.U c)) = _
    rw [Cohomology.app_constantSection, map_constantSection]
  rw [← hc, localDerivation_apply]
  have hd : d.d (constantSection Y i.U c) = 0 := d.d_app c
  rw [hd, map_zero, map_zero]

/-- Gluing preserves addition, Leibniz, restrictions and vanishing on the base field. -/
noncomputable def extendOnSource [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) :
    PresheafOfModulesOfCommRing.Derivation' M.val (constantsPresheafMap X) where
  d {U} := AddMonoidHom.mk' (globalSection f M d U.unop) (globalSection_add f M d U.unop)
  d_mul {U} := globalSection_mul f M d U.unop
  d_map {U V} i a := globalSection_naturality f M d U.unop V.unop i.unop.le a
  d_app {U} := globalSection_constant f M d U.unop

/-- Precomposition with the structure-sheaf map, giving a target derivation into the direct
image of M. -/
noncomputable def precomposeDerivation (M : X.left.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (constantsPresheafMap X)) :
    OnTargetDerivation f M where
  d {U} := d.d.comp (f.left.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b :=
    (congrArg d.d ((f.left.app U.unop).hom.map_mul a b)).trans (d.d_mul _ _)
  d_map {U V} i a := by
    have h : f.left.app V.unop (Y.left.presheaf.map i a) =
        X.left.presheaf.map ((TopologicalSpace.Opens.map f.left.base).map i.unop).op
          (f.left.app U.unop a) :=
      congrArg (fun g : Γ(Y.left, U.unop) ⟶ Γ(X.left, f.left ⁻¹ᵁ V.unop) => g.hom a)
        (f.left.c.naturality i)
    exact (congrArg d.d h).trans (d.d_map _ _)
  d_app {U} c :=
    (congrArg d.d (Cohomology.app_constantSection f U.unop c)).trans (d.d_app c)

/-- The absolute integer derivation on sections over V underlying the source relative
derivation. -/
noncomputable def sourceAbsolute (M : X.left.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (constantsPresheafMap X))
    (V : X.left.Opens) : Derivation ℤ Γ(X.left, V) Γ(M, V) :=
  Derivation.mk' (d.d (X := op V)).toIntLinearMap (d.d_mul (X := op V))

/-- Any source derivation extending the target derivation has the prescribed chart values. -/
lemma sourceDerivation_onChart [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M)
    (dx : PresheafOfModulesOfCommRing.Derivation' M.val (constantsPresheafMap X))
    (h : precomposeDerivation f M dx = d) {W : X.left.Opens} {T : Y.left.Opens}
    (i : Chart f W T) (a : Γ(X.left, W)) :
    (M.val.map (homOfLE i.leW).op) (dx.d a) = chartSection f M d i a := by
  have hlocal : sourceAbsolute M dx i.V =
      localDerivation f M d i.U i.affineU i.V i.affineV i.lePull :=
    derivation_ext (f.left.appLE i.U i.V i.lePull).hom
      (f.left.etale_appLE i.affineU i.affineV i.lePull).formallyEtale _ _ (by
        intro b
        change dx.d (f.left.appLE i.U i.V i.lePull b) = _
        rw [localDerivation_apply]
        change dx.d (X.left.presheaf.map (homOfLE i.lePull).op (f.left.app i.U b)) = _
        erw [dx.d_map]
        exact congrArg (fun z => (M.val.map (homOfLE i.lePull).op) z)
          (congrArg (fun k : OnTargetDerivation f M => k.d (X := op i.U) b) h))
  unfold chartSection
  rw [← hlocal]
  exact (dx.d_map (homOfLE i.leW).op a).symm

/-- An extension of the target derivation to the source is unique. -/
lemma extendOnSource_unique [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M)
    (dx : PresheafOfModulesOfCommRing.Derivation' M.val (constantsPresheafMap X))
    (h : precomposeDerivation f M dx = d) : extendOnSource f M d = dx := by
  ext U a
  apply (moduleSheaf M).eq_of_locally_eq' (fun i : Chart f U.unop ⊤ => i.V) U.unop
    (fun i => homOfLE i.leW) (chartCover f U.unop ⊤ le_top)
  intro i
  change (M.val.map (homOfLE i.leW).op) (globalSection f M d U.unop a) =
    (M.val.map (homOfLE i.leW).op) (dx.d a)
  rw [globalSection_restrict]
  exact (sourceDerivation_onChart f M d dx h i a).symm

/-- Precomposing the glued source extension recovers the target derivation. -/
lemma precompose_extendOnSource [Etale f.left] (M : X.left.Modules)
    (d : OnTargetDerivation f M) : precomposeDerivation f M (extendOnSource f M d) = d := by
  ext U a
  let W := f.left ⁻¹ᵁ U.unop
  apply (moduleSheaf M).eq_of_locally_eq' (fun i : Chart f W U.unop => i.V) W
    (fun i => homOfLE i.leW) (chartCover f W U.unop le_rfl)
  intro i
  change (M.val.map (homOfLE i.leW).op) (globalSection f M d W (f.left.app U.unop a)) =
    (M.val.map (homOfLE i.leW).op) (d.d a)
  rw [globalSection_restrict]
  unfold chartSection
  have hc := (f.left.appLE_map (V := W) le_rfl (homOfLE i.leW).op).trans
    (f.left.map_appLE i.lePull (homOfLE i.leT).op).symm
  rw [Scheme.Hom.appLE_eq_app] at hc
  have hcb := congrArg (fun k : Γ(Y.left, U.unop) ⟶ Γ(X.left, i.V) => k a) hc
  change X.left.presheaf.map (homOfLE i.leW).op (f.left.app U.unop a) =
    f.left.appLE i.U i.V i.lePull (Y.left.presheaf.map (homOfLE i.leT).op a) at hcb
  rw [hcb, localDerivation_apply]
  erw [d.d_map]
  change (M.val.map (homOfLE i.lePull).op)
      ((M.val.map ((TopologicalSpace.Opens.map f.left.base).map (homOfLE i.leT)).op) (d.d a)) =
    (M.val.map (homOfLE i.leW).op) (d.d a)
  rw [← M.val.map_comp_apply]
  rfl

/-- Precomposition along an étale morphism bijects the actual relative derivations. -/
lemma precomposeDerivation_bijective [Etale f.left] (M : X.left.Modules) :
    Function.Bijective (precomposeDerivation f M) := by
  constructor
  · intro dx ex h
    exact (extendOnSource_unique f M _ dx rfl).symm.trans
      (extendOnSource_unique f M _ ex h.symm)
  · intro d
    exact ⟨extendOnSource f M d, precompose_extendOnSource f M d⟩

/-- Exact correspondence of the canonical adjoint differential map with
derivation precomposition. -/
lemma differential_precompose (M : X.left.Modules) (h : differentialSheaf X ⟶ M) :
    differentialSheafHomEquiv Y ((Scheme.Modules.pushforward f.left).obj M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _
        (differentialPullbackMap f ≫ h)) =
      precomposeDerivation f M (differentialSheafHomEquiv X M h) := by
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv_naturality_right,
    differentialPullbackMap_adjoint]
  ext U a
  change h.val.app _
      ((differentialPushforwardMap f).val.app U ((differentialSheafDerivation Y).d a)) =
    h.val.app _ ((differentialSheafDerivation X).d (f.left.app U.unop a))
  rw [differentialPushforwardMap_d]
  rfl

/-- The canonical differential pullback map of an étale morphism is an isomorphism. -/
theorem isIso_differentialPullbackMap [Etale f.left] : IsIso (differentialPullbackMap f) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  constructor
  · intro h k hhk
    apply (differentialSheafHomEquiv X M).injective
    apply (precomposeDerivation_bijective f M).injective
    rw [← differential_precompose f M h, ← differential_precompose f M k]
    exact congrArg (fun q => differentialSheafHomEquiv Y
      ((Scheme.Modules.pushforward f.left).obj M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _ q)) hhk
  · intro q
    let d := differentialSheafHomEquiv Y ((Scheme.Modules.pushforward f.left).obj M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _ q)
    let h := (differentialSheafHomEquiv X M).symm (extendOnSource f M d)
    refine ⟨h, ?_⟩
    apply ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).injective
    apply (differentialSheafHomEquiv Y ((Scheme.Modules.pushforward f.left).obj M)).injective
    rw [differential_precompose]
    change precomposeDerivation f M
      ((differentialSheafHomEquiv X M) ((differentialSheafHomEquiv X M).symm
        (extendOnSource f M d))) = d
    rw [Equiv.apply_symm_apply]
    exact precompose_extendOnSource f M d

end Scheme

end AlgebraicGeometry.Scheme.Modules.Differentials.EtalePullback

namespace AlgebraicGeometry.Scheme.Modules.Differentials

universe u

variable {F : Type u} [Field F]

/-- The isomorphism induced by the canonical differential pullback map of an étale morphism. -/
def etaleDifferentialIso {X Y : FScheme F} (f : X ⟶ Y) [Etale f.left] :
    (Scheme.Modules.pullback f.left).obj (differentialSheaf Y) ≅ differentialSheaf X := by
  letI := EtalePullback.isIso_differentialPullbackMap f
  exact asIso (differentialPullbackMap f)

/-- The étale differential isomorphism has exactly the canonical differential map as its hom. -/
@[simp]
theorem etaleDifferentialIso_hom {X Y : FScheme F} (f : X ⟶ Y) [Etale f.left] :
    (etaleDifferentialIso f).hom = differentialPullbackMap f := rfl

end AlgebraicGeometry.Scheme.Modules.Differentials
