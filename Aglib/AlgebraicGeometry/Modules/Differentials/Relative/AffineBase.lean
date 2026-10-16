/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Relative derivations over an affine base

For any scheme over `Spec R`, relative derivations are exactly derivations
annihilating the original constant `R` sections. Principal base-open rings
are localizations and hence formally unramified, so the induced derivation
on each such ring is zero. Original sheaf separatedness then gives vanishing
on every base section. The coefficient module sheaf is arbitrary.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- Constant base sections through the original global structural map and restrictions. -/
def affineBaseConstants : (Functor.const X.Opensᵒᵖ).obj R ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op
  naturality U V i := by
    simp only [Functor.const_obj_map, Category.assoc,
      ← X.presheaf.map_comp]
    rfl

/-- On an inverse-image open, constants are the original pullback of base constants. -/
theorem affineBaseConstants_app_preimage (U : (Spec R).Opens) :
    (affineBaseConstants f).app (op (f ⁻¹ᵁ U)) =
      CommRingCat.ofHom (algebraMap R Γ(Spec R, U)) ≫ f.app U := by
  have h : (Spec R).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ f.app U =
      f.appTop ≫ X.presheaf.map (homOfLE le_top).op :=
    f.naturality (homOfLE (le_top : U ≤ ⊤)).op
  exact (congrArg (fun k => (Scheme.ΓSpecIso R).inv ≫ k) h).symm

/-- Forgetting relative base-section vanishing retains exactly the original derivation values. -/
def toAffineBaseDerivation (M : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c) :
    PresheafOfModulesOfCommRing.Derivation' M.val (affineBaseConstants f) where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {U} r := by
    change d.d (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op
      (f.appTop ((Scheme.ΓSpecIso R).inv r))) = 0
    exact (d.d_map (homOfLE (le_top : U.unop ≤ ⊤)).op
      (f.appTop ((Scheme.ΓSpecIso R).inv r))).trans
      ((congrArg (M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op)
        (d.d_app ((Scheme.ΓSpecIso R).inv r))).trans (map_zero _))

variable (M : X.Modules)
  (d : PresheafOfModulesOfCommRing.Derivation' M.val (affineBaseConstants f))

/-- The original pullback of any constant base section has zero derivative. -/
theorem affineBaseDerivation_constant (U : (Spec R).Opens) (r : R) :
    d.d (f.app U (algebraMap R Γ(Spec R, U) r)) = 0 := by
  have h := congrArg (fun k : R ⟶ Γ(X, f ⁻¹ᵁ U) => k r)
    (affineBaseConstants_app_preimage f U)
  exact (congrArg d.d h).symm.trans (d.d_app r)

/-- The original section pullback and derivation induce an actual base-linear derivation. -/
def affineBaseSectionDerivation (U : (Spec R).Opens) :
    letI := Module.compHom Γ(M, f ⁻¹ᵁ U) (f.app U).hom
    letI := Module.compHom Γ(M, f ⁻¹ᵁ U) (algebraMap R Γ(Spec R, U))
    _root_.Derivation R Γ(Spec R, U) Γ(M, f ⁻¹ᵁ U) := by
  let := Module.compHom Γ(M, f ⁻¹ᵁ U) (f.app U).hom
  let := Module.compHom Γ(M, f ⁻¹ᵁ U) (algebraMap R Γ(Spec R, U))
  refine {
    toFun := fun a => d.d (f.app U a)
    map_add' := fun a b =>
      (congrArg d.d ((f.app U).hom.map_add a b)).trans (d.d.map_add _ _)
    map_smul' := ?_
    map_one_eq_zero' := ?_
    leibniz' := fun a b =>
      (congrArg d.d ((f.app U).hom.map_mul a b)).trans (d.d_mul _ _) }
  · intro r a
    change d.d (f.app U (r • a)) = _
    rw [Algebra.smul_def, map_mul, d.d_mul, affineBaseDerivation_constant,
      smul_zero, add_zero]
    rfl
  · exact (congrArg d.d (f.app U).hom.map_one).trans (d.d_one _)

/-- The induced section derivation has exactly the original pointwise values. -/
theorem affineBaseSectionDerivation_apply (U : (Spec R).Opens) (a : Γ(Spec R, U)) :
    affineBaseSectionDerivation f M d U a = d.d (f.app U a) := rfl

/-- Principal base-open sections have zero derivative because their relative Kähler module
over the base ring is zero. No condition on the coefficient module is used. -/
theorem affineBaseDerivation_basicOpen (r : R)
    (a : Γ(Spec R, PrimeSpectrum.basicOpen r)) :
    d.d (f.app (PrimeSpectrum.basicOpen r) a) = 0 := by
  let U := PrimeSpectrum.basicOpen r
  let := Module.compHom Γ(M, f ⁻¹ᵁ U) (f.app U).hom
  let := Module.compHom Γ(M, f ⁻¹ᵁ U) (algebraMap R Γ(Spec R, U))
  let : IsScalarTower R Γ(Spec R, U) Γ(M, f ⁻¹ᵁ U) :=
    IsScalarTower.of_compHom _ _ _
  let : Algebra.FormallyUnramified R Γ(Spec R, U) :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers r)
  let : Subsingleton (_root_.Derivation R Γ(Spec R, U) Γ(M, f ⁻¹ᵁ U)) :=
    (KaehlerDifferential.linearMapEquivDerivation R Γ(Spec R, U)).surjective.subsingleton
  exact congrArg (fun D : _root_.Derivation R Γ(Spec R, U) Γ(M, f ⁻¹ᵁ U) => D a)
    (Subsingleton.elim (affineBaseSectionDerivation f M d U) 0)

/-- Original sheaf separatedness extends principal-open vanishing to every base section. -/
theorem affineBaseDerivation_base (U : (Spec R).Opens) (a : Γ(Spec R, U)) :
    d.d (f.app U a) = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show f x ∈ U from hx) U.isOpen
  let hsub : f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ f ⁻¹ᵁ U :=
    ((Opens.map f.base).map (homOfLE hrU)).le
  refine ⟨f ⁻¹ᵁ PrimeSpectrum.basicOpen r, hsub, hxr, ?_⟩
  change M.val.map (homOfLE hsub).op (d.d (f.app U a)) =
    M.val.map (homOfLE hsub).op 0
  have hn : f.app (PrimeSpectrum.basicOpen r)
        ((Spec R).presheaf.map (homOfLE hrU).op a) =
      X.presheaf.map (homOfLE hsub).op (f.app U a) :=
    ConcreteCategory.congr_hom (f.naturality (homOfLE hrU).op) a
  exact (d.d_map (homOfLE hsub).op (f.app U a)).symm.trans
    ((congrArg d.d hn).symm.trans
      ((affineBaseDerivation_basicOpen f M d r
        ((Spec R).presheaf.map (homOfLE hrU).op a)).trans
        (map_zero (M.val.map (homOfLE hsub).op).hom).symm))

/-- Killing constant base sections gives the native relative derivation with unchanged values. -/
def fromAffineBaseDerivation : PresheafOfModulesOfCommRing.Derivation M.val f.c where
  d := d.d
  d_mul := d.d_mul
  d_map := d.d_map
  d_app {U} a := affineBaseDerivation_base f M d U.unop a

/-- Relative derivations over an affine base are exactly derivations killing its constants,
for every actual coefficient module sheaf. -/
def affineBaseDerivationEquiv :
    PresheafOfModulesOfCommRing.Derivation M.val f.c ≃
      PresheafOfModulesOfCommRing.Derivation' M.val (affineBaseConstants f) where
  toFun := toAffineBaseDerivation f M
  invFun := fromAffineBaseDerivation f M
  left_inv d := by
    ext U a
    rfl
  right_inv d := by
    ext U a
    rfl

/-- The forward equivalence has exactly the original derivation values. -/
theorem affineBaseDerivationEquiv_apply_d
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c)
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (affineBaseDerivationEquiv f M d).d a = d.d a := rfl

/-- The inverse equivalence has exactly the original derivation values. -/
theorem affineBaseDerivationEquiv_symm_d (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    ((affineBaseDerivationEquiv f M).symm d).d a = d.d a := rfl

/-- The affine-base equivalence commutes with original coefficient morphisms. -/
theorem affineBaseDerivationEquiv_postcomp (N : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c) (k : M ⟶ N) :
    affineBaseDerivationEquiv f N (d.postcomp k.val) =
      (affineBaseDerivationEquiv f M d).postcomp k.val := by
  ext U a
  rfl

/-- The inverse affine-base equivalence commutes with the same coefficient morphisms. -/
theorem affineBaseDerivationEquiv_symm_postcomp (N : X.Modules) (k : M ⟶ N) :
    (affineBaseDerivationEquiv f N).symm (d.postcomp k.val) =
      ((affineBaseDerivationEquiv f M).symm d).postcomp k.val := by
  ext U a
  rfl

section SheafComparison

open SheafOfModulesOfCommRing.DifferentialsConstruction

/-- The two native universal sheaves attached to the two equivalent derivation conditions. -/
def affineBaseUniversalIso : relativeDifferentialSheaf f ≅
    relativeDifferentials X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f) := by
  let P : X.Modules :=
    relativeDifferentials X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f)
  let D := derivation X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f)
  let g : relativeDifferentialSheaf f ⟶ P :=
    relativeDifferentialDesc f P ((affineBaseDerivationEquiv f P).symm D)
  let h : P ⟶ relativeDifferentialSheaf f :=
    desc X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f) (relativeDifferentialSheaf f)
      (affineBaseDerivationEquiv f (relativeDifferentialSheaf f) (relativeDifferentialDerivation f))
  have hg (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
      g.val.app U ((relativeDifferentialDerivation f).d a) = D.d a :=
    relativeDifferentialDesc_d f P ((affineBaseDerivationEquiv f P).symm D) U a
  have hh (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
      h.val.app U (D.d a) = (relativeDifferentialDerivation f).d a :=
    desc_d X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f) (relativeDifferentialSheaf f)
      (affineBaseDerivationEquiv f (relativeDifferentialSheaf f)
        (relativeDifferentialDerivation f)) U a
  refine ⟨g, h, ?_, ?_⟩
  · apply relativeDifferentialSheaf_hom_ext f _
    intro U a
    exact (congrArg (h.val.app U) (hg U a)).trans (hh U a)
  · apply SheafOfModulesOfCommRing.DifferentialsConstruction.hom_ext
      X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f) P
    intro U a
    exact (congrArg (g.val.app U) (hh U a)).trans (hg U a)

/-- The first universal comparison preserves the actual differential values. -/
theorem affineBaseUniversalIso_hom_d (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (affineBaseUniversalIso f).hom.val.app U ((relativeDifferentialDerivation f).d a) =
      (derivation X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f)).d a :=
  relativeDifferentialDesc_d f _ _ U a

/-- The inverse universal comparison preserves those same values. -/
theorem affineBaseUniversalIso_inv_d (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (affineBaseUniversalIso f).inv.val.app U
        ((derivation X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f)).d a) =
      (relativeDifferentialDerivation f).d a :=
  desc_d X.sheaf (F := 𝟭 X.Opens) (affineBaseConstants f) _ _ U a

/-- The original same-site constant-base differential presheaf,
with original module sheafification. -/
abbrev affineBaseDifferentialSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
      (affineBaseConstants f))

/-- Actual relative differentials over `Spec R` identify canonically with the original
sheafification of constant-`R` differentials. -/
def relativeDifferentialSheafAffineBaseIso :
    relativeDifferentialSheaf f ≅ affineBaseDifferentialSheaf f :=
  affineBaseUniversalIso f ≪≫ relativeDifferentialsIdIso X.sheaf (affineBaseConstants f)

/-- The final comparison sends the original differential to the original constant-base
sheafification unit applied to the native same-site differential. -/
theorem relativeDifferentialSheafAffineBaseIso_hom_d
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialSheafAffineBaseIso f).hom.val.app U
        ((relativeDifferentialDerivation f).d a) =
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X)
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
          (affineBaseConstants f)).presheaf).app U
        ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
          (affineBaseConstants f)).d a) :=
  (congrArg ((relativeDifferentialsIdIso X.sheaf (affineBaseConstants f)).hom.val.app U)
    (affineBaseUniversalIso_hom_d f U a)).trans
    (relativeDifferentialsIdIso_hom_d X.sheaf (affineBaseConstants f) U a)

/-- The inverse comparison sends that same original sheafified differential back to `d a`. -/
theorem relativeDifferentialSheafAffineBaseIso_inv_d
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialSheafAffineBaseIso f).inv.val.app U
        ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X)
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
            (affineBaseConstants f)).presheaf).app U
          ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
            (affineBaseConstants f)).d a)) =
      (relativeDifferentialDerivation f).d a :=
  (congrArg ((affineBaseUniversalIso f).inv.val.app U)
    (relativeDifferentialsIdIso_inv_d X.sheaf (affineBaseConstants f) U a)).trans
    (affineBaseUniversalIso_inv_d f U a)

end SheafComparison

end AlgebraicGeometry.Scheme.Modules.Differentials
