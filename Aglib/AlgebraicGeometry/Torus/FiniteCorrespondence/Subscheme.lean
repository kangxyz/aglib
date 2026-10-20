/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.Basic
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ModuleCycle
public import Aglib.Algebra.Module.CommutingAutomorphisms.SupportPoints
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Subscheme for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `Subscheme.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`159aec09944ecbd45efb3fb5906f876768b1ffe7fd2555f9a0190350678e1d83`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

/-!
The source records Suslin, “On the Grayson Spectral Sequence”, MathNet English
text (2003), printed p.220, retained PDF SHA-256
`ce78ac4118284b93394874a11a2aa1cd7002af388a4ef035ade0c9d5f38b295b`.
This is source provenance for the prime/subscheme dictionary. The native
statements prove their displayed scheme and ideal identifications directly.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Torus.FiniteCorrespondence.Subscheme
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R]

/-- The split two-dimensional torus is affine. -/
instance torus_isAffine : IsAffine (torusScheme R) := by
  dsimp [torusScheme]
  infer_instance

/-- Coordinates of an actual map to an affine scheme. -/
def coordinateMap {A : CommRingCat.{u}} {Z : Scheme.{u}} (i : Z ⟶ Spec A) :
    A ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso A).inv ≫ i.appTop

theorem coordinateMap_specMap {A B : CommRingCat.{u}} (f : A ⟶ B) :
    coordinateMap (Spec.map f) = f ≫ (Scheme.ΓSpecIso B).inv :=
  (Scheme.ΓSpecIso_inv_naturality f).symm

theorem coordinateMap_comp {A B : CommRingCat.{u}} {Z : Scheme.{u}}
    (i : Z ⟶ Spec B) (f : A ⟶ B) :
    coordinateMap (i ≫ Spec.map f) = f ≫ coordinateMap i := by
  simp only [coordinateMap, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]

/-- Extract the defining ideal from an independently specified ideal sheaf. -/
def definingIdeal (I : (torusScheme R).IdealSheafData) : Ideal (Laurent R) :=
  RingHom.ker (coordinateMap I.subschemeι).hom

theorem definingIdeal_eq (I : (torusScheme R).IdealSheafData) :
    definingIdeal I = (I.ideal ⟨⊤, isAffineOpen_top _⟩).comap
      (Scheme.ΓSpecIso (.of (Laurent R))).inv.hom := by
  rw [definingIdeal, coordinateMap, CommRingCat.hom_comp, ← RingHom.comap_ker]
  congr 1
  exact I.ker_subschemeι_app ⟨⊤, isAffineOpen_top _⟩

theorem definingIdeal_injective : Function.Injective (definingIdeal (R := R)) := by
  intro I J h
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [definingIdeal_eq, definingIdeal_eq] at h
  exact Ideal.comap_injective_of_surjective _
    (Scheme.ΓSpecIso (.of (Laurent R))).commRingCatIsoToRingEquiv.symm.surjective h

theorem definingIdeal_ker {Z : Scheme.{u}} (i : Z ⟶ torusScheme R)
    [QuasiCompact i] :
    definingIdeal i.ker = RingHom.ker (coordinateMap i).hom := by
  rw [definingIdeal_eq, i.ker_apply]
  exact RingHom.comap_ker _ _

theorem definingIdeal_point (p : FiniteDominantPrime R) :
    definingIdeal (pointImmersion p).ker = p.val := by
  rw [definingIdeal_ker, pointImmersion, coordinateMap_specMap]
  change RingHom.ker
    ((Scheme.ΓSpecIso (.of (Laurent R ⧸ p.val))).commRingCatIsoToRingEquiv.symm.toRingHom.comp
      (Ideal.Quotient.mk p.val)) = p.val
  rw [RingHom.ker_equiv_comp, Ideal.mk_ker]

/-- Integral closed subschemes of the actual affine torus, finite and dominant
onto the base. This definition uses scheme predicates, not prime labels.
For a reduced integral simplex, finite dominance is the source's finite
surjectivity condition (Suslin 2003, printed p.220). -/
def FiniteDominantSubscheme (R : Type u) [CommRing R] :=
  {I : (torusScheme R).IdealSheafData //
    IsIntegral I.subscheme ∧ IsFinite (I.subschemeι ≫ torusStructure R) ∧
      IsDominant (I.subschemeι ≫ torusStructure R)}

/-- A finite dominant subscheme carries its specified integral scheme structure. -/
instance integral (Z : FiniteDominantSubscheme R) : IsIntegral Z.val.subscheme := Z.property.1
/-- A finite dominant subscheme has a finite structure map to the base. -/
instance finite (Z : FiniteDominantSubscheme R) :
    IsFinite (Z.val.subschemeι ≫ torusStructure R) := Z.property.2.1
/-- A finite dominant subscheme has a dominant structure map to the base. -/
instance dominant (Z : FiniteDominantSubscheme R) :
    IsDominant (Z.val.subschemeι ≫ torusStructure R) := Z.property.2.2

/-- The existing forward prime geometry, placed in the independent scheme presentation. -/
def ofPoint (p : FiniteDominantPrime R) : FiniteDominantSubscheme R := by
  refine ⟨(pointImmersion p).ker, ?_, ?_, ?_⟩
  · exact IsIntegral.of_isIso (pointImmersion p).toImage
  all_goals
    have he : (pointImmersion p).ker.subschemeι ≫ torusStructure R =
        inv (pointImmersion p).toImage ≫ pointStructure p := by
      rw [← pointImmersion_structure]
      apply (IsIso.eq_inv_comp _).mpr
      simp only [← Category.assoc, Scheme.Hom.toImage_imageι]
    rw [he]
    infer_instance

/-- Every actual integral finite dominant closed immersion supplies the
independent ideal-sheaf presentation; the source scheme is preserved up to
its canonical isomorphism onto its scheme-theoretic image. -/
def ofClosedImmersion {Z : Scheme.{u}} [IsIntegral Z]
    (i : Z ⟶ torusScheme R) [IsClosedImmersion i]
    [IsFinite (i ≫ torusStructure R)] [IsDominant (i ≫ torusStructure R)] :
    FiniteDominantSubscheme R := by
  refine ⟨i.ker, IsIntegral.of_isIso i.toImage, ?_, ?_⟩
  all_goals
    have he : i.ker.subschemeι ≫ torusStructure R =
        inv i.toImage ≫ (i ≫ torusStructure R) := by
      apply (IsIso.eq_inv_comp _).mpr
      simp only [← Category.assoc, Scheme.Hom.toImage_imageι]
    rw [he]
    infer_instance

theorem coordinateMap_surjective (Z : FiniteDominantSubscheme R) :
    Function.Surjective (coordinateMap Z.val.subschemeι).hom := by
  exact (Z.val.subschemeι_app_surjective ⟨⊤, isAffineOpen_top _⟩).comp
    (Scheme.ΓSpecIso (.of (Laurent R))).commRingCatIsoToRingEquiv.symm.surjective

theorem coordinateMap_structure_finite (Z : FiniteDominantSubscheme R) :
    (coordinateMap (Z.val.subschemeι ≫ torusStructure R)).hom.Finite := by
  exact (Scheme.Hom.finite_appTop _).comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)

theorem definingIdeal_finite (Z : FiniteDominantSubscheme R) :
    Module.Finite R (Laurent R ⧸ definingIdeal Z.val) := by
  let f := (coordinateMap Z.val.subschemeι).hom
  let e := f.quotientKerEquivOfSurjective (coordinateMap_surjective Z)
  have h := coordinateMap_structure_finite Z
  have hc : coordinateMap (Z.val.subschemeι ≫ torusStructure R) =
      CommRingCat.ofHom (algebraMap R (Laurent R)) ≫ coordinateMap Z.val.subschemeι :=
    coordinateMap_comp _ _
  rw [hc, CommRingCat.hom_comp] at h
  have he : e.symm.toRingHom.comp (f.comp (algebraMap R (Laurent R))) =
      algebraMap R (Laurent R ⧸ definingIdeal Z.val) := by
    ext r
    exact RingHom.quotientKerEquivOfSurjective_symm_apply
      (coordinateMap_surjective Z) _
  apply RingHom.finite_algebraMap.mp
  rw [← he]
  exact (RingHom.Finite.of_surjective e.symm.toRingHom e.symm.surjective).comp h

theorem coordinateMap_structure_injective [_root_.IsReduced R]
    (Z : FiniteDominantSubscheme R) :
    Function.Injective (coordinateMap (Z.val.subschemeι ≫ torusStructure R)).hom := by
  let i := Z.val.subschemeι ≫ torusStructure R
  let : IsSchemeTheoreticallyDominant i := IsSchemeTheoreticallyDominant.of_isDominant i
  have hi : Function.Injective i.appTop := i.app_injective ⊤
  exact hi.comp (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.injective

theorem definingIdeal_dominant [_root_.IsReduced R] (Z : FiniteDominantSubscheme R) :
    (definingIdeal Z.val).under R = ⊥ := by
  have h := coordinateMap_structure_injective Z
  have hc : coordinateMap (Z.val.subschemeι ≫ torusStructure R) =
      CommRingCat.ofHom (algebraMap R (Laurent R)) ≫ coordinateMap Z.val.subschemeι :=
    coordinateMap_comp _ _
  rw [hc, CommRingCat.hom_comp] at h
  ext r
  change (coordinateMap Z.val.subschemeι).hom (algebraMap R (Laurent R) r) = 0 ↔ r = 0
  exact ⟨fun hr => h (by simpa using hr), fun hr => by simp [hr]⟩

/-- The inverse is built from global sections of the actual integral subscheme.
Reducedness of the base is used exactly to turn dominance into injectivity. -/
def toPoint [_root_.IsReduced R] (Z : FiniteDominantSubscheme R) : FiniteDominantPrime R :=
  ⟨definingIdeal Z.val, RingHom.ker_isPrime _, definingIdeal_finite Z,
    definingIdeal_dominant Z⟩

@[simp] theorem toPoint_ofPoint [_root_.IsReduced R] (p : FiniteDominantPrime R) :
    toPoint (ofPoint p) = p := by
  apply Subtype.val_injective
  exact definingIdeal_point p

@[simp] theorem ofPoint_toPoint [_root_.IsReduced R] (Z : FiniteDominantSubscheme R) :
    ofPoint (toPoint Z) = Z := by
  apply Subtype.val_injective
  apply definingIdeal_injective
  exact definingIdeal_point (toPoint Z)

/-- Canonical degreewise generator identification with genuine integral finite
closed subschemes. No flatness of their coordinate algebras is imposed. -/
def pointEquivSubscheme [_root_.IsReduced R] : FiniteDominantPrime R ≃ FiniteDominantSubscheme R
    where
  toFun := ofPoint
  invFun := toPoint
  left_inv := toPoint_ofPoint
  right_inv := ofPoint_toPoint

/-- The inverse literally realizes the original closed subscheme over the torus. -/
def realizationIso [_root_.IsReduced R] {Z : Scheme.{u}} [IsIntegral Z]
    (i : Z ⟶ torusScheme R) [IsClosedImmersion i]
    [IsFinite (i ≫ torusStructure R)] [IsDominant (i ≫ torusStructure R)] :
    Z ≅ pointScheme (toPoint (ofClosedImmersion i)) := by
  let p := toPoint (ofClosedImmersion i)
  have h : (pointImmersion p).ker = i.ker :=
    congrArg Subtype.val (ofPoint_toPoint (ofClosedImmersion i))
  let l := IsClosedImmersion.lift (pointImmersion p) i h.le
  let := IsClosedImmersion.isIso_lift (pointImmersion p) i h
  exact asIso l

@[reassoc (attr := simp)]
theorem realizationIso_hom_immersion [_root_.IsReduced R]
    {Z : Scheme.{u}} [IsIntegral Z]
    (i : Z ⟶ torusScheme R) [IsClosedImmersion i]
    [IsFinite (i ≫ torusStructure R)] [IsDominant (i ≫ torusStructure R)] :
    (realizationIso i).hom ≫ pointImmersion (toPoint (ofClosedImmersion i)) = i :=
  IsClosedImmersion.lift_fac _ _ _

/-- All ideals, including nonreduced fibres, have their actual closed subscheme. -/
def ofIdeal (I : Ideal (Laurent R)) : (torusScheme R).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker

@[simp] theorem definingIdeal_ofIdeal (I : Ideal (Laurent R)) :
    definingIdeal (ofIdeal I) = I := by
  rw [ofIdeal, definingIdeal_ker, coordinateMap_specMap]
  change RingHom.ker
    ((Scheme.ΓSpecIso (.of (Laurent R ⧸ I))).commRingCatIsoToRingEquiv.symm.toRingHom.comp
      (Ideal.Quotient.mk I)) = I
  rw [RingHom.ker_equiv_comp, Ideal.mk_ker]

theorem definingIdeal_le_iff (I J : (torusScheme R).IdealSheafData) :
    definingIdeal I ≤ definingIdeal J ↔ I ≤ J := by
  rw [definingIdeal_eq, definingIdeal_eq]
  rw [Ideal.comap_le_comap_iff_of_surjective
    (Scheme.ΓSpecIso (.of (Laurent R))).inv.hom
    (show Function.Surjective (Scheme.ΓSpecIso (.of (Laurent R))).inv.hom from
      (Scheme.ΓSpecIso (.of (Laurent R))).commRingCatIsoToRingEquiv.symm.surjective)]
  exact ⟨Scheme.IdealSheafData.le_of_isAffine, fun h => h _⟩

/-- The identity-coordinate closed immersion is specified by its actual equation. -/
def axisImmersion (a : Laurent R) :
    Spec (.of (Laurent R ⧸ Ideal.span ({a} : Set (Laurent R)))) ⟶ torusScheme R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The hypersurface defined by `a` is a closed subscheme of the torus. -/
instance axisImmersion_isClosedImmersion (a : Laurent R) :
    IsClosedImmersion (axisImmersion a) := by
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Geometric factorization through the closed hypersurface a=0. -/
def FactorsThroughAxis (I : (torusScheme R).IdealSheafData) (a : Laurent R) : Prop :=
  ∃ h : I.subscheme ⟶ Spec (.of (Laurent R ⧸ Ideal.span ({a} : Set (Laurent R)))),
    h ≫ axisImmersion a = I.subschemeι

theorem factorsThroughAxis_iff (I : (torusScheme R).IdealSheafData) (a : Laurent R) :
    FactorsThroughAxis I a ↔ a ∈ definingIdeal I := by
  have ha : definingIdeal (axisImmersion a).ker = Ideal.span ({a} : Set (Laurent R)) :=
    definingIdeal_ofIdeal _
  constructor
  · rintro ⟨h, hh⟩
    have hle := (definingIdeal_le_iff (axisImmersion a).ker I).mpr (by
      rw [← I.ker_subschemeι, ← hh]
      exact h.le_ker_comp _)
    rw [ha] at hle
    exact hle (Ideal.subset_span (Set.mem_singleton a))
  · intro h
    have hle : (axisImmersion a).ker ≤ I :=
      (definingIdeal_le_iff _ _).mp (by rw [ha]; exact Ideal.span_le.mpr (by simpa using h))
    refine ⟨IsClosedImmersion.lift (axisImmersion a) I.subschemeι ?_, ?_⟩
    · simpa only [I.ker_subschemeι] using hle
    · exact IsClosedImmersion.lift_fac _ _ _

/-- Source identity-axis condition on actual closed subschemes. -/
def OnIdentityAxisScheme (Z : FiniteDominantSubscheme R) : Prop :=
  FactorsThroughAxis Z.val (firstCoordinate R - 1) ∨
    FactorsThroughAxis Z.val (secondCoordinate R - 1)

@[simp] theorem ofPoint_onIdentityAxis (p : FiniteDominantPrime R) :
    OnIdentityAxisScheme (ofPoint p) ↔ OnIdentityAxis p := by
  simp only [OnIdentityAxisScheme, factorsThroughAxis_iff, ofPoint,
    definingIdeal_point, OnIdentityAxis]

variable {S : Type u} [CommRing S]

/-- The defining ideal of the geometric direct image is the ring-theoretic inverse image. -/
theorem definingIdeal_map (I : (torusScheme S).IdealSheafData)
    (f : Laurent R →+* Laurent S) :
    definingIdeal (I.map (Spec.map (CommRingCat.ofHom f))) =
      (definingIdeal I).comap f := by
  rw [Scheme.IdealSheafData.map, definingIdeal_ker, coordinateMap_comp,
    CommRingCat.hom_comp, ← RingHom.comap_ker]
  rfl

/-- The actual scheme-theoretic fibre ideal, not an operator transported by the
prime-label equivalence. This also covers nonreduced and nonflat fibres. -/
theorem definingIdeal_comap (I : (torusScheme R).IdealSheafData)
    (f : Laurent R →+* Laurent S) :
    definingIdeal (I.comap (Spec.map (CommRingCat.ofHom f))) =
      (definingIdeal I).map f := by
  let J := ofIdeal ((definingIdeal I).map f)
  apply le_antisymm
  · have h : I.comap (Spec.map (CommRingCat.ofHom f)) ≤ J := by
      apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
      apply (definingIdeal_le_iff _ _).mp
      rw [definingIdeal_map, definingIdeal_ofIdeal]
      exact Ideal.le_comap_map
    have h' := (definingIdeal_le_iff _ _).mpr h
    simpa only [J, definingIdeal_ofIdeal] using h'
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [← definingIdeal_map]
    apply (definingIdeal_le_iff _ _).mpr
    exact I.le_map_comap _

end AlgebraicGeometry.Torus.FiniteCorrespondence.Subscheme
