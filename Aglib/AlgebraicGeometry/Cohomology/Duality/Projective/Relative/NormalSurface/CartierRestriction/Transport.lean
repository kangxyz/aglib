/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.ClosedEmbedding.UnitTrace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.SerreTransport
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.DerivedHom

/-!
# Original affine and Serre transports for canonical restriction

The specified canonical reconstruction transports the original coefficient-valued
Serre map. Original affine derived sections then retain all integer shifts,
including negative targets, and the actual closed-image composition. Coherent
sources give bijectivity of these displayed maps. Their arbitrary source Ext
laws follow from the same original units, shifted compositions and Serre map.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open RelativeCanonicalReindex

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- The public signatures retain the standard module derived-category model. -/
public local instance restrictionTransportModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- Postcomposition by the specified target isomorphism as an additive equivalence. -/
public def restrictionPostcompEquiv {C : Type*} [Category* C] [Preadditive C]
    (K : C) {L L' : C} (e : L ≅ L') : (K ⟶ L) ≃+ (K ⟶ L') where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by
    change (f ≫ e.hom) ≫ e.inv = f
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv g := by
    change (g ≫ e.inv) ≫ e.hom = g
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  map_add' f g := by
    simp only [Preadditive.add_comp]

/-- Identify Ext classes with arrows to the specified shifted single-object reconstruction. -/
public def restrictionExtTargetEquiv
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    (F W : C) (K : DerivedCategory C) (r : ℕ)
    (e : ((DerivedCategory.singleFunctor C 0).obj W)⟦(r : ℤ)⟧ ≅ K) :
    Ext F W r ≃+ ((DerivedCategory.singleFunctor C 0).obj F ⟶ K) where
  toFun x := x.hom ≫ e.hom
  invFun f := Ext.homAddEquiv.symm (f ≫ e.inv)
  left_inv x := by
    apply Ext.homAddEquiv.injective
    rw [AddEquiv.apply_symm_apply]
    change (x.hom ≫ e.hom) ≫ e.inv = x.hom
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv f := by
    change Ext.homAddEquiv (Ext.homAddEquiv.symm (f ≫ e.inv)) ≫ e.hom = f
    rw [AddEquiv.apply_symm_apply, Category.assoc, e.inv_hom_id, Category.comp_id]
  map_add' x y := by rw [Ext.add_hom, Preadditive.add_comp]

/-- Reindex the supplied canonical reconstruction to the original Ext target degree. -/
public def restrictionPurityInput
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    (F W : C) (K : DerivedCategory C) (c : ℤ)
    (E : K ≅ (DerivedCategory.singleFunctor C c).obj W)
    (q r : ℕ) (h : (q : ℤ) - r = c) :
    Ext F W r ≃+ ((DerivedCategory.singleFunctor C 0).obj F ⟶ K⟦(q : ℤ)⟧) :=
  restrictionExtTargetEquiv F W (K⟦(q : ℤ)⟧) r
    (singleReindexIso W c q r h ≪≫
      (shiftFunctor (DerivedCategory C) (q : ℤ)).mapIso E.symm)

private theorem restrictionPurityInput_apply
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    (F W : C) (K : DerivedCategory C) (c : ℤ)
    (E : K ≅ (DerivedCategory.singleFunctor C c).obj W)
    (q r : ℕ) (h : (q : ℤ) - r = c) (x : Ext F W r) :
    restrictionPurityInput F W K c E q r h x =
      x.hom ≫ (singleReindexIso W c q r h).hom ≫ E.inv⟦(q : ℤ)⟧' := rfl

private theorem restrictionPurityInput_identity
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    (W : C) (K : DerivedCategory C) (c : ℕ)
    (E : K ≅ (DerivedCategory.singleFunctor C (c : ℤ)).obj W) :
    restrictionPurityInput W W K (c : ℤ) E c 0 (by omega) (Ext.mk₀ (𝟙 W)) =
      ((DerivedCategory.singleFunctors C).shiftIso (c : ℤ) 0 c (by omega)).inv.app W ≫
        E.inv⟦(c : ℤ)⟧' := by
  rw [restrictionPurityInput_apply, Ext.mk₀_hom]
  simp [singleReindexIso, ShiftedHom.mk₀, shiftFunctorZero']

private theorem restrictionPurityInput_comp
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    (F W : C) (K : DerivedCategory C) (c q r : ℕ) (h : c + r = q)
    (E : K ≅ (DerivedCategory.singleFunctor C (c : ℤ)).obj W) (x : Ext F W r) :
    restrictionPurityInput F W K (c : ℤ) E q r (by omega) x =
      x.hom.comp (c := (q : ℤ)) (restrictionPurityInput W W K (c : ℤ) E c 0
        (by omega) (Ext.mk₀ (𝟙 W))) (by omega) := by
  rw [restrictionPurityInput_identity, restrictionPurityInput_apply,
    singleReindexIso_hom_eq_shift]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z => x.hom ≫
      (((DerivedCategory.singleFunctors C).shiftIso (c : ℤ) 0 c (by omega)).inv.app W)
        ⟦(r : ℤ)⟧' ≫ z)
      ((shiftFunctorAdd' (DerivedCategory C) (c : ℤ) r q (by omega)).inv.naturality E.inv).symm

private theorem restrictionPurityInput_comp_of_degree
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    (F W : C) (K : DerivedCategory C) (c : ℤ) (c₀ q r : ℕ)
    (hc : (c₀ : ℤ) = c) (h : c₀ + r = q)
    (E : K ≅ (DerivedCategory.singleFunctor C c).obj W) (x : Ext F W r) :
    restrictionPurityInput F W K c E q r (by omega) x =
      x.hom.comp (c := (q : ℤ)) (restrictionPurityInput W W K c E c₀ 0
        (by omega) (Ext.mk₀ (𝟙 W))) (by omega) := by
  subst c
  exact restrictionPurityInput_comp F W K c₀ q r h E x

/-- Transport the specified Serre map through the original canonical reconstruction. -/
public def restrictionPuritySerreMap
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt A]
    [Category* B] [Abelian B] [HasDerivedCategory B]
    (F W : A) (K : DerivedCategory A) (D : DerivedCategory B) (N : B)
    (n d q r : ℕ) (h : (q : ℤ) - r = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj W)
    (Φ : ((DerivedCategory.singleFunctor A 0).obj F ⟶ K⟦(q : ℤ)⟧) →+
      (D ⟶ ((DerivedCategory.singleFunctor B (n : ℤ)).obj N)⟦(q : ℤ)⟧)) :
    Ext F W r →+
      ShiftedHom D ((DerivedCategory.singleFunctor B 0).obj N) ((r : ℤ) - d) :=
  ((restrictionPostcompEquiv D
    (singleReindexIso N n q ((r : ℤ) - d) (by omega)).symm).toAddMonoidHom).comp
      (Φ.comp (restrictionPurityInput F W K ((n : ℤ) - d) E q r h).toAddMonoidHom)

private theorem restrictionPuritySerreMap_apply
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt A]
    [Category* B] [Abelian B] [HasDerivedCategory B]
    (F W : A) (K : DerivedCategory A) (D : DerivedCategory B) (N : B)
    (n d q r : ℕ) (h : (q : ℤ) - r = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj W)
    (Φ : ((DerivedCategory.singleFunctor A 0).obj F ⟶ K⟦(q : ℤ)⟧) →+
      (D ⟶ ((DerivedCategory.singleFunctor B (n : ℤ)).obj N)⟦(q : ℤ)⟧))
    (x : Ext F W r) :
    restrictionPuritySerreMap F W K D N n d q r h E Φ x =
      Φ (restrictionPurityInput F W K ((n : ℤ) - d) E q r h x) ≫
        (singleReindexIso N n q ((r : ℤ) - d) (by omega)).inv := rfl

private theorem restrictionPuritySerreMap_bijective
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt A]
    [Category* B] [Abelian B] [HasDerivedCategory B]
    (F W : A) (K : DerivedCategory A) (D : DerivedCategory B) (N : B)
    (n d q r : ℕ) (h : (q : ℤ) - r = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj W)
    (Φ : ((DerivedCategory.singleFunctor A 0).obj F ⟶ K⟦(q : ℤ)⟧) →+
      (D ⟶ ((DerivedCategory.singleFunctor B (n : ℤ)).obj N)⟦(q : ℤ)⟧))
    (hΦ : Function.Bijective Φ) :
    Function.Bijective (restrictionPuritySerreMap F W K D N n d q r h E Φ) :=
  (restrictionPostcompEquiv D
    (singleReindexIso N n q ((r : ℤ) - d) (by omega)).symm).bijective.comp
      (hΦ.comp (restrictionPurityInput F W K ((n : ℤ) - d) E q r h).bijective)

private theorem restrictionOutputReindex
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (N : B) (n d c q r z : ℤ) (hc : c = n - d) (hq : c + r = q) (hz : z = -d) :
    (shiftFunctorAdd' (DerivedCategory B) c r q hq).inv.app
        ((DerivedCategory.singleFunctor B n).obj N) ≫
      (singleReindexIso N n q (r - d) (by omega)).inv =
    ((singleReindexIso N n c z (by omega)).inv)⟦r⟧' ≫
      (shiftFunctorAdd' (DerivedCategory B) z r (r - d) (by omega)).inv.app
        ((DerivedCategory.singleFunctor B 0).obj N) := by
  subst z
  exact singleReindexIso_output_inv N n d c q r hc hq

private theorem restrictionPuritySerre_eq_trace
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt A]
    [Category* B] [Abelian B] [HasDerivedCategory B]
    (G : DerivedCategory.Plus A ⥤ DerivedCategory B) [G.CommShift ℤ]
    (W : A) (K : DerivedCategory A) (N : B) (n d c : ℕ)
    (hc : (c : ℤ) = (n : ℤ) - d)
    (E : K ≅ (DerivedCategory.singleFunctor A ((n : ℤ) - d)).obj W)
    (Φ : ∀ (F : A) (q : ℕ),
      ((DerivedCategory.singleFunctor A 0).obj F ⟶ K⟦(q : ℤ)⟧) →+
        (G.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F) ⟶
          ((DerivedCategory.singleFunctor B (n : ℤ)).obj N)⟦(q : ℤ)⟧))
    (hΦ : ∀ (F F' : A) (a b q : ℕ) (η : Ext F F' a)
      (g : (DerivedCategory.singleFunctor A 0).obj F' ⟶ K⟦(b : ℤ)⟧)
      (hab : a + b = q),
      Φ F q (η.hom.comp (c := (q : ℤ)) g (by omega)) =
        (η.homPlus.map G).comp (c := (q : ℤ)) (Φ F' b g) (by omega))
    (F : A) (r : ℕ) (β : Ext F W r) :
    restrictionPuritySerreMap F W K
        (G.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F)) N
        n d (c + r) r (by omega) E (Φ F (c + r)) β =
      (β.homPlus.map G).comp (c := (r : ℤ) - d)
        (restrictionPuritySerreMap W W K
          (G.obj ((DerivedCategory.Plus.singleFunctor A 0).obj W)) N
          n d c 0 (by omega) E (Φ W c) (Ext.mk₀ (𝟙 W)))
        (by omega) := by
  let δ := restrictionPurityInput W W K ((n : ℤ) - d) E c 0
    (by omega) (Ext.mk₀ (𝟙 W))
  have hinput := restrictionPurityInput_comp_of_degree
    F W K ((n : ℤ) - d) c (c + r) r hc rfl E β
  have hout := restrictionOutputReindex N (n : ℤ) d c
    ((c + r : ℕ) : ℤ) r ((0 : ℤ) - d) hc (by omega) (by omega)
  rw [restrictionPuritySerreMap_apply, restrictionPuritySerreMap_apply]
  change Φ F (c + r)
      (restrictionPurityInput F W K ((n : ℤ) - d) E (c + r) r
        (by omega) β) ≫
      (singleReindexIso N (n : ℤ) ((c + r : ℕ) : ℤ) ((r : ℤ) - d)
        (by omega)).inv =
    (β.homPlus.map G).comp (c := (r : ℤ) - d)
      (Φ W c δ ≫
        (singleReindexIso N (n : ℤ) c ((0 : ℤ) - d) (by omega)).inv) (by omega)
  rw [hinput, hΦ F W r c (c + r) β δ (by omega)]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun z => β.homPlus.map G ≫ (Φ W c δ)⟦(r : ℤ)⟧' ≫ z) hout

section OriginalSerre

variable (A : Type u) [CommRing A] (ι : Type u)
  {Z : Scheme.{u}} (j : Z ⟶ ProjectiveSpace A ι) [IsClosedImmersion j]
  (n : ℕ) (en : ι ≃ Fin (n + 1))
  (N : (Spec (.of A)).Modules) [N.IsQuasicoherent]

/-- The original closed right-adjoint value with the specified relative coefficient. -/
public abbrev restrictionSerreObject : DerivedCategory Z.Modules :=
  DerivedCategory.Plus.ι.obj
    ((derivedClosedImmersionRightAdjointPlus j).obj
      ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace A ι).Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj N)))

/-- The original derived structural image of a single coefficient sheaf. -/
public abbrev restrictionSerreImage (F : Z.Modules) : DerivedCategory (Spec (.of A)).Modules :=
  (derivedPushforwardPlus (j ≫ toSpec A ι) ⋙ DerivedCategory.Plus.ι).obj
    ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj F)

variable (W : Z.Modules) (d c : ℕ) (hc : (c : ℤ) = (n : ℤ) - d)
  (E : restrictionSerreObject A ι j n N ≅
    (DerivedCategory.singleFunctor Z.Modules ((n : ℤ) - d)).obj W)

/-- The original closed-embedding Serre map with its specified canonical coefficient reconstruction.
-/
public def restrictionSerreMap (F : Z.Modules) (r : ℕ) :
    Ext.{u + 1} F W r →+
      ShiftedHom (restrictionSerreImage A ι j F)
        ((DerivedCategory.singleFunctor (Spec (.of A)).Modules 0).obj N) ((r : ℤ) - d) :=
  restrictionPuritySerreMap F W (restrictionSerreObject A ι j n N)
    (restrictionSerreImage A ι j F) N n d (c + r) r (by omega) E
    (relativeClosedEmbeddingSerreMap j (toSpec A ι) A ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec A ι)) n en N F (c + r))

private theorem restrictionSerreMap_bijective [IsNoetherianRing A] (F : Z.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType Z F) (r : ℕ) :
    Function.Bijective (restrictionSerreMap A ι j n en N W d c hc E F r) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  exact restrictionPuritySerreMap_bijective F W (restrictionSerreObject A ι j n N)
    (restrictionSerreImage A ι j F) N n d (c + r) r (by omega) E
    (relativeClosedEmbeddingSerreMap j (toSpec A ι) A ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec A ι)) n en N F (c + r))
    (relativeClosedEmbeddingSerreMap_bijective j (toSpec A ι) A ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec A ι)) n en N F hF (c + r))

private theorem restrictionSerreMap_eq_trace (F : Z.Modules) (r : ℕ)
    (β : Ext.{u + 1} F W r) :
    restrictionSerreMap A ι j n en N W d c hc E F r β =
      (β.homPlus.map (derivedPushforwardPlus (j ≫ toSpec A ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (restrictionSerreMap A ι j n en N W d c hc E W 0 (Ext.mk₀ (𝟙 W))) (by omega) := by
  exact restrictionPuritySerre_eq_trace
    (derivedPushforwardPlus (j ≫ toSpec A ι) ⋙ DerivedCategory.Plus.ι)
    W (restrictionSerreObject A ι j n N) N n d c hc E
    (fun T q => relativeClosedEmbeddingSerreMap j (toSpec A ι) A ι (𝟙 _) (𝟙 _)
      (IsPullback.id_horiz (toSpec A ι)) n en N T q)
    (by
      intro T T' a b q η g hab
      exact relativeClosedEmbeddingSerreMap_comp j (toSpec A ι) A ι (𝟙 _) (𝟙 _)
        (IsPullback.id_horiz (toSpec A ι)) n en N η g hab)
    F r β

private theorem restrictionSerreMap_comp {F F' : Z.Modules} {a b r : ℕ}
    (α : Ext.{u + 1} F F' a) (β : Ext.{u + 1} F' W b) (hab : a + b = r) :
    restrictionSerreMap A ι j n en N W d c hc E F r (α.comp β hab) =
      (α.homPlus.map (derivedPushforwardPlus (j ≫ toSpec A ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (restrictionSerreMap A ι j n en N W d c hc E F' b β) (by omega) := by
  rw [restrictionSerreMap_eq_trace A ι j n en N W d c hc E F r (α.comp β hab),
    restrictionSerreMap_eq_trace A ι j n en N W d c hc E F' b β,
    Ext.homPlus_comp, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc (a₁ := (a : ℤ)) (a₂ := (b : ℤ)) (a₃ := (0 : ℤ) - d)
    (a₁₂ := (r : ℤ)) (a₂₃ := (b : ℤ) - d) (a := (r : ℤ) - d)
    (α.homPlus.map (derivedPushforwardPlus (j ≫ toSpec A ι) ⋙ DerivedCategory.Plus.ι))
    (β.homPlus.map (derivedPushforwardPlus (j ≫ toSpec A ι) ⋙ DerivedCategory.Plus.ι))
    (restrictionSerreMap A ι j n en N W d c hc E W 0 (Ext.mk₀ (𝟙 W)))
    (by omega) (by omega) (by omega)

end OriginalSerre

/-- A fully faithful additive shift-compatible functor transports original shifted arrows. -/
public def restrictionShiftedHomEquiv
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    (G : C ⥤ D) [G.Additive] [G.Full] [G.Faithful] [G.CommShift ℤ]
    (K L : C) (s : ℤ) : ShiftedHom K L s ≃+ ShiftedHom (G.obj K) (G.obj L) s where
  toFun f := f.map G
  invFun g := G.preimage (g ≫ (G.commShiftIso s).inv.app L)
  left_inv f := by
    change G.preimage ((G.map f ≫ (G.commShiftIso s).hom.app L) ≫
      (G.commShiftIso s).inv.app L) = f
    rw [Category.assoc, Iso.hom_inv_id_app]
    change G.preimage (G.map f ≫ 𝟙 (G.obj (L⟦s⟧))) = f
    rw [Category.comp_id, Functor.preimage_map]
  right_inv g := by
    change G.map (G.preimage (g ≫ (G.commShiftIso s).inv.app L)) ≫
      (G.commShiftIso s).hom.app L = g
    rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
    change g ≫ 𝟙 ((G.obj L)⟦s⟧) = g
    exact Category.comp_id g
  map_add' f g := by simp only [ShiftedHom.map, Functor.map_add, Preadditive.add_comp]

private theorem restrictionShiftedHomEquiv_apply
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    (G : C ⥤ D) [G.Additive] [G.Full] [G.Faithful] [G.CommShift ℤ]
    (K L : C) (s : ℤ) (f : ShiftedHom K L s) :
    restrictionShiftedHomEquiv G K L s f = f.map G := rfl

/-- Transport original arrows through the specified source and target isomorphisms. -/
public def restrictionHomIsoEquiv {C : Type*} [Category* C] [Preadditive C]
    {K K' L L' : C} (e : K ≅ K') (d : L ≅ L') : (K ⟶ L) ≃+ (K' ⟶ L') where
  toFun f := e.inv ≫ f ≫ d.hom
  invFun g := e.hom ≫ g ≫ d.inv
  left_inv f := by simp only [Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]
  right_inv g := by simp only [Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]
  map_add' f g := by simp only [Preadditive.comp_add, Preadditive.add_comp]

/-- The additive arrow equivalence of a specified bijective functor map. -/
public def restrictionFunctorHomEquiv
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (K L : C)
    (hF : Function.Bijective (F.map (X := K) (Y := L))) :
    (K ⟶ L) ≃+ (F.obj K ⟶ F.obj L) where
  toFun f := F.map f
  invFun := (Equiv.ofBijective (F.map (X := K) (Y := L)) hF).symm
  left_inv := (Equiv.ofBijective (F.map (X := K) (Y := L)) hF).left_inv
  right_inv := (Equiv.ofBijective (F.map (X := K) (Y := L)) hF).right_inv
  map_add' _ _ := F.map_add

/-- Transport shifted arrows through the original functors and specified comparison isomorphisms. -/
public def restrictionHomTransportEquiv
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (U : C ⥤ C') (F : C ⥤ D) (V : D ⥤ D')
    [U.Additive] [U.Full] [U.Faithful] [U.CommShift ℤ]
    [F.Additive] [F.CommShift ℤ]
    [V.Additive] [V.Full] [V.Faithful] [V.CommShift ℤ]
    (K L : C) (H T : D') (s : ℤ)
    (hF : Function.Bijective (F.map (X := K) (Y := L⟦s⟧)))
    (e : H ≅ V.obj (F.obj K)) (d : V.obj (F.obj L) ≅ T) :
    ShiftedHom (U.obj K) (U.obj L) s ≃+ ShiftedHom H T s :=
  (restrictionShiftedHomEquiv U K L s).symm.trans
    ((restrictionFunctorHomEquiv F K (L⟦s⟧) hF).trans
      ((restrictionPostcompEquiv (F.obj K) ((F.commShiftIso s).app L)).trans
        ((restrictionShiftedHomEquiv V (F.obj K) (F.obj L) s).trans
          (restrictionHomIsoEquiv e.symm ((shiftFunctor D' s).mapIso d)))))

private theorem restrictionHomTransportEquiv_apply
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (U : C ⥤ C') (F : C ⥤ D) (V : D ⥤ D')
    [U.Additive] [U.Full] [U.Faithful] [U.CommShift ℤ]
    [F.Additive] [F.CommShift ℤ]
    [V.Additive] [V.Full] [V.Faithful] [V.CommShift ℤ]
    (K L : C) (H T : D') (s : ℤ)
    (hF : Function.Bijective (F.map (X := K) (Y := L⟦s⟧)))
    (e : H ≅ V.obj (F.obj K)) (d : V.obj (F.obj L) ≅ T)
    (f : ShiftedHom (U.obj K) (U.obj L) s) :
    restrictionHomTransportEquiv U F V K L H T s hF e d f =
      e.hom ≫ ((restrictionShiftedHomEquiv U K L s).symm f).map (F ⋙ V) ≫ d.hom⟦s⟧' := by
  change e.hom ≫ ShiftedHom.map
      (show ShiftedHom (F.obj K) (F.obj L) s from
        F.map ((restrictionShiftedHomEquiv U K L s).symm f) ≫
          (F.commShiftIso s).hom.app L) V ≫ d.hom⟦s⟧' = _
  simp only [ShiftedHom.map, Functor.map_comp, Functor.comp_map,
    Functor.commShiftIso_comp_hom_app, Category.assoc]

private theorem restrictionShiftedHomEquiv_symm_comp
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    (G : C ⥤ D) [G.Additive] [G.Full] [G.Faithful] [G.CommShift ℤ]
    {K K' L : C} {a b c : ℤ}
    (α : ShiftedHom (G.obj K) (G.obj K') a)
    (β : ShiftedHom (G.obj K') (G.obj L) b) (h : b + a = c) :
    (restrictionShiftedHomEquiv G K L c).symm (α.comp β h) =
      ((restrictionShiftedHomEquiv G K K' a).symm α).comp
        ((restrictionShiftedHomEquiv G K' L b).symm β) h := by
  apply (restrictionShiftedHomEquiv G K L c).injective
  rw [AddEquiv.apply_symm_apply, restrictionShiftedHomEquiv_apply, ShiftedHom.map_comp]
  rw [← restrictionShiftedHomEquiv_apply, AddEquiv.apply_symm_apply,
    ← restrictionShiftedHomEquiv_apply, AddEquiv.apply_symm_apply]

private theorem restriction_map_bijective_target_iso
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    (K : C) {L L' : C} (e : L ≅ L')
    (hf : Function.Bijective (F.map (X := K) (Y := L))) :
    Function.Bijective (F.map (X := K) (Y := L')) := by
  let E : (K ⟶ L') ≃ (F.obj K ⟶ F.obj L') :=
    (Iso.homCongr (Iso.refl K) e.symm).trans
      ((Equiv.ofBijective (F.map (X := K) (Y := L)) hf).trans
        (Iso.homCongr (Iso.refl (F.obj K)) (F.mapIso e)))
  have he (f : K ⟶ L') : E f = F.map f := by
    change (𝟙 _) ≫ F.map ((𝟙 _) ≫ f ≫ e.inv) ≫ F.map e.hom = F.map f
    rw [Category.id_comp, Category.id_comp, ← F.map_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have heq : (E : (K ⟶ L') → _) = F.map := by funext f; exact he f
  rw [← heq]
  exact E.bijective

/-- The original derived comparison of a functor isomorphism commutes with shifts,
as a consequence of its original derived-unit equation. -/
public theorem restriction_derivedIso_commShift
    {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
    [Category* D] [Abelian D] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (e : F ≅ G) :
    (F.rightDerivedFunctorPlusIso e).hom.CommShift ℤ := by
  have he : (NatIso.mapCochainComplexPlus e).hom =
      NatTrans.mapCochainComplexPlus e.hom := by
    ext K i
    rfl
  let : (NatIso.mapCochainComplexPlus e).hom.CommShift ℤ := by
    rw [he]
    exact NatTrans.mapCochainComplexPlus_commShift e.hom
  let β := Functor.whiskerRight (NatIso.mapCochainComplexPlus e).hom DerivedCategory.Plus.Q ≫
    G.rightDerivedFunctorPlusUnit
  let : β.CommShift ℤ := by dsimp only [β]; infer_instance
  exact Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso C) F.rightDerivedFunctorPlusUnit β
      (F.rightDerivedFunctorPlusIso e).hom (by
        apply NatTrans.ext
        funext K
        exact F.rightDerivedFunctorPlusIso_hom_app e K)

/-- The native homology-preserving composition comparison retains the original shifts. -/
public theorem restriction_derivedComp_commShift
    {C D T : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
    [Category* D] [Abelian D] [HasDerivedCategory D] [EnoughInjectives D]
    [Category* T] [Abelian T] [HasDerivedCategory T]
    (F : C ⥤ D) (G : D ⥤ T) [F.Additive] [G.Additive] [G.PreservesHomology] :
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.CommShift ℤ := by
  let β := Functor.rightDerivedFunctorPlusCompUnit F G
  let : β.CommShift ℤ := by
    dsimp only [β, Functor.rightDerivedFunctorPlusCompUnit]
    infer_instance
  exact Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso C) (F ⋙ G).rightDerivedFunctorPlusUnit β
      (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom (by
        apply NatTrans.ext
        funext K
        exact (rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app F G K).trans
          (Functor.rightDerivedFunctorPlusCompUnit_app F G K).symm)

/-- Postcomposition with a fixed coefficient map respects native shifted composition. -/
public theorem restriction_shifted_postcomp
    {C : Type*} [Category* C] [HasShift C ℤ] {K L T T' : C}
    {a b c : ℤ} (α : ShiftedHom K L a) (β : ShiftedHom L T b)
    (e : T ⟶ T') (h : b + a = c) :
    (α.comp β h) ≫ e⟦c⟧' = α.comp (β ≫ e⟦b⟧') h := by
  have he := (shiftFunctorAdd' C b a c h).inv.naturality e
  simpa only [ShiftedHom.comp, Functor.map_comp, Functor.comp_map, Category.assoc] using
    congrArg (fun q => α ≫ β⟦a⟧' ≫ q) he.symm

private theorem restrictionMappedConjugate_comp
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (P : B ⥤ C) (F : C ⥤ D) (G : B ⥤ D)
    [P.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
    (e : G ≅ P ⋙ F) [e.hom.CommShift ℤ]
    {X Y : B} {L : C} {L' : D} {a b c : ℤ}
    (α : ShiftedHom X Y a) (β : ShiftedHom (P.obj Y) L b)
    (d : F.obj L ⟶ L') (h : b + a = c) :
    e.hom.app X ≫ ((α.map P).comp β h).map F ≫ d⟦c⟧' =
      (α.map G).comp (e.hom.app Y ≫ β.map F ≫ d⟦b⟧') h := by
  have hn := ShiftedHom.map_naturality α e.hom
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hn
  have hp : e.hom.app X ≫ (α.map (P ⋙ F)).comp (β.map F) h =
      (α.map G).comp (e.hom.app Y ≫ β.map F) h := by
    simpa only [ShiftedHom.comp, Functor.map_comp, Category.assoc] using
      congrArg (fun q => q ≫ (β.map F)⟦a⟧' ≫
        (shiftFunctorAdd' D b a c h).inv.app (F.obj L)) hn.symm
  rw [ShiftedHom.map_comp, ← ShiftedHom.comp_map]
  calc
    _ = ((α.map G).comp (e.hom.app Y ≫ β.map F) h) ≫ d⟦c⟧' := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ d⟦c⟧') hp
    _ = _ := by
      simpa only [Category.assoc] using
        restriction_shifted_postcomp (α.map G) (e.hom.app Y ≫ β.map F) d h

private theorem restrictionWhiskeredComposition_commShift
    {B C D E : Type*} [Category* B] [Category* C] [Category* D] [Category* E]
    [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (P : B ⥤ C) (G : B ⥤ D) (H H' : C ⥤ D) (J : D ⥤ E)
    [P.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [H'.CommShift ℤ] [J.CommShift ℤ]
    (a : G ≅ P ⋙ H) (b : H ≅ H')
    (ha : a.hom.CommShift ℤ) (hb : b.hom.CommShift ℤ) :
    ((Functor.isoWhiskerRight (a ≪≫ Functor.isoWhiskerLeft P b) J) ≪≫
      Functor.associator P H' J).hom.CommShift ℤ := by
  let : a.hom.CommShift ℤ := ha
  let : b.hom.CommShift ℤ := hb
  rw [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

private theorem restrictionHomTransportEquiv_comp
    {B C D C' D' : Type*}
    [Category* B] [Category* C] [Category* D] [Category* C'] [Category* D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    (P : B ⥤ C) (G : B ⥤ D') (U : C ⥤ C') (F : C ⥤ D) (V : D ⥤ D')
    [P.CommShift ℤ] [G.CommShift ℤ]
    [U.Additive] [U.Full] [U.Faithful] [U.CommShift ℤ]
    [F.Additive] [F.CommShift ℤ]
    [V.Additive] [V.Full] [V.Faithful] [V.CommShift ℤ]
    (e : G ≅ P ⋙ F ⋙ V) [e.hom.CommShift ℤ]
    {M M' : B} (L : C) (T : D') (d : V.obj (F.obj L) ≅ T)
    {a b c : ℤ}
    (hF : Function.Bijective (F.map (X := P.obj M) (Y := L⟦c⟧)))
    (hF' : Function.Bijective (F.map (X := P.obj M') (Y := L⟦b⟧)))
    (α : ShiftedHom M M' a) (f : ShiftedHom (U.obj (P.obj M')) (U.obj L) b)
    (h : b + a = c) :
    restrictionHomTransportEquiv U F V (P.obj M) L (G.obj M) T c hF (e.app M) d
        ((α.map (P ⋙ U)).comp f h) =
      (α.map G).comp
        (restrictionHomTransportEquiv U F V (P.obj M') L (G.obj M') T b hF'
          (e.app M') d f) h := by
  let v := (restrictionShiftedHomEquiv U (P.obj M') L b).symm f
  have hα : (restrictionShiftedHomEquiv U (P.obj M) (P.obj M') a).symm
      (α.map (P ⋙ U)) = α.map P := by
    apply (restrictionShiftedHomEquiv U (P.obj M) (P.obj M') a).injective
    rw [AddEquiv.apply_symm_apply, restrictionShiftedHomEquiv_apply]
    exact ShiftedHom.comp_map α P U
  have hlift : (restrictionShiftedHomEquiv U (P.obj M) L c).symm
      ((α.map (P ⋙ U)).comp f h) = (α.map P).comp v h :=
    (restrictionShiftedHomEquiv_symm_comp U (α.map (P ⋙ U)) f h).trans
      (congrArg (fun z => z.comp v h) hα)
  rw [restrictionHomTransportEquiv_apply, restrictionHomTransportEquiv_apply, hlift]
  exact restrictionMappedConjugate_comp P (F ⋙ V) G e α v d.hom h

section AffineSections

variable {A : CommRingCat.{u}} {Z : Scheme.{u}}
  (p : Z ⟶ Spec A) [QuasiCompact p] [QuasiSeparated p]

/-- Actual derived module sections along the original structural scalar map. -/
public abbrev restrictionDerivedSections :
    DerivedCategory.Plus Z.Modules ⥤ DerivedCategory.Plus (ModuleCat.{u} A) :=
  (moduleGlobalSectionsFunctorOfHom Z
    (p.appTop.hom.comp (ΓSpecIso A).inv.hom)).rightDerivedFunctorPlus

/-- Compare actual derived sections with structural pushforward followed by affine sections. -/
public def restrictionAffineSectionsIso :
    restrictionDerivedSections p ≅ derivedPushforwardPlus p ⋙
      (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus :=
  moduleDerivedGlobalSectionsPushforwardCompIso p (ΓSpecIso A).inv.hom ≪≫
    Functor.isoWhiskerLeft (derivedPushforwardPlus p)
      ((moduleGlobalSectionsFunctorOfHom (Spec A) (ΓSpecIso A).inv.hom).rightDerivedFunctorPlusIso
        (moduleAffineGlobalSectionsIso A).symm)

/-- Identify the actual derived affine sections of an acyclic single coefficient sheaf. -/
public def restrictionAffineCoefficientIso (N : (Spec A).Modules) [N.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
        ((moduleSpecΓFunctor (R := A)).obj N) :=
  (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlusSingleIsoOfAcyclic N
    (AffineDerived.isZero_rightDerived_globalSections_succ N)

/-- Actual affine derived sections are bijective on the original coefficient-valued
shifted arrows. -/
public theorem restrictionAffineSections_map_bijective
    (M : Z.Modules) [M.IsQuasicoherent] (N : (Spec A).Modules) [N.IsQuasicoherent]
    (s : ℤ) :
    let F := (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus
    let K := (derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)
    let L := (DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N
    Function.Bijective (F.map (X := K) (Y := L⟦s⟧)) := by
  let F := (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus
  let K := (derivedPushforwardPlus p).obj
    ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)
  let L := (DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N
  by_cases hs : 0 ≤ s
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hs
    exact moduleSpecDerivedPushforwardSectionsHom_bijective p M N 0 r
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -s by omega)
    let Ln := (DerivedCategory.Plus.singleFunctor (Spec A).Modules (n : ℤ)).obj N
    let U : DerivedCategory.Plus (Spec A).Modules ⥤ DerivedCategory (Spec A).Modules :=
      DerivedCategory.Plus.ι
    let FF := Functor.FullyFaithful.ofFullyFaithful U
    let e : Ln⟦(0 : ℤ)⟧ ≅ L⟦s⟧ := FF.preimageIso
      ((U.commShiftIso (0 : ℤ)).app Ln ≪≫
        (singleReindexIso N n 0 s (by omega)).symm ≪≫
        ((U.commShiftIso s).app L).symm)
    exact restriction_map_bijective_target_iso F K e
      (moduleSpecDerivedPushforwardSectionsHom_bijective p M N n 0)

/-- The original derived-sections comparison after full derived-category inclusion. -/
public def restrictionAffineFullSectionsIso :
    restrictionDerivedSections p ⋙ DerivedCategory.Plus.ι ≅
      derivedPushforwardPlus p ⋙ (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι :=
  Functor.isoWhiskerRight (restrictionAffineSectionsIso p) DerivedCategory.Plus.ι ≪≫
    Functor.associator _ _ _

/-- The actual affine coefficient comparison in the full derived module category. -/
public def restrictionAffineFullCoefficientIso (N : (Spec A).Modules) [N.IsQuasicoherent] :
    DerivedCategory.Plus.ι.obj ((moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N)) ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((moduleSpecΓFunctor (R := A)).obj N) :=
  DerivedCategory.Plus.ι.mapIso (restrictionAffineCoefficientIso N) ≪≫
    (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} A) 0).app
      ((moduleSpecΓFunctor (R := A)).obj N)

/-- The original affine derived-sections equivalence on coefficient-valued shifted arrows. -/
public def restrictionAffineHomEquiv
    (M : Z.Modules) [M.IsQuasicoherent] (N : (Spec A).Modules) [N.IsQuasicoherent]
    (s : ℤ) :
    ShiftedHom (DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)))
        ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N) s ≃+
      ShiftedHom (DerivedCategory.Plus.ι.obj ((restrictionDerivedSections p).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((moduleSpecΓFunctor (R := A)).obj N)) s :=
  restrictionHomTransportEquiv
    (DerivedCategory.Plus.ι : DerivedCategory.Plus (Spec A).Modules ⥤
      DerivedCategory (Spec A).Modules)
    (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus
    (DerivedCategory.Plus.ι : DerivedCategory.Plus (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A))
    ((derivedPushforwardPlus p).obj ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M))
    ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N)
    (DerivedCategory.Plus.ι.obj ((restrictionDerivedSections p).obj
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((moduleSpecΓFunctor (R := A)).obj N)) s
    (restrictionAffineSections_map_bijective p M N s)
    ((restrictionAffineFullSectionsIso p).app
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M))
    (restrictionAffineFullCoefficientIso N)

private theorem restrictionSectionsComposition_commShift
    {B : Type u} [CommRing B] {Y T : Scheme.{u}} (g : Y ⟶ T)
    (α : B →+* Γ(T, ⊤)) :
    (moduleDerivedGlobalSectionsPushforwardCompIso g α).hom.CommShift ℤ := by
  let F := moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)
  let G := Scheme.Modules.pushforward g
  let H := moduleGlobalSectionsFunctorOfHom T α
  let β := Functor.whiskerRight
      (NatTrans.mapCochainComplexPlus (modulePushforwardGlobalSectionsIso g α).inv)
        DerivedCategory.Plus.Q ≫
    Functor.rightDerivedFunctorPlusCompUnit G H
  let : β.CommShift ℤ := by dsimp only [β]; infer_instance
  exact Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso Y.Modules) F.rightDerivedFunctorPlusUnit β
      (moduleDerivedGlobalSectionsPushforwardCompIso g α).hom (by
        apply NatTrans.ext
        funext K
        exact moduleDerivedGlobalSectionsPushforwardCompIso_unit g α K)

omit [QuasiCompact p] [QuasiSeparated p] in
private theorem restrictionAffineFullSectionsIso_commShift :
    (restrictionAffineFullSectionsIso p).hom.CommShift ℤ := by
  have ha : (moduleDerivedGlobalSectionsPushforwardCompIso p
      (ΓSpecIso A).inv.hom).hom.CommShift ℤ :=
    restrictionSectionsComposition_commShift p (ΓSpecIso A).inv.hom
  have hb :
      ((moduleGlobalSectionsFunctorOfHom (Spec A) (ΓSpecIso A).inv.hom).rightDerivedFunctorPlusIso
      (moduleAffineGlobalSectionsIso A).symm).hom.CommShift ℤ :=
    restriction_derivedIso_commShift _ _ (moduleAffineGlobalSectionsIso A).symm
  exact restrictionWhiskeredComposition_commShift (derivedPushforwardPlus p)
    (restrictionDerivedSections p)
    (moduleGlobalSectionsFunctorOfHom (Spec A) (ΓSpecIso A).inv.hom).rightDerivedFunctorPlus
    (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus
    (DerivedCategory.Plus.ι : DerivedCategory.Plus (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A))
    (moduleDerivedGlobalSectionsPushforwardCompIso p (ΓSpecIso A).inv.hom)
    ((moduleGlobalSectionsFunctorOfHom (Spec A) (ΓSpecIso A).inv.hom).rightDerivedFunctorPlusIso
      (moduleAffineGlobalSectionsIso A).symm) ha hb

private theorem restrictionAffineHomEquiv_comp
    {M M' : Z.Modules} [M.IsQuasicoherent] [M'.IsQuasicoherent]
    (N : (Spec A).Modules) [N.IsQuasicoherent] {a : ℕ} {s t : ℤ}
    (α : Ext.{u + 1} M M' a)
    (f : ShiftedHom (DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M')))
        ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N) s)
    (h : s + (a : ℤ) = t) :
    restrictionAffineHomEquiv p M N t
        ((α.homPlus.map (derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι)).comp f h) =
      (α.homPlus.map (restrictionDerivedSections p ⋙ DerivedCategory.Plus.ι)).comp
        (restrictionAffineHomEquiv p M' N s f) h := by
  let : (restrictionAffineFullSectionsIso p).hom.CommShift ℤ :=
    restrictionAffineFullSectionsIso_commShift p
  exact restrictionHomTransportEquiv_comp (derivedPushforwardPlus p)
    (restrictionDerivedSections p ⋙ DerivedCategory.Plus.ι)
    (DerivedCategory.Plus.ι : DerivedCategory.Plus (Spec A).Modules ⥤
      DerivedCategory (Spec A).Modules)
    (moduleSpecΓFunctor (R := A)).rightDerivedFunctorPlus
    (DerivedCategory.Plus.ι : DerivedCategory.Plus (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A))
    (restrictionAffineFullSectionsIso p)
    ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((moduleSpecΓFunctor (R := A)).obj N)) (restrictionAffineFullCoefficientIso N)
    (restrictionAffineSections_map_bijective p M N t)
    (restrictionAffineSections_map_bijective p M' N s) α.homPlus f h

end AffineSections

/-- Precomposition by the specified source isomorphism as an additive equivalence. -/
public def restrictionPrecompEquiv {C : Type*} [Category* C] [Preadditive C]
    {S T : C} (e : S ≅ T) (N : C) : (T ⟶ N) ≃+ (S ⟶ N) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := by simp only [Iso.inv_hom_id_assoc]
  right_inv f := by simp only [Iso.hom_inv_id_assoc]
  map_add' f g := by simp only [Preadditive.comp_add]

/-- The original spectrum/global-sections isomorphism on the structure coefficient. -/
public def restrictionSpecUnitSectionsIso (A : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := A)).obj (SheafOfModules.unit (Spec A).ringCatSheaf) ≅
      ModuleCat.of A A := by
  let E := (ΓSpecIso A).commRingCatIsoToRingEquiv
  let L : ((moduleSpecΓFunctor (R := A)).obj
      (SheafOfModules.unit (Spec A).ringCatSheaf)) ≃ₗ[A] A :=
    { __ := E.toAddEquiv
      map_smul' r x := by
        change E (E.symm r * (show Γ(Spec A, ⊤) from x)) =
          r * E (show Γ(Spec A, ⊤) from x)
        rw [map_mul, E.apply_symm_apply] }
  exact L.toModuleIso

section ModuleSerre

variable (A : Type u) [CommRing A] (ι : Type u)
  {Z : Scheme.{u}} (j : Z ⟶ ProjectiveSpace A ι) [IsClosedImmersion j]
  (n : ℕ) (en : ι ≃ Fin (n + 1))
  (N : (Spec (.of A)).Modules) [N.IsQuasicoherent]
  (V : ModuleCat.{u} A) (eV : (moduleSpecΓFunctor (R := .of A)).obj N ≅ V)
  (W : Z.Modules) (d c : ℕ) (hc : (c : ℤ) = (n : ℤ) - d)
  (E : restrictionSerreObject A ι j n N ≅
    (DerivedCategory.singleFunctor Z.Modules ((n : ℤ) - d)).obj W)

/-- The original Serre map followed by actual affine derived sections and the
specified original coefficient comparison, with integer target degree `r-d`. -/
public def restrictionModuleSerreMap (F : Z.Modules) [F.IsQuasicoherent] (r : ℕ) :
    Ext.{u + 1} F W r →+
      ShiftedHom (DerivedCategory.Plus.ι.obj
        ((restrictionDerivedSections (j ≫ toSpec A ι)).obj
          ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj F)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj V) ((r : ℤ) - d) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  exact (restrictionPostcompEquiv _
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) ((r : ℤ) - d)).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        eV))).toAddMonoidHom.comp
    ((restrictionAffineHomEquiv (j ≫ toSpec A ι) F N ((r : ℤ) - d)).toAddMonoidHom.comp
      (restrictionSerreMap A ι j n en N W d c hc E F r))

private theorem restrictionModuleSerreMap_apply (F : Z.Modules) [F.IsQuasicoherent]
    (r : ℕ) (x : Ext.{u + 1} F W r) :
    letI : Finite ι := Finite.of_equiv _ en.symm
    restrictionModuleSerreMap A ι j n en N V eV W d c hc E F r x =
      restrictionAffineHomEquiv (j ≫ toSpec A ι) F N ((r : ℤ) - d)
        (restrictionSerreMap A ι j n en N W d c hc E F r x) ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map eV.hom)⟦((r : ℤ) - d)⟧' := by
  rfl

/-- Coherent sources give bijectivity of this same original coefficient-valued map. -/
public theorem restrictionModuleSerreMap_bijective [IsNoetherianRing A]
    (F : Z.Modules) [F.IsQuasicoherent]
    (hF : QuasiCoherent.affineLocallyFiniteType Z F) (r : ℕ) :
    Function.Bijective (restrictionModuleSerreMap A ι j n en N V eV W d c hc E F r) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  exact (restrictionPostcompEquiv _
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) ((r : ℤ) - d)).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso eV))).bijective.comp
    ((restrictionAffineHomEquiv (j ≫ toSpec A ι) F N ((r : ℤ) - d)).bijective.comp
      (restrictionSerreMap_bijective A ι j n en N W d c hc E F hF r))

/-- Arbitrary source Yoneda products retain their actual derived-section images. -/
public theorem restrictionModuleSerreMap_comp
    {F F' : Z.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent] {a b r : ℕ}
    (α : Ext.{u + 1} F F' a) (x : Ext.{u + 1} F' W b) (hab : a + b = r) :
    restrictionModuleSerreMap A ι j n en N V eV W d c hc E F r (α.comp x hab) =
      (α.homPlus.map (restrictionDerivedSections (j ≫ toSpec A ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (restrictionModuleSerreMap A ι j n en N V eV W d c hc E F' b x) (by omega) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  rw [restrictionModuleSerreMap_apply, restrictionModuleSerreMap_apply,
    restrictionSerreMap_comp, restrictionAffineHomEquiv_comp]
  exact restriction_shifted_postcomp _ _
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map eV.hom) (by omega)

variable {T : Scheme.{u}} (i : T ⟶ Z) [IsClosedImmersion i]

/-- Compare the actual closed-image composite with its original structural derived image. -/
public def restrictionClosedImageIso (F : T.Modules) :
    DerivedCategory.Plus.ι.obj ((derivedPushforwardPlus (i ≫ (j ≫ toSpec A ι))).obj
      ((DerivedCategory.Plus.singleFunctor T.Modules 0).obj F)) ≅
        restrictionSerreImage A ι j ((Scheme.Modules.pushforward i).obj F) :=
  DerivedCategory.Plus.ι.mapIso (relativeClosedEmbeddingPushforwardSingleIso i (j ≫ toSpec A ι) F)

/-- The same original Serre/affine map after the specified closed-image composition. -/
public def restrictionClosedSerreMap (F : T.Modules) [F.IsQuasicoherent] (r : ℕ) :
    Ext.{u + 1} ((Scheme.Modules.pushforward i).obj F) W r →+
      ShiftedHom (DerivedCategory.Plus.ι.obj
        ((restrictionDerivedSections (i ≫ (j ≫ toSpec A ι))).obj
          ((DerivedCategory.Plus.singleFunctor T.Modules 0).obj F)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj V) ((r : ℤ) - d) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  exact (restrictionPostcompEquiv _
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) ((r : ℤ) - d)).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        eV))).toAddMonoidHom.comp
    ((restrictionAffineHomEquiv (i ≫ (j ≫ toSpec A ι)) F N ((r : ℤ) - d)).toAddMonoidHom.comp
      ((restrictionPrecompEquiv (restrictionClosedImageIso A ι j i F) _).toAddMonoidHom.comp
        (restrictionSerreMap A ι j n en N W d c hc E ((Scheme.Modules.pushforward i).obj F) r)))

private theorem restrictionClosedSerreMap_apply (F : T.Modules) [F.IsQuasicoherent]
    (r : ℕ) (x : Ext.{u + 1} ((Scheme.Modules.pushforward i).obj F) W r) :
    letI : Finite ι := Finite.of_equiv _ en.symm
    restrictionClosedSerreMap A ι j n en N V eV W d c hc E i F r x =
      restrictionAffineHomEquiv (i ≫ (j ≫ toSpec A ι)) F N ((r : ℤ) - d)
        ((restrictionClosedImageIso A ι j i F).hom ≫
          restrictionSerreMap A ι j n en N W d c hc E ((Scheme.Modules.pushforward i).obj F) r x) ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map eV.hom)⟦((r : ℤ) - d)⟧' := by
  rfl

/-- Original finite pushforward and coherent Serre duality give bijectivity. -/
public theorem restrictionClosedSerreMap_bijective [IsNoetherianRing A]
    (F : T.Modules) [F.IsQuasicoherent]
    (hF : QuasiCoherent.affineLocallyFiniteType T F) (r : ℕ) :
    Function.Bijective (restrictionClosedSerreMap A ι j n en N V eV W d c hc E i F r) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  exact (restrictionPostcompEquiv _
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) ((r : ℤ) - d)).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso eV))).bijective.comp
    ((restrictionAffineHomEquiv (i ≫ (j ≫ toSpec A ι)) F N ((r : ℤ) - d)).bijective.comp
      ((restrictionPrecompEquiv (restrictionClosedImageIso A ι j i F) _).bijective.comp
        (restrictionSerreMap_bijective A ι j n en N W d c hc E
          ((Scheme.Modules.pushforward i).obj F)
          (QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward i hF) r)))

/-- The original closed-image, affine and Serre comparisons preserve source Ext products. -/
public theorem restrictionClosedSerreMap_comp
    {F F' : T.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent] {a b r : ℕ}
    (α : Ext.{u + 1} F F' a)
    (x : Ext.{u + 1} ((Scheme.Modules.pushforward i).obj F') W b) (hab : a + b = r) :
    restrictionClosedSerreMap A ι j n en N V eV W d c hc E i F r
        ((α.mapExactFunctor (Scheme.Modules.pushforward i)).comp x hab) =
      (α.homPlus.map (restrictionDerivedSections (i ≫ (j ≫ toSpec A ι)) ⋙
        DerivedCategory.Plus.ι)).comp
        (restrictionClosedSerreMap A ι j n en N V eV W d c hc E i F' b x) (by omega) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  have hC := relativeClosedEmbeddingPushforwardSingleIso_ext_naturality i (j ≫ toSpec A ι) α
  have hinput : (restrictionClosedImageIso A ι j i F).hom ≫
      (((α.mapExactFunctor (Scheme.Modules.pushforward i)).homPlus.map
        (derivedPushforwardPlus (j ≫ toSpec A ι) ⋙ DerivedCategory.Plus.ι)).comp
          (c := (r : ℤ) - d)
          (restrictionSerreMap A ι j n en N W d c hc E
            ((Scheme.Modules.pushforward i).obj F') b x) (by omega)) =
      (α.homPlus.map (derivedPushforwardPlus (i ≫ (j ≫ toSpec A ι)) ⋙
        DerivedCategory.Plus.ι)).comp (c := (r : ℤ) - d)
        ((restrictionClosedImageIso A ι j i F').hom ≫
          restrictionSerreMap A ι j n en N W d c hc E
            ((Scheme.Modules.pushforward i).obj F') b x) (by omega) := by
    simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
    simpa only [restrictionClosedImageIso, Functor.mapIso_hom, Category.assoc] using
      congrArg (fun f => f ≫
        (restrictionSerreMap A ι j n en N W d c hc E
          ((Scheme.Modules.pushforward i).obj F') b x)⟦(a : ℤ)⟧' ≫
          (shiftFunctorAdd' (DerivedCategory (Spec (.of A)).Modules)
            ((b : ℤ) - d) (a : ℤ) ((r : ℤ) - d) (by omega)).inv.app
              ((DerivedCategory.singleFunctor (Spec (.of A)).Modules 0).obj N)) hC
  rw [restrictionClosedSerreMap_apply, restrictionClosedSerreMap_apply,
    restrictionSerreMap_comp, hinput, restrictionAffineHomEquiv_comp]
  exact restriction_shifted_postcomp _ _
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map eV.hom) (by omega)

end ModuleSerre

end AlgebraicGeometry.Scheme.Cohomology
