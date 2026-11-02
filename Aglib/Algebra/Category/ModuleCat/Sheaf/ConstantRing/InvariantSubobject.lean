/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InvariantSections
public import Aglib.CategoryTheory.Adjunction.UnitHomMap
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Actual invariant subobjects and their original quotient comparisons

The original fixed-image section map is amalgamated on its actual cover and
transposed by the native constant adjunction. Original image/unit and section
comparisons determine its complete pullback equation, monomorphism reflection,
and literal cokernel/projection comparison. The overlap condition is the one
proved by native graph-cover separatedness in `InvariantSections`; no desired
map or pullback equation is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf.ConstantRing

universe u v r w g a b

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R : Type r} [CommRing R] (F : Sheaf J (ModuleCat.{w} R))
  {T U V : C} {G : Type g} [Group G] (action : G →* Aut U)
  (q : U ⟶ T) (hq : Sieve.ofArrows (fun _ : Unit => U) (fun _ => q) ∈ J T)
  (p₁ p₂ : V ⟶ U) (hp : IsPullback p₁ p₂ q q)
  (overlap : ∀ {E : ModuleCat.{w} R} (z : E ⟶ F.obj.obj (op U)),
    (∀ σ : G, z ≫ F.obj.map (action σ).hom.op = z) →
      z ≫ F.obj.map p₁.op = z ≫ F.obj.map p₂.op)
  {M N : ModuleCat.{w} R} (sectionIso : M ≅ F.obj.obj (op U)) (i : N ⟶ M)
  (hi : ∀ (σ : G) (x : N),
    Presheaf.transportedRestrictionRepresentation F.obj action sectionIso σ (i x) = i x)

/-- Native amalgamation of exactly the supplied fixed-image section map. -/
def invariantSubobjectSection : N ⟶ F.obj.obj (op T) :=
  invariantSectionDescend F action q hq p₁ p₂ hp overlap (i ≫ sectionIso.hom)
    (Presheaf.transportedRestrictionRepresentation_fixed F.obj action sectionIso i hi)

/-- The actual descended fixed-image map restricts to the original section map. -/
@[reassoc (attr := simp)]
theorem invariantSubobjectSection_restriction :
    invariantSubobjectSection J F action q hq p₁ p₂ hp overlap sectionIso i hi ≫
      F.obj.map q.op = i ≫ sectionIso.hom :=
  invariantSectionDescend_restriction F action q hq p₁ p₂ hp overlap
    (i ≫ sectionIso.hom)
    (Presheaf.transportedRestrictionRepresentation_fixed F.obj action sectionIso i hi)

variable (hT : IsTerminal T) [HasWeakSheafify J (ModuleCat.{w} R)]


/-- The original constant-adjunction inverse of the actual descended fixed-image map. -/
def invariantSubobjectMap : (constantSheaf J (ModuleCat.{w} R)).obj N ⟶ F :=
  ((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv N F).symm
    (invariantSubobjectSection J F action q hq p₁ p₂ hp overlap sectionIso i hi)

/-- Its actual adjoint is the original amalgamation, rather than a replacement section map. -/
theorem invariantSubobjectMap_homEquiv :
    (constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv N F
      (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT) =
        invariantSubobjectSection J F action q hq p₁ p₂ hp overlap sectionIso i hi :=
  Equiv.apply_symm_apply _ _

variable {D : Type a} [Category.{b} D]
  {P : Sheaf J (ModuleCat.{w} R) ⥤ D} {Q : D ⥤ Sheaf J (ModuleCat.{w} R)}
  {K : ModuleCat.{w} R ⥤ D} {coverSections : D ⥤ ModuleCat.{w} R}
  (imageAdjunction : P ⊣ Q) (coverAdjunction : K ⊣ coverSections)
  (rightSectionsIso : Q ⋙
    ((sheafSections J (ModuleCat.{w} R)).obj (op T)) ≅ coverSections)
  (constantIso : constantSheaf J (ModuleCat.{w} R) ⋙ P ≅ K)
  (hconstantIso : constantIso = Adjunction.leftAdjointCompIso
    (constantSheafAdj J (ModuleCat.{w} R) hT) imageAdjunction coverAdjunction rightSectionsIso)
  (trivialization : P.obj F ≅ K.obj M)
  (sectionComparison : coverSections.obj (P.obj F) ≅ F.obj.obj (op U))
  (hsectionIso : sectionIso.hom = coverAdjunction.unit.app M ≫
    coverSections.map trivialization.inv ≫ sectionComparison.hom)
  (hrestriction : imageAdjunction.unitSectionMap
    ((sheafSections J (ModuleCat.{w} R)).obj (op T)) rightSectionsIso F ≫
    sectionComparison.hom = F.obj.map q.op)

include hconstantIso hsectionIso hrestriction in
/-- The full original image of the constructed map is the literal constant map of i. -/
@[reassoc]
theorem invariantSubobjectMap_pullback :
    P.map (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT) ≫
      trivialization.hom = constantIso.hom.app N ≫ K.map i := by
  let d := invariantSubobjectSection J F action q hq p₁ p₂ hp overlap sectionIso i hi
  let r := imageAdjunction.unitSectionMap
    ((sheafSections J (ModuleCat.{w} R)).obj (op T)) rightSectionsIso F
  have hd : d ≫ r = i ≫ coverAdjunction.unit.app M ≫
      coverSections.map trivialization.inv := by
    apply (cancel_mono sectionComparison.hom).mp
    rw [Category.assoc, hrestriction, invariantSubobjectSection_restriction, hsectionIso]
    simp only [Category.assoc]
  apply (cancel_epi (constantIso.inv.app N)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  apply (coverAdjunction.homEquiv N _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  have ht : coverAdjunction.homEquiv N _
      (constantIso.inv.app N ≫ P.map
        (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT)) =
      d ≫ r :=
    (Adjunction.unitSectionMap_homEquiv (constantSheafAdj J (ModuleCat.{w} R) hT)
      imageAdjunction coverAdjunction
      rightSectionsIso constantIso hconstantIso _).trans
        (congrArg (fun z => z ≫ r)
          (invariantSubobjectMap_homEquiv J F action q hq p₁ p₂ hp overlap sectionIso i hi hT))
  rw [ht]
  change (d ≫ r) ≫ coverSections.map trivialization.hom = _
  rw [hd]
  simp only [Category.assoc, ← Functor.map_comp, trivialization.inv_hom_id,
    Adjunction.homEquiv_unit]
  rw [coverSections.map_id]
  exact (congrArg
    (fun z : M ⟶ coverSections.obj (K.obj M) => i ≫ z)
    (Category.comp_id (coverAdjunction.unit.app M))).trans
      (coverAdjunction.unit.naturality i)

include hconstantIso hsectionIso hrestriction in
/-- Original image faithfulness reflects the mono furnished by the actual constant map. -/
theorem invariantSubobjectMap_mono [P.Faithful] [K.PreservesMonomorphisms] [Mono i] :
    Mono (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT) := by
  have hm : Mono (P.map
      (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT) ≫
        trivialization.hom) := by
    rw [invariantSubobjectMap_pullback J F action q hq p₁ p₂ hp overlap sectionIso i hi hT
      imageAdjunction coverAdjunction rightSectionsIso constantIso hconstantIso trivialization
      sectionComparison hsectionIso hrestriction]
    infer_instance
  have hm' : Mono (P.map
      (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT)) :=
    mono_of_mono _ trivialization.hom
  exact P.mono_of_mono_map hm'

section Cokernel

variable [HasSheafify J (ModuleCat.{w} R)]

include hconstantIso hsectionIso hrestriction in
/-- The original map and its actual cokernel give the native short exact sequence. -/
theorem invariantSubobjectMap_shortExact [P.Faithful] [K.PreservesMonomorphisms] [Mono i] :
    (ShortComplex.cokernelSequence
      (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT)).ShortExact := by
  refine { exact := ShortComplex.cokernelSequence_exact _, mono_f := ?_ }
  exact invariantSubobjectMap_mono J F action q hq p₁ p₂ hp overlap sectionIso i hi hT
    imageAdjunction coverAdjunction rightSectionsIso constantIso hconstantIso trivialization
    sectionComparison hsectionIso hrestriction

variable [Preadditive D] [P.PreservesZeroMorphisms] [K.PreservesZeroMorphisms]

/-- The original quotient is compared through exactly the actual image and constant cokernels. -/
def invariantSubobjectCokernelIso :
    P.obj (cokernel
      (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT)) ≅
      K.obj (cokernel i) := by
  let : P.IsLeftAdjoint := imageAdjunction.isLeftAdjoint
  let : K.IsLeftAdjoint := coverAdjunction.isLeftAdjoint
  exact PreservesCokernel.iso P _ ≪≫
    cokernel.mapIso _ (K.map i) (constantIso.app N) trivialization
      (invariantSubobjectMap_pullback J F action q hq p₁ p₂ hp overlap sectionIso i hi hT
        imageAdjunction coverAdjunction rightSectionsIso constantIso hconstantIso trivialization
        sectionComparison hsectionIso hrestriction) ≪≫
      (PreservesCokernel.iso K i).symm

/-- The quotient comparison retains the literal original cokernel projection. -/
@[reassoc]
theorem invariantSubobjectCokernelIso_projection :
    P.map (cokernel.π
      (invariantSubobjectMap J F action q hq p₁ p₂ hp overlap sectionIso i hi hT)) ≫
      (invariantSubobjectCokernelIso J F action q hq p₁ p₂ hp overlap sectionIso i hi hT
        imageAdjunction coverAdjunction rightSectionsIso constantIso hconstantIso trivialization
        sectionComparison hsectionIso hrestriction).hom =
      trivialization.hom ≫ K.map (cokernel.π i) := by
  let : P.IsLeftAdjoint := imageAdjunction.isLeftAdjoint
  let : K.IsLeftAdjoint := coverAdjunction.isLeftAdjoint
  simp [invariantSubobjectCokernelIso, PreservesCokernel.iso_inv]

end Cokernel

end ModuleCat.Sheaf.ConstantRing
