/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.KillSmallMaps.IndexFunctor

/-!
# The genuine functorial all-maps attachment

The map is the native pushout map induced by postcomposition on all original
maps and the native identity-cone functor. Identity, composition and naturality
hold for the original attachment and its original inclusion.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ)
  {K L M : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
/-- The native map of the original all-maps pushout attachments. -/
def killAllMapsMap (f : K ⟶ L) : killAllMapsAttachment A K ⟶ killAllMapsAttachment A L :=
  pushout.map _ _ _ _ f (identityConeFunctor.map (killAllMapsCoproductMap A f))
    (killAllMapsCoproductMap A f) (killAllMapsCoproductMap_evaluation A f).symm
    (by simp [identityConeFunctor, mappingCone.map])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma killAllMapsι_map (f : K ⟶ L) :
    killAllMapsι A K ≫ killAllMapsMap A f = f ≫ killAllMapsι A L := by
  simp [killAllMapsMap, killAllMapsι, killSmallMapsι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma killAllMapsConeMap_map (f : K ⟶ L) :
    killSmallMapsConeMap (killAllMapsSources A K) (killAllMapsEvaluation A K) ≫
      killAllMapsMap A f = identityConeFunctor.map (killAllMapsCoproductMap A f) ≫
        killSmallMapsConeMap (killAllMapsSources A L) (killAllMapsEvaluation A L) := by
  simp [killAllMapsMap, killSmallMapsConeMap]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma killAllMapsMap_id (K : CochainComplex C ℤ) :
    killAllMapsMap A (𝟙 K) = 𝟙 (killAllMapsAttachment A K) := by
  apply pushout.hom_ext
  · change killAllMapsι A K ≫ killAllMapsMap A (𝟙 K) = killAllMapsι A K ≫ 𝟙 _
    simp
  · change killSmallMapsConeMap _ _ ≫ killAllMapsMap A (𝟙 K) =
      killSmallMapsConeMap _ _ ≫ 𝟙 _
    simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma killAllMapsMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    killAllMapsMap A (f ≫ g) = killAllMapsMap A f ≫ killAllMapsMap A g := by
  apply pushout.hom_ext
  · change killAllMapsι A K ≫ killAllMapsMap A (f ≫ g) =
      killAllMapsι A K ≫ (killAllMapsMap A f ≫ killAllMapsMap A g)
    simp
  · change killSmallMapsConeMap _ _ ≫ killAllMapsMap A (f ≫ g) =
      killSmallMapsConeMap _ _ ≫ (killAllMapsMap A f ≫ killAllMapsMap A g)
    simp [Functor.map_comp]

/-- The actual all-maps attachment is a functor, with no replacement premise. -/
def killAllMapsFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := killAllMapsAttachment A K
  map f := killAllMapsMap A f
  map_id := killAllMapsMap_id A
  map_comp := killAllMapsMap_comp A

/-- The original all-maps inclusion is natural. -/
def killAllMapsUnit : 𝟭 (CochainComplex C ℤ) ⟶ killAllMapsFunctor A where
  app K := killAllMapsι A K
  naturality _ _ f := (killAllMapsι_map A f).symm

instance killAllMapsUnit_mono (K : CochainComplex C ℤ) :
    Mono ((killAllMapsUnit A).app K) := inferInstanceAs (Mono (killAllMapsι A K))

/-- The original natural unit is a quasi-isomorphism for an acyclic family. -/
lemma killAllMapsUnit_quasiIso (hA : ∀ i, (A i).Acyclic) (K : CochainComplex C ℤ) :
    QuasiIso ((killAllMapsUnit A).app K) := killAllMapsι_quasiIso A K hA

end CochainComplex
