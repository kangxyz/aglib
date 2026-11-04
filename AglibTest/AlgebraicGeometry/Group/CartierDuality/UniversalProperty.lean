/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty

/-! Affine characters and arbitrary-test character restriction retain the original groups. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped TensorProduct Module.Dual.FiniteDual
open AlgebraicGeometry.Scheme.OverField (FScheme Base)
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]
  (R : Type u) [CommRing R] [Algebra k R]

example :
    (Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) ≃
      ((Over.pullback (Spec.algebraMap k R)).mapGrp.obj G ⟶
        MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R))) :=
  affineCharacterEquiv G R

example (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    specUnitsEquiv (CommAlgCat.of R (R ⊗[k] coordinateHopf G))
        ((coordinateScalarExtensionIso G R).inv ≫ affineCharacterEquiv G R p).hom.hom =
      Units.map (Module.Dual.characterTensorHom k (coordinateHopf G) R
        (affineDualPointEquiv G R p)).toMonoidHom
          (HopfAlgebra.coevaluationUnit k (coordinateHopf G)) :=
  affineCharacterEquiv_coevaluation G R p

example :
    (Over.pullback (dualGroup G).X.hom).mapGrp.obj G ⟶
      MultiplicativeGroup.groupScheme (dualGroup G).X.left :=
  universalCharacter G

example :
    specUnitsEquiv
        (CommAlgCat.of (Dual k (coordinateHopf G))
          (Dual k (coordinateHopf G) ⊗[k] coordinateHopf G))
        ((coordinateScalarExtensionIso G (Dual k (coordinateHopf G))).inv ≫
          universalCharacter G).hom.hom =
      Units.map (Algebra.TensorProduct.comm k (coordinateHopf G)
        (Dual k (coordinateHopf G))).toAlgHom.toMonoidHom
          (HopfAlgebra.coevaluationUnit k (coordinateHopf G)) :=
  universalCharacter_coevaluation G

example (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left :=
  characterOfPoint G T p

example {T U : FScheme k} (h : U ⟶ T) (p : T ⟶ (dualGroup G).X) :
    characterOfPoint G U (h ≫ p) = restrictCharacter G h (characterOfPoint G T p) :=
  characterOfPoint_naturality G h p

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
example (T : FScheme k)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left) :
    restrictCharacter G (𝟙 T) c = c :=
  restrictCharacter_id G T c

example (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    characterOfPoint G (Over.mk (Spec.algebraMap k R)) p = affineCharacterEquiv G R p :=
  characterOfPoint_affine G R p

example : Function.Bijective (characterOfPoint G (Over.mk (Spec.algebraMap k R))) :=
  characterOfPoint_affine_bijective G R

example (T : FScheme k) :
    (T ⟶ (dualGroup G).X) ≃
      ((Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left) :=
  characterEquiv G T

example {T U : FScheme k} (h : U ⟶ T) (p : T ⟶ (dualGroup G).X) :
    characterEquiv G U (h ≫ p) = restrictCharacter G h (characterEquiv G T p) :=
  characterEquiv_naturality G h p

example (T : FScheme k)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left) :
    characterOfPoint G T ((characterEquiv G T).symm c) = c :=
  (characterEquiv G T).apply_symm_apply c

example {T U : FScheme k} (h : U ⟶ T)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left) :
    (characterEquiv G U).symm (restrictCharacter G h c) =
      h ≫ (characterEquiv G T).symm c :=
  characterEquiv_symm_naturality G h c

example : (characterFunctor G).RepresentableBy (dualGroup G).X :=
  characterRepresentableBy G
