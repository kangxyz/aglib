/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf

/-!
# Original killed abelian sheaves as genuine ZMod-valued sheaves

For every natural modulus, including zero, literal annihilation of the original
abelian sheaf identity constructs a genuine module-valued sheaf on the same
site. Its original sections, restrictions and coefficient morphisms are retained.
The canonical underlying-sheaf comparison is natural and is exposed through the
native `sheafCompose` functor with its actual preservation hypothesis.
-/
