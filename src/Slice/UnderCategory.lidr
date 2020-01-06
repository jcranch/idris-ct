\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2020 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

An \emph{undercategory} is the category of morphisms from a fixed
object in a category.

> module Slice.UnderCategory
>
> import Basic.Category
> import Utils
>
> %access public export
> %default total
>
>
> record UnderObject
>   (cat : Category)
>   (a : obj cat)
>   where
>     constructor MkUnderObject
>     ObjUnder : obj cat
>     morUnder : mor cat a ObjUnder
>
> record UnderMorphism
>   (cat : Category)
>   (a : obj cat)
>   (f : UnderObject cat a)
>   (g : UnderObject cat a)
>   where
>     constructor MkUnderMorphism
>     HomUnder : mor cat (ObjUnder f) (ObjUnder g)
>     triUnder : compose cat a (ObjUnder f) (ObjUnder g) (morUnder f) HomUnder = morUnder g
>
> UnderMorphismEqual : {f, g : UnderObject cat a} -> (u, v : UnderMorphism cat a f g) -> (HomUnder u = HomUnder v) -> (u = v)
> UnderMorphismEqual {cat} {a} {f} {g} (MkUnderMorphism u r) (MkUnderMorphism u s) Refl = cong {f = MkUnderMorphism u} (equalitiesEqual _ _)
>
> UnderIdentity : (f : UnderObject cat a) -> UnderMorphism cat a f f
> UnderIdentity {cat} {a} f = MkUnderMorphism (identity cat (ObjUnder f)) (rightIdentity cat a (ObjUnder f) (morUnder f))
>
> UnderCompose :
>      (f, g, h : UnderObject cat a)
>   -> (u : UnderMorphism cat a f g)
>   -> (v : UnderMorphism cat a g h)
>   -> UnderMorphism cat a f h
> UnderCompose {cat} {a} f g h u v = MkUnderMorphism
>   (compose cat (ObjUnder f) (ObjUnder g) (ObjUnder h) (HomUnder u) (HomUnder v))
>   (trans
>     (associativity cat
>       a (ObjUnder f) (ObjUnder g) (ObjUnder h)
>       (morUnder f) (HomUnder u) (HomUnder v))
>     (trans
>       (cong2 {f = compose cat a (ObjUnder g) (ObjUnder h)} (triUnder u) Refl)
>       (triUnder v)))
>
>
> UnderLeftIdentity :
>      (f, g : UnderObject cat a)
>   -> (u : UnderMorphism cat a f g)
>   -> UnderCompose f f g (UnderIdentity f) u = u
> UnderLeftIdentity {cat} _ _ _ = UnderMorphismEqual _ _ (leftIdentity cat _ _ _)
>
> UnderRightIdentity :
>      (f, g : UnderObject cat a)
>   -> (u : UnderMorphism cat a f g)
>   -> UnderCompose f g g u (UnderIdentity g) = u
> UnderRightIdentity {cat} _ _ _ = UnderMorphismEqual _ _ (rightIdentity cat _ _ _)
>
> UnderAssociativity :
>      (f, g, h, i : UnderObject cat a)
>   -> (u : UnderMorphism cat a f g)
>   -> (v : UnderMorphism cat a g h)
>   -> (w : UnderMorphism cat a h i)
>   -> UnderCompose f g i u (UnderCompose g h i v w) = UnderCompose f h i (UnderCompose f g h u v) w
> UnderAssociativity {cat} {a} _ _ _ _ _ _ _ = UnderMorphismEqual _ _ (associativity cat _ _ _ _ _ _ _)
>
> UnderCategory : (cat : Category) -> (a : obj cat) -> Category
> UnderCategory cat a = MkCategory
>   (UnderObject cat a)
>   (UnderMorphism cat a)
>   (UnderIdentity {cat} {a})
>   (UnderCompose {cat} {a})
>   (UnderLeftIdentity {cat} {a})
>   (UnderRightIdentity {cat} {a})
>   (UnderAssociativity {cat} {a})
