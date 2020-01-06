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

An \emph{overcategory} is the category of morphisms to a fixed object
in a category.

> module Slice.OverCategory
>
> import Basic.Category
> import Utils
>
> %access public export
> %default total
>
>
> record OverObject
>   (cat : Category)
>   (a : obj cat)
>   where
>     constructor MkOverObject
>     ObjOver : obj cat
>     morOver : mor cat ObjOver a
>
> record OverMorphism
>   (cat : Category)
>   (a : obj cat)
>   (f : OverObject cat a)
>   (g : OverObject cat a)
>   where
>     constructor MkOverMorphism
>     HomOver : mor cat (ObjOver f) (ObjOver g)
>     triOver : compose cat (ObjOver f) (ObjOver g) a HomOver (morOver g) = morOver f
>
> overMorphismEqual : {f, g : OverObject cat a} -> (u, v : OverMorphism cat a f g) -> (HomOver u = HomOver v) -> (u = v)
> overMorphismEqual {cat} {a} {f} {g} (MkOverMorphism u r) (MkOverMorphism u s) Refl = cong {f = MkOverMorphism u} (equalitiesEqual _ _)
>
> overIdentity : (f : OverObject cat a) -> OverMorphism cat a f f
> overIdentity {cat} {a} f = MkOverMorphism (identity cat (ObjOver f)) (leftIdentity cat (ObjOver f) a (morOver f))
>
> overCompose :
>      (f, g, h : OverObject cat a)
>   -> (u : OverMorphism cat a f g)
>   -> (v : OverMorphism cat a g h)
>   -> OverMorphism cat a f h
> overCompose {cat} {a} f g h u v = MkOverMorphism
>   (compose cat (ObjOver f) (ObjOver g) (ObjOver h) (HomOver u) (HomOver v))
>   (trans
>     (sym (associativity cat
>            (ObjOver f) (ObjOver g) (ObjOver h) a
>            (HomOver u) (HomOver v) (morOver h)))
>       (trans
>         (cong (triOver v))
>         (triOver u)))
>
> overLeftIdentity :
>      (f, g : OverObject cat a)
>   -> (u : OverMorphism cat a f g)
>   -> overCompose f f g (overIdentity f) u = u
> overLeftIdentity {cat} _ _ _ = overMorphismEqual _ _ (leftIdentity cat _ _ _)
>
> overRightIdentity :
>      (f, g : OverObject cat a)
>   -> (u : OverMorphism cat a f g)
>   -> overCompose f g g u (overIdentity g) = u
> overRightIdentity {cat} _ _ _ = overMorphismEqual _ _ (rightIdentity cat _ _ _)
>
> overAssociativity :
>      (f, g, h, i : OverObject cat a)
>   -> (u : OverMorphism cat a f g)
>   -> (v : OverMorphism cat a g h)
>   -> (w : OverMorphism cat a h i)
>   -> overCompose f g i u (overCompose g h i v w) = overCompose f h i (overCompose f g h u v) w
> overAssociativity {cat} {a} _ _ _ _ _ _ _ = overMorphismEqual _ _ (associativity cat _ _ _ _ _ _ _)
>
> overCategory : (cat : Category) -> (a : obj cat) -> Category
> overCategory cat a = MkCategory
>   (OverObject cat a)
>   (OverMorphism cat a)
>   (overIdentity {cat} {a})
>   (overCompose {cat} {a})
>   (overLeftIdentity {cat} {a})
>   (overRightIdentity {cat} {a})
>   (overAssociativity {cat} {a})
