\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

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

> module CategoryReasoning
>
> import Basic.Category
>
> %access public export
> %default total
>
> -- Preorder reasoning syntax for morphisms in a category
> ||| Used for preorder reasoning syntax. Not intended for direct use.
> qed : (cat : Category) -> (a : obj cat) -> mor _ a a
> qed cat a = identity cat a
>
> ||| Used for preorder reasoning syntax. Not intended for direct use.
> step : (cat : Category) -> (a : obj cat) -> mor cat a b -> mor cat b c -> mor cat a c
> step cat a f g = compose _ _ _ _ f g
>
> liftEquality : (cat : Category) -> (a, b : obj cat) -> a = b -> mor cat a b
> liftEquality cat a a Refl = identity _ a
