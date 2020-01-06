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

> module Utils
>
> %access public export
> %default total
>
> cong2 : {f : t -> u -> v} -> a = b -> c = d -> f a c = f b d
> cong2 Refl Refl = Refl
>
> dPairEq : {x, y : DPair a b}
>        -> fst x = fst y
>        -> snd x = snd y
>        -> x = y
> dPairEq {x=(n ** m)} {y=(n ** m)} Refl Refl = Refl
>
> pairEq : {x, y : (a, b)}
>       -> fst x = fst y
>       -> snd x = snd y
>       -> x = y
> pairEq {x=(n, m)} {y=(n, m)} Refl Refl = Refl
>
> equalitiesEqual : (p, q : x = y) -> p = q
> equalitiesEqual {x = x} {y = _} Refl Refl = Refl
