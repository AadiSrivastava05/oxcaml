(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(** Strength reduction of derived induction variables.

    A loop reaches [Cmm] as a [Ccatch Recursive] whose handler parameters are
    the loop-carried values. When such a handler has an integer parameter [i]
    that every exit either steps by a constant or resets to a duplicable value,
    and the handler body computes [b + i] for some [b] bound outside the loop,
    this pass carries [b + i] in a new handler parameter instead of rebuilding
    it on every iteration: the entry edges pass [b + i0] and the stepping edges
    pass [j + stride].

    OCaml code has to write this shape. The garbage collector locates a block's
    header from any pointer it scans, and the header sits immediately before the
    data, so an interior pointer is not a representable value and an array walk
    cannot hoist a moving pointer the way C can. The index form is forced by the
    language, so the arithmetic it implies is worth removing.

    Deliberately out of scope: non-constant strides, sums of two induction
    variables, products ([b * i]), reassociation, any loop whose header is not
    syntactically a [Ccatch Recursive], and any invariant not already bound
    outside the loop (nothing is hoisted). Only the first eligible parameter of
    a handler is treated as an induction variable. See the implementation for
    the exact conditions. *)

val fundecl : Cmm.fundecl -> Cmm.fundecl
