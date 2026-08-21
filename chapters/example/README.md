The guiding example of Chapter 3 (`chapters/03-approach.typ`, section "A Guiding
Example"), kept here so the listings can be checked against the source.

    example.rs          the Rust, 8 functions over 1 struct and 2 enums. Carries
                        `use prusti_contracts::*` and one `body_invariant!(true)`
                        per loop, without which Prusti refuses the file; the
                        thesis elides both and says so in a footnote.
    example.vpr         Prusti's encoding of it, 3371 lines, 151 members, with
                        identifiers shortened by shorten-names.py
    example.clean.vpr   the same file with per-statement `label _before_*` lines,
                        MIR comments and blank lines stripped, 1481 lines — what
                        the chapter's listings are quoted from
    shorten-names.py    the identifier shortening, applied to both .vpr files and
                        to every listing in the thesis

This program is *not* one of the 22 benchmarks measured in Chapter 5: it carries
two loops, and the benchmark corpus is loop-free by construction. It is here
because it is the smallest program that puts an enum, a match, a back edge and a
`&mut` reborrow in front of the reader at once.

Regenerate with

    PRUSTI_CHECK_OVERFLOWS=false PRUSTI_DUMP_VIPER_PROGRAM=true \
        prusti-rustc --crate-type=lib --edition=2021 example.rs

then rebuild the clean file with

    grep -vE '^\s*//|^\s*label _before_|^\s*$' example.vpr > example.clean.vpr

and shorten the identifiers in both:

    python3 shorten-names.py example.vpr example.clean.vpr

The shortening is injective on the identifiers of this crate (checked: no two
generated names map to the same short name in example.clean.vpr). The scheme:

    s_<T>                   -> <T>, with Int_i32 -> i32, Bool -> bool,
                               Int_isize -> isize, 0_Tuple -> Unit,
                               2_Tuple -> Pair, Ref_mutable -> RefMut,
                               Ref_immutable -> RefImm,
                               <f>_Closure_0 -> Closure_<f>
    p_<T>                   -> own_<T>          (predicate)
    p_<T>_<i>_owned         -> own_<T>_<i>      (variant payload predicate)
    p_<T>_snap              -> snap_<T>
    p_<T>_assign            -> assign_<T>
    p_<T>_val               -> val_<T>          (field)
    p_<T>_field_discr       -> <T>_field_discr
    make_generic_s_<T>      -> generic_<T>      (function on snapshots)
    make_concrete_s_<T>     -> concrete_<T>
    make_generic_<T>        -> unchanged        (method on refs)
    m_<f>                   -> <f>
    mir_binop_Lt_Int_i32_Int_i32 -> lt_i32_i32, likewise le, and
    AddWithOverflow/SubWithOverflow -> add_ovf/sub_ovf
