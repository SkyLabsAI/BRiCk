/*
 * Copyright (c) 2020-2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

#include <llvm/ADT/ArrayRef.h>

namespace clang {
class Decl;
class NamedDecl;
class NonTypeTemplateParmDecl;
} // namespace clang

namespace fmt {
class Formatter;
}

class ClangPrinter;
class CoqPrinter;

namespace default_template_alias {

/*
Return whether cpp2v knows how to synthesize aliases for `param`'s default.

This is intentionally narrower than what C++ accepts.

TODO: Extend support beyond literal non-type defaults and direct references to
earlier non-type template parameters. More general defaults require expression
substitution/evaluation before they can be printed into the BRiCk alias table.
*/
bool isSupportedValueDefault(const clang::NonTypeTemplateParmDecl *param);

/*
Print every `Dtemplated_typedef` that cpp2v synthesizes from default template
arguments on `decl`.

Precondition: the caller has already decided that template declarations and
typedef declarations should be printed. The function emits aliases when `decl`
is a class/union or type-alias template declaration whose template has a suffix
of defaulted parameters that this module can represent in the BRiCk alias
table. It emits no output when those declaration/default-argument conditions
are not met.

TODO: This currently rejects template-template parameters, parameter packs,
duplicate enclosing/local parameter names, and non-type defaults outside
`isSupportedValueDefault`.

TODO: Alias generation is currently all-or-nothing for a declaration: if any
defaulted parameter in the suffix is unsupported, no default-template aliases
are emitted for that declaration.
*/
void printDefaultTemplateAliases(const clang::Decl *decl, CoqPrinter &print,
                                 ClangPrinter &cprint);

/*
Print the argument list for the target of a generated default-template alias.

`params` is the full template parameter list of the original declaration, and
`keep` is the number of parameters that remain explicit in the generated alias.
The function prints one BRiCk `list temp_arg` containing all original template
arguments after recursively expanding the omitted default arguments through
earlier parameters.

Precondition: `keep <= params.size()`, every element of `params` is either a
`TemplateTypeParmDecl` or `NonTypeTemplateParmDecl`, no element is a parameter
pack, and every parameter at index `keep` or later has a default argument that
this module can print. For non-type template parameters, callers should check
`isSupportedValueDefault` before calling this function. For example, `keep == 1`
is valid only when the second and all later parameters have defaults.

TODO: This function performs only local recursive substitution for defaults that
are already known to be printable; it is not a general Clang template
substitution engine.

TODO: A more complete implementation could use Clang's Sema substitution
machinery with `MultiLevelTemplateArgumentList`, but that requires constructing
dependent `TemplateArgument`s for parameter-to-parameter substitution and can
trigger diagnostics or semantic instantiation.

TODO: Generalizing this function to template-template parameters or parameter
packs requires a larger representation story for generated aliases.

For example, given:

    template <typename T, typename U = T, typename V = U> struct C;

calling `printTargetArgs(..., params, 1, ...)` prints the argument list:

    [Atype (Tparam "T"); Atype (Tparam "T"); Atype (Tparam "T")]

The caller is responsible for wrapping this list in the surrounding target
name, producing a complete target type such as `Tnamed "C<$T, $T, $T>"`.
*/
fmt::Formatter &printTargetArgs(CoqPrinter &print,
                                llvm::ArrayRef<const clang::NamedDecl *> params,
                                unsigned keep, ClangPrinter &cprint);

} // namespace default_template_alias
