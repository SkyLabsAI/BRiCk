/*
 * Copyright (c) 2020-2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 */
#pragma once

namespace clang {
class Decl;
} // namespace clang

namespace fmt {
class Formatter;
}

class ClangPrinter;
class CoqPrinter;

namespace default_template_alias {

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
duplicate enclosing/local parameter names, and non-type defaults that this
module cannot print into the generated alias table.

TODO: Alias generation is currently all-or-nothing for a declaration: if any
defaulted parameter in the suffix is unsupported, no default-template aliases
are emitted for that declaration.
*/
void printDefaultTemplateAliases(const clang::Decl *decl, CoqPrinter &print,
                                 ClangPrinter &cprint);

} // namespace default_template_alias
