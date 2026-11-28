/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is based on the tutorial here:
 * https://clang.llvm.org/docs/LibASTMatchersTutorial.html
 * See the LICENSE-LLVM file in the repositroy root for details.
 *
 */
#include "clang/AST/ASTConsumer.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include <optional>
#include <sys/utsname.h>
// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"
// Declares llvm::cl::extrahelp.
#include "Logging.hpp"
#include "ToCoq.hpp"
#include "Trace.hpp"
#include "Version.hpp"
#include "llvm/Support/CommandLine.h"

using namespace clang;
using namespace clang::tooling;
using namespace llvm;

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
static cl::OptionCategory Cpp2V("cpp2v options");

// CommonOptionsParser declares HelpMessage with a description of the common
// command-line options related to the compilation database and input files.
// It's nice to have this help message in all tools.
static cl::extrahelp CommonHelp(
    "\nACTUAL USAGE: cpp2v [cpp2v options] <source> -- [clang options]\n");

static cl::opt<std::string> VFileOutput("module",
                                        cl::desc("print translation unit"),
                                        cl::value_desc("filename"),
                                        cl::Optional, cl::cat(Cpp2V));

static cl::alias DashO("o", cl::desc("alias for --module"),
                       cl::value_desc("filename"), cl::aliasopt(VFileOutput));

static cl::opt<bool> Verbose("v", cl::desc("verbose"), cl::Optional,
                             cl::cat(Cpp2V));
static cl::opt<bool> Verboser("vv", cl::desc("verboser"), cl::Optional,
                              cl::cat(Cpp2V));
static cl::opt<bool> Quiet("q", cl::desc("quiet"), cl::Optional,
                           cl::cat(Cpp2V));

static cl::opt<bool> Comment("comment", cl::desc("include name comments"),
                             cl::Optional, cl::cat(Cpp2V));

static cl::opt<bool> NoElaborate(
    "no-elaborate",
    cl::desc("Do not force generation of implicit member functions."),
    cl::Optional, cl::cat(Cpp2V));

static cl::opt<bool> Elaborate(
    "elaborate",
    cl::desc("Elaborate templates and un-forced definitions. This is unsafe in general and can cause segfaults."),
    cl::Optional, cl::cat(Cpp2V));

static cl::opt<bool> Version("cpp2v-version",
                             cl::desc("print version and exit"), cl::Optional,
                             cl::ValueOptional, cl::cat(Cpp2V));

static cl::opt<std::string> Templates("templates", cl::desc("print templates"),
                                      cl::value_desc("filename"), cl::Optional,
                                      cl::cat(Cpp2V));

static cl::opt<bool>
    NoTemplates("no-templates",
                cl::desc("Do not include templates in the -o output"),
                cl::Optional, cl::cat(Cpp2V));

static cl::opt<bool>
    NoSystem("no-system",
             cl::desc("Do not use the system clang resource directory"),
             cl::Optional, cl::cat(Cpp2V));

static cl::opt<std::string> NameTest("name-test",
                                     cl::desc("print structured names"),
                                     cl::value_desc("filename"), cl::Optional,
                                     cl::cat(Cpp2V));

static cl::opt<bool> CheckTypes("check-types",
                                cl::desc("check types of translation units"),
                                cl::Optional, cl::ValueOptional,
                                cl::cat(Cpp2V));

static cl::bits<Trace::Bit> TraceBits(
    "trace", cl::desc("print debug trace on fd 2 (can be repeated)"),
    cl::ZeroOrMore, cl::CommaSeparated,
    cl::values(clEnumValN(Trace::Bit::Elaborate, "Elaborate",
                          "trace definition of implicits"),
               clEnumValN(Trace::Bit::ModuleBuilder, "ModuleBuilder",
                          "trace declaration filter"),
               clEnumValN(Trace::Bit::Decl, "Decl",
                          "trace declaration printer"),
               clEnumValN(Trace::Bit::Name, "Name", "trace name printer"),
               clEnumValN(Trace::Bit::Type, "Type", "trace type printer"),
               clEnumValN(Trace::Bit::Local, "Local",
                          "trace local declaration printer"),
               clEnumValN(Trace::Bit::Stmt, "Stmt", "trace statement printer"),
               clEnumValN(Trace::Bit::Expr, "Expr", "trace expression printer"),
               clEnumValN(Trace::Bit::ALL, "ALL", "trace everything")),
    cl::cat(Cpp2V));

static cl::opt<bool> NoSharing("no-sharing", cl::desc("disable sharing"),
                               cl::Optional, cl::ValueOptional, cl::cat(Cpp2V));

static cl::opt<bool>
    NoAliases("no-aliases",
              cl::desc("do not emit typedef and using declarations"),
              cl::Optional, cl::ValueOptional, cl::cat(Cpp2V));

static cl::opt<std::string>
    Interactive("for-interactive",
                cl::desc("INTERNAL USE: the output will be interpreted "
                         "directly within a process"),
                cl::value_desc("module_name"), cl::Optional, cl::cat(Cpp2V));

static cl::opt<std::string>
    Attributes("attributes", cl::desc("Attributes to pass to the [cpp.prog]"),
               cl::value_desc("attrs"), cl::Optional, cl::cat(Cpp2V));

class ToCoqAction : public clang::ASTFrontendAction {
public:
    virtual std::unique_ptr<clang::ASTConsumer>
    CreateASTConsumer(clang::CompilerInstance &Compiler,
                      llvm::StringRef InFile) override {
#if 0
	Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames.push_back(
		"with");
	Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames.push_back(
		"internal");
	for (auto i :
		 Compiler.getInvocation().getLangOpts()->CommentOpts.BlockCommandNames) {
		llvm::errs() << i << "\n";
	}
#endif

        if (Compiler.getDiagnostics().getNumErrors() > 0) {
            return nullptr;
        }
        bool should_elaborate = true; // TODO: change the default to false!
        if (Elaborate) {
            should_elaborate = true;
        }
        if (NoElaborate) {
            should_elaborate = false;
        }
        auto *result =
            new ToCoqConsumer(&Compiler, to_opt(VFileOutput),
                              to_opt(Templates), to_opt(NameTest),
                              Trace::fromBits(TraceBits.getBits()), Comment,
                              !NoSharing, CheckTypes, !NoTemplates,
                              should_elaborate, !NoAliases, to_opt(Interactive),
                              to_opt(Attributes));
        return std::unique_ptr<clang::ASTConsumer>(result);
    }

    template <typename T> std::optional<T> to_opt(const cl::opt<T> &val) {
        if (val.empty()) {
            return std::optional<T>();
        } else {
            return std::optional<T>(val.getValue());
        }
    }

    virtual bool BeginSourceFileAction(CompilerInstance &CI) override {
        return this->clang::ASTFrontendAction::BeginSourceFileAction(CI);
    }
};

std::optional<std::string> getCommandOutput(const char *command) {
    std::string Result;
    std::array<char, 128> Buffer;
    std::unique_ptr<FILE, decltype(&pclose)> Pipe(popen(command, "r"), pclose);
    if (!Pipe) {
        return {}; // Fallback
    }
    while (fgets(Buffer.data(), Buffer.size(), Pipe.get()) != nullptr) {
        Result += Buffer.data();
    }
    // Trim trailing newline
    if (!Result.empty() && Result.back() == '\n') {
        Result.pop_back();
    }
    return {Result};
}

std::optional<std::string> getClangResourceDir() {
    return getCommandOutput("clang -print-resource-dir");
}

std::optional<std::string> getMacSysRoot() {
    return getCommandOutput("xcrun --show-sdk-path");
}

bool isDarwin() {
    struct utsname name;
    uname(&name);
    return strcmp(name.sysname, "Darwin") == 0;
}

void addOpt(ClangTool &Tool, const char *opt, std::optional<std::string> value,
            const char *desc) {
    if (value.has_value()) {
        std::string arg{opt};
        arg += value.value();
        // Place this at the beginning of the arguments in case it is overloaded
        // later
        Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
            arg.c_str(), ArgumentInsertPosition::BEGIN));
        logging::log(logging::Level::VERBOSER) << "Using " << arg << "\n";
    } else {
        logging::log(logging::Level::VERBOSER)
            << "Could not detect " << desc << ".\n";
    }
}

static cl::list<std::string> RemapDirs(
    "remap-dir",
    cl::desc("FROM=TO: read a file under directory FROM from the same "
             "relative path under TO when that file exists there. Relative "
             "FROM and TO are resolved against the working directory at "
             "startup. Paths already under TO are left alone. Example, "
             "run from <root>/_build/default: --remap-dir=../..=."),
    cl::value_desc("FROM=TO"), cl::ZeroOrMore, cl::cat(Cpp2V));

// PROTOTYPE (skylabs-fm#436). A file system that sends lookups of
// FROM/rel to TO/rel when TO/rel exists, and falls back to FROM/rel
// otherwise.
//
// dune copies each source file R/rel to R/_build/default/rel, and the
// tools are run on the copy while -I flags from compile_commands.json
// still name R. Without remapping, one header can be reached both as
// the copy and as the original: two inodes, so clang's `#pragma once`
// (which identifies files by inode) does not deduplicate them. With
// --remap-dir=R=R/_build/default every reachable copy is read through
// one inode, whichever spelling found it.
class RemapFileSystem : public vfs::ProxyFileSystem {
    struct Mapping {
        std::string From, To;
    };
    std::vector<Mapping> Mappings;

    static bool isUnder(StringRef Path, StringRef Dir) {
        return Path == Dir ||
               (Path.starts_with(Dir) && sys::path::is_separator(Path[Dir.size()]));
    }

    // The remapped spelling of Path, if any mapping applies and the
    // target exists.
    std::optional<std::string> remap(const Twine &Path) {
        SmallString<256> Abs;
        Path.toVector(Abs);
        if (getUnderlyingFS().makeAbsolute(Abs))
            return std::nullopt;
        sys::path::remove_dots(Abs, /*remove_dot_dot=*/true);
        for (const auto &M : Mappings) {
            if (!isUnder(Abs, M.From) || isUnder(Abs, M.To))
                continue;
            SmallString<256> Target(M.To);
            sys::path::append(Target, Abs.str().substr(M.From.size()));
            if (getUnderlyingFS().exists(Target))
                return std::string(Target.str());
        }
        return std::nullopt;
    }

public:
    RemapFileSystem(IntrusiveRefCntPtr<vfs::FileSystem> FS)
        : ProxyFileSystem(std::move(FS)) {}

    // Adds FROM=TO, resolving relative paths against the current
    // working directory. Returns false on a malformed argument.
    bool addMapping(StringRef Arg) {
        auto [From, To] = Arg.split('=');
        if (From.empty() || To.empty())
            return false;
        auto Norm = [&](StringRef P) {
            SmallString<256> S(P);
            getUnderlyingFS().makeAbsolute(S);
            sys::path::remove_dots(S, /*remove_dot_dot=*/true);
            return std::string(S.str());
        };
        Mappings.push_back({Norm(From), Norm(To)});
        logging::log(logging::Level::VERBOSER)
            << "Remapping " << Mappings.back().From << " to "
            << Mappings.back().To << "\n";
        return true;
    }

    ErrorOr<vfs::Status> status(const Twine &Path) override {
        if (auto T = remap(Path)) {
            auto S = getUnderlyingFS().status(*T);
            if (!S)
                return S;
            // Keep the requested name; the inode is the target's, which is
            // what lets FileManager identify both spellings.
            return vfs::Status::copyWithNewName(*S, Path);
        }
        return ProxyFileSystem::status(Path);
    }

    ErrorOr<std::unique_ptr<vfs::File>>
    openFileForRead(const Twine &Path) override {
        if (auto T = remap(Path))
            return vfs::File::getWithPath(
                getUnderlyingFS().openFileForRead(*T), Path);
        return ProxyFileSystem::openFileForRead(Path);
    }

    bool exists(const Twine &Path) override {
        if (remap(Path))
            return true;
        return ProxyFileSystem::exists(Path);
    }
};

int main(int argc, const char **argv) {
    auto MaybeOptionsParser = CommonOptionsParser::create(argc, argv, Cpp2V);
    if (not MaybeOptionsParser) {
        llvm::errs() << MaybeOptionsParser.takeError();
        return 1;
    }

    auto &OptionsParser = MaybeOptionsParser.get();

    if (Version) {
        llvm::errs() << "cpp2v version " << cpp2v::VERSION << "\n";
        return 0;
    }

    logging::set_level(logging::NONE);
    if (Verboser) {
        logging::set_level(logging::VERBOSER);
    } else if (Verbose) {
        logging::set_level(logging::VERBOSE);
    } else if (Quiet) {
        logging::set_level(logging::NONE);
    }

    auto DiagOptions = new DiagnosticOptions();
    IntrusiveRefCntPtr<vfs::FileSystem> BaseFS = vfs::getRealFileSystem();
    if (!RemapDirs.empty()) {
        auto Remap = makeIntrusiveRefCnt<RemapFileSystem>(BaseFS);
        for (const auto &Arg : RemapDirs) {
            if (!Remap->addMapping(Arg)) {
                llvm::errs() << "cpp2v: malformed --remap-dir=" << Arg
                             << " (expected FROM=TO)\n";
                return 1;
            }
        }
        BaseFS = Remap;
    }

    ClangTool Tool(OptionsParser.getCompilations(),
                   OptionsParser.getSourcePathList(),
                   std::make_shared<PCHContainerOperations>(), BaseFS);

    if (!NoSystem.getValue()) {
        addOpt(Tool, "-resource-dir=", getClangResourceDir(),
               "the system resource directory");

        logging::log(logging::Level::VERBOSER)
            << "Is this a Darwin platform (Mac/iOS)? " << isDarwin() << "\n";

        if (isDarwin()) {
            // XXX: On Mac, this lets us find the C++ stdlib that comes
            // with the _system_ SDK (say, clang 16), not the C++
            // stdlib that comes with the _user_ compiler.
            addOpt(Tool, "-isysroot", getMacSysRoot(),
                   "the Mac sysroot directory");
        }
    }

#if CLANG_VERSION_MAJOR > 20
    Tool.setDiagnosticConsumer(
        new clang::TextDiagnosticPrinter(llvm::errs(), *DiagOptions, false));
#else
    Tool.setDiagnosticConsumer(
        new clang::TextDiagnosticPrinter(llvm::errs(), DiagOptions, false));
#endif

    return Tool.run(newFrontendActionFactory<ToCoqAction>().get());
}
