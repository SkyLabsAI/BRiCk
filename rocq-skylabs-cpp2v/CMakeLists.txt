##
## Copyright (c) 2020-2024 BlueRock Security, Inc.
## This software is distributed under the terms of the BedRock Open-Source License.
## See the LICENSE-BedRock file in the repository root for details.
##
cmake_minimum_required(VERSION 3.12)
project(cpp2v)

if(DEFINED ENV{BUILD_TYPE})
  set(CMAKE_BUILD_TYPE ${BUILD_TYPE})
endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Picks the newest version of clang, see https://github.com/CastXML/CastXML/issues/148
set(CMAKE_FIND_PACKAGE_SORT_ORDER NATURAL)
set(CMAKE_FIND_PACKAGE_SORT_DIRECTION DEC)

find_package(Clang REQUIRED CONFIG)

IF (${LLVM_VERSION} VERSION_LESS 16.0.0)
  MESSAGE(FATAL_ERROR "LLVM version " ${LLVM_VERSION} " < 16.0.0 not supported")
ENDIF()

message(STATUS "Found LLVM: ${LLVM_INSTALL_PREFIX} (version ${LLVM_PACKAGE_VERSION})")
message(STATUS "Using ClangConfig.cmake in: ${CLANG_CMAKE_DIR}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${LLVM_CMAKE_DIR}"
  "${CLANG_CMAKE_DIR}"
)

include(AddLLVM)

set(CPP2V_LLVM_COMPONENTS support core bitreader)

include_directories(
  ${LLVM_INCLUDE_DIRS}
  include
  llvm-include
)
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

IF(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/.git)
  FIND_PACKAGE(Git)
  IF(GIT_FOUND)
    EXECUTE_PROCESS(
      COMMAND ${GIT_EXECUTABLE} describe --tags --always
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      OUTPUT_VARIABLE "GIT_VERSION"
      ERROR_QUIET
      OUTPUT_STRIP_TRAILING_WHITESPACE)
    MESSAGE( STATUS "Git version: ${GIT_VERSION}" )
  ELSE(GIT_FOUND)
    SET(GIT_VERSION no-version)
  ENDIF(GIT_FOUND)
ENDIF(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/.git)

add_definitions( -DGIT_VERSION="${GIT_VERSION}")

# Pure owned IR/source infrastructure. This target deliberately has no Clang
# frontend dependency, so its unit tests remain narrow and deterministic.
add_llvm_library(cpp2v-ir
  STATIC
  PARTIAL_SOURCES_INTENDED
  src/SourceInfo.cpp
  src/SourceInfoEncoding.cpp
  src/IR.cpp
  src/IRFactories.cpp
  src/Sharing.cpp
  src/RocqEmitter.cpp
  src/LocationEmitter.cpp
)
target_compile_features(cpp2v-ir PUBLIC cxx_std_17)
target_compile_options(cpp2v-ir PUBLIC -fno-rtti -Wall -Wimplicit-fallthrough)
llvm_config(cpp2v-ir USE_SHARED support)

# The extraction layer is separate so cpp2v-ir and @cpp2v-unit-tests remain
# Clang-free. Its SourceManager/FileID maps exist only while extraction runs.
add_llvm_library(cpp2v-clang-source
  STATIC
  PARTIAL_SOURCES_INTENDED
  src/ClangSourceInfo.cpp
)
target_compile_features(cpp2v-clang-source PUBLIC cxx_std_17)
target_compile_options(cpp2v-clang-source PUBLIC -fno-rtti -Wall
                                                  -Wimplicit-fallthrough)
target_link_libraries(cpp2v-clang-source PUBLIC cpp2v-ir clang-cpp)
llvm_config(cpp2v-clang-source USE_SHARED support)

# Semantic extraction is Clang-backed but remains outside the pure IR library.
add_llvm_library(cpp2v-clang-builder
  STATIC
  PARTIAL_SOURCES_INTENDED
  src/IRBuilder.cpp
  src/BuildSupport.cpp
  src/BuildName.cpp
  src/BuildType.cpp
  src/BuildExpr.cpp
  src/BuildLocalDecl.cpp
  src/BuildStmt.cpp
  src/BuildDecl.cpp
)
target_compile_features(cpp2v-clang-builder PUBLIC cxx_std_17)
target_compile_options(cpp2v-clang-builder PUBLIC -fno-rtti -Wall
                                                   -Wimplicit-fallthrough)
target_link_libraries(cpp2v-clang-builder PUBLIC cpp2v-clang-source clang-cpp)
llvm_config(cpp2v-clang-builder USE_SHARED support)

add_llvm_library(tocoq
  STATIC
  PARTIAL_SOURCES_INTENDED
  src/Elaborate.cpp
  src/Version.cpp
  # --name-test intentionally retains the legacy diagnostic name formatter.
  # Its exact closure is Name -> Type/Expr -> Stmt -> LocalDecl; production
  # semantic output never enters it, and no declaration printer remains.
  src/PrintName.cpp
  src/PrintExpr.cpp
  src/PrintStmt.cpp
  src/PrintType.cpp
  src/PrintLocalDecl.cpp
  src/DiagnosticPrinter.cpp
  src/ModuleBuilder.cpp
  src/CommentScanner.cpp
  src/Formatter.cpp
  src/Logging.cpp
  src/Assert.cpp
  src/Location.cpp
  src/Template.cpp
  src/ClangPrinter.cpp
  src/StringPrettyPrinter.cpp
  src/ToCoq.cpp
  src/FromClang.cpp
)

add_llvm_executable(cpp2v
  PARTIAL_SOURCES_INTENDED
  src/cpp2v.cpp
)

add_llvm_executable(cpp2v-unit-tests
  PARTIAL_SOURCES_INTENDED
  tests/unit/IRTests.cpp
)
target_compile_features(cpp2v-unit-tests PRIVATE cxx_std_17)
target_compile_options(cpp2v-unit-tests PRIVATE -fno-rtti -Wall
                                               -Wimplicit-fallthrough)
llvm_config(cpp2v-unit-tests USE_SHARED support)
target_link_libraries(cpp2v-unit-tests PRIVATE cpp2v-ir)

add_llvm_executable(cpp2v-source-info-probe
  PARTIAL_SOURCES_INTENDED
  tests/unit/SourceInfoProbe.cpp
)
target_compile_features(cpp2v-source-info-probe PRIVATE cxx_std_17)
target_compile_options(cpp2v-source-info-probe PRIVATE -fno-rtti -Wall
                                                        -Wimplicit-fallthrough)
target_link_libraries(cpp2v-source-info-probe PRIVATE cpp2v-clang-source)
llvm_config(cpp2v-source-info-probe USE_SHARED support)

add_llvm_executable(cpp2v-name-builder-probe
  PARTIAL_SOURCES_INTENDED
  tests/unit/NameBuilderProbe.cpp
)
target_compile_features(cpp2v-name-builder-probe PRIVATE cxx_std_17)
target_compile_options(cpp2v-name-builder-probe PRIVATE -fno-rtti -Wall
                                                        -Wimplicit-fallthrough)
target_link_libraries(cpp2v-name-builder-probe PRIVATE cpp2v-clang-builder)
llvm_config(cpp2v-name-builder-probe USE_SHARED support)

add_llvm_executable(cpp2v-type-expr-builder-probe
  PARTIAL_SOURCES_INTENDED
  tests/unit/TypeExprBuilderProbe.cpp
)
target_compile_features(cpp2v-type-expr-builder-probe PRIVATE cxx_std_17)
target_compile_options(cpp2v-type-expr-builder-probe PRIVATE -fno-rtti -Wall
                                                             -Wimplicit-fallthrough)
target_link_libraries(cpp2v-type-expr-builder-probe PRIVATE cpp2v-clang-builder)
llvm_config(cpp2v-type-expr-builder-probe USE_SHARED support)

add_llvm_executable(cpp2v-sharing-builder-probe
  PARTIAL_SOURCES_INTENDED
  tests/unit/SharingBuilderProbe.cpp
)
target_compile_features(cpp2v-sharing-builder-probe PRIVATE cxx_std_17)
target_compile_options(cpp2v-sharing-builder-probe PRIVATE -fno-rtti -Wall
                                                           -Wimplicit-fallthrough)
target_link_libraries(cpp2v-sharing-builder-probe PRIVATE cpp2v-clang-builder)
llvm_config(cpp2v-sharing-builder-probe USE_SHARED support)

add_llvm_executable(cpp2v-declaration-builder-probe
  PARTIAL_SOURCES_INTENDED
  tests/unit/DeclarationBuilderProbe.cpp
)
target_compile_features(cpp2v-declaration-builder-probe PRIVATE cxx_std_17)
target_compile_options(cpp2v-declaration-builder-probe PRIVATE -fno-rtti -Wall
                                                               -Wimplicit-fallthrough)
target_link_libraries(cpp2v-declaration-builder-probe PRIVATE
  cpp2v-clang-builder tocoq)
llvm_config(cpp2v-declaration-builder-probe USE_SHARED support)

set_property(TARGET cpp2v-ir PROPERTY POSITION_INDEPENDENT_CODE ON)
set_property(TARGET cpp2v-clang-source PROPERTY POSITION_INDEPENDENT_CODE ON)
set_property(TARGET cpp2v-clang-builder PROPERTY POSITION_INDEPENDENT_CODE ON)
set_property(TARGET tocoq PROPERTY POSITION_INDEPENDENT_CODE ON)
target_compile_features(tocoq PUBLIC cxx_std_17)
target_compile_features(cpp2v PRIVATE cxx_std_17)
target_compile_options(tocoq PUBLIC -fno-rtti -Wall -Wimplicit-fallthrough)
target_compile_options(cpp2v PRIVATE -fno-rtti -Wall -Wimplicit-fallthrough)

llvm_config(cpp2v USE_SHARED ${CPP2V_LLVM_COMPONENTS})

# Link production orchestration to both the pure emitter and the Clang-backed
# owner builder; Clang is no longer reachable after IRBuilder returns.
target_link_libraries(tocoq PUBLIC cpp2v-ir cpp2v-clang-builder)
target_link_libraries(cpp2v PUBLIC ${llvm_libs} clang-cpp tocoq)
