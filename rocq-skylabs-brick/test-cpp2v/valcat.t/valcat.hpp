/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#pragma once

// A type's value category
//
// See https://en.cppreference.com/w/cpp/language/value_category

enum class ValCat { Prvalue, Lvalue, Xvalue };

template<typename T> struct valcat_of { static constexpr ValCat value = ValCat::Prvalue; };
template<typename T> struct valcat_of<T&> { static constexpr ValCat value = ValCat::Lvalue; };
template<typename T> struct valcat_of<T&&> { static constexpr ValCat value = ValCat::Xvalue; };

template<typename T> constexpr bool is_prvalue = valcat_of<T>::value == ValCat::Prvalue;
template<typename T> constexpr bool is_lvalue = valcat_of<T>::value == ValCat::Lvalue;
template<typename T> constexpr bool is_xvalue = valcat_of<T>::value == ValCat::Xvalue;

template<typename T> constexpr bool is_rvalue = is_prvalue<T> || is_xvalue<T>;
template<typename T> constexpr bool is_glvalue = is_lvalue<T> || is_xvalue<T>;

// An expression's value category
//
// See https://en.cppreference.com/w/cpp/language/decltype

#define IS_PRVALUE(e) is_prvalue<decltype((e))>
#define IS_LVALUE(e) is_lvalue<decltype((e))>
#define IS_XVALUE(e) is_xvalue<decltype((e))>
#define IS_RVALUE(e) is_rvalue<decltype((e))>
#define IS_GLVALUE(e) is_glvalue<decltype((e))>

#define PRVALUE(e) static_assert(IS_PRVALUE(e), "PRVALUE(" #e ")")
#define LVALUE(e) static_assert(IS_LVALUE(e), "LVALUE(" #e ")")
#define XVALUE(e) static_assert(IS_XVALUE(e), "XVALUE(" #e ")")
