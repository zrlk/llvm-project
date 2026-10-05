//===- SignatureCheck.h - Named lifetime well-formedness -*------- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Checks that named lifetime annotations are well formed. This is a purely
// syntactic check on the declaration: it does not look at the body and does
// not require the CFG.
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMESAFETY_SIGNATURECHECK_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMESAFETY_SIGNATURECHECK_H

#include "clang/Analysis/Analyses/LifetimeSafety/LifetimeSafety.h"
#include "clang/Analysis/AnalysisDeclContext.h"

namespace clang::lifetimes::internal {

/// Diagnoses named lifetime annotations on the function under analysis and on
/// all of its redeclarations. Covers both their well-formedness and their
/// agreement with any `lifetimebound` attributes on the same function.
///
/// Redeclarations are included because annotations written on types do not
/// merge across them, so an annotation in a header is only ever visible on the
/// declaration that spelled it.
void checkNamedLifetimes(AnalysisDeclContext &AC,
                         LifetimeSafetySemaHelper *SemaHelper,
                         const LifetimeSafetyOpts &Opts);

} // namespace clang::lifetimes::internal

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMESAFETY_SIGNATURECHECK_H
