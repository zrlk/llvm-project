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

#include "clang/AST/DeclCXX.h"
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

/// Diagnoses named lifetime annotations on the class definition \p RD: the
/// lifetimes its `LIFETIME_PARAMS` introduces, and the ones written on the
/// types of its fields.
///
/// This is meant to run once per class, when its definition is complete,
/// rather than with each member function: a class need not have any, and one
/// with several would be diagnosed once per member.
///
/// FIXME: Nothing calls this yet. The natural caller is
/// `Sema::CheckCompletedCXXClass`, and the prototype deliberately makes no
/// changes to Sema's core declaration handling. Until a caller exists, class
/// `LIFETIME_PARAMS` and field types are not checked for well-formedness.
void checkRecordNamedLifetimes(const ASTContext &Ctx, const CXXRecordDecl *RD,
                               LifetimeSafetySemaHelper &SemaHelper);

} // namespace clang::lifetimes::internal

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMESAFETY_SIGNATURECHECK_H
