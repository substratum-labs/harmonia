import Harmonia.Applications.Kadmos.Generated.SourceValidator

namespace Harmonia.Applications.Kadmos.Generated

/-- Untrusted child-span proposals for low-level statement syntax. The checker
    below validates every source interval, delimiter and AST child. -/
inductive StmtCertificate where
  | empty
  | final (bodySpan : SourceSpan) (body : StmtCertificate)
  | sequence (firstSpan restSpan : SourceSpan)
      (first rest : StmtCertificate)
  | returnExpr (exprSpan : SourceSpan)
  | throwExpr (exprSpan : SourceSpan)
  | doExpr (exprSpan : SourceSpan)
  | localBinding (exprSpan : SourceSpan)
  | augmentLocal (exprSpan : SourceSpan)
  | ifThen (condSpan bodySpan : SourceSpan) (body : StmtCertificate)
  | ifThenIndented (condSpan bodySpan : SourceSpan)
      (indent : String) (body : StmtCertificate)
  deriving Repr

def spanWithin (outer inner : SourceSpan) : Bool :=
  outer.start ≤ inner.start && inner.start ≤ inner.stop &&
    inner.stop ≤ outer.stop

private def statementSeparator : TargetLang → String
  | .ts => "\n  "
  | .python => "\n    "

/-- AST-guided restricted checker. A certificate has no authority until all
    source equations and recursively checked low-level children succeed. -/
def validateStmtCertificate (lang : TargetLang) (source : String)
    (span : SourceSpan) (stmt : TargetStmt) (cert : StmtCertificate) : Bool :=
  let bounds := span.start ≤ span.stop && span.stop ≤ source.length
  bounds &&
    match stmt, cert with
    | .empty, .empty => span.text source == ""
    | .sequence body .empty, .final bodySpan bodyCert =>
        singleStatementCheck body && spanWithin span bodySpan &&
          span.text source == bodySpan.text source &&
          validateStmtCertificate lang source bodySpan body bodyCert
    | .sequence first rest, .sequence firstSpan restSpan firstCert restCert =>
        singleStatementCheck first && spanWithin span firstSpan &&
          spanWithin span restSpan &&
          firstSpan.stop ≤ restSpan.start &&
          span.text source == firstSpan.text source ++
            statementSeparator lang ++ restSpan.text source &&
          validateStmtCertificate lang source firstSpan first firstCert &&
          validateStmtCertificate lang source restSpan rest restCert
    | .returnValue value, .returnExpr exprSpan =>
        spanWithin span exprSpan &&
          (match lang with
           | .ts => span.text source == "return " ++ exprSpan.text source ++ ";"
           | .python => span.text source == "return " ++ exprSpan.text source) &&
          validateFunctionExpr lang (exprSpan.text source) value
    | .throwValue value, .throwExpr exprSpan =>
        spanWithin span exprSpan &&
          (match lang with
           | .ts => span.text source == "throw " ++ exprSpan.text source ++ ";"
           | .python => span.text source == "raise " ++ exprSpan.text source) &&
          validateFunctionExpr lang (exprSpan.text source) value
    | .doExpr value, .doExpr exprSpan =>
        spanWithin span exprSpan &&
          (match lang with
           | .ts => span.text source == exprSpan.text source ++ ";"
           | .python => span.text source == exprSpan.text source) &&
          validateFunctionExpr lang (exprSpan.text source) value
    | .letLocal name mutable value, .localBinding exprSpan =>
        lang == .ts && spanWithin span exprSpan &&
          expressionIdentifierCheck .ts name &&
          span.text source ==
            (if mutable then "let " else "const ") ++ name ++ " = " ++
              exprSpan.text source ++ ";" &&
          validateFunctionExpr .ts (exprSpan.text source) value
    | .assign (.local name) value, .localBinding exprSpan =>
        lang == .python && spanWithin span exprSpan &&
          expressionIdentifierCheck .python name &&
          span.text source == name ++ " = " ++ exprSpan.text source &&
          validateFunctionExpr .python (exprSpan.text source) value
    | .augment (.local name) .add value, .augmentLocal exprSpan =>
        lang == .python && spanWithin span exprSpan &&
          expressionIdentifierCheck .python name &&
          span.text source == name ++ " += " ++ exprSpan.text source &&
          validateFunctionExpr .python (exprSpan.text source) value
    | .ifThenElse cond yes .empty, .ifThen condSpan bodySpan bodyCert =>
        spanWithin span condSpan && spanWithin span bodySpan &&
          condSpan.stop ≤ bodySpan.start &&
          (match lang with
           | .ts => singleStatementCheck yes &&
               span.text source == "if (" ++ condSpan.text source ++
                 ") " ++ bodySpan.text source
           | .python => suiteLinesWithin "        " (bodySpan.text source) &&
               span.text source == "if " ++ condSpan.text source ++
                 ":\n        " ++ bodySpan.text source) &&
          validateFunctionExpr lang (condSpan.text source) cond &&
          validateStmtCertificate lang source bodySpan yes bodyCert
    | .ifThenElse cond yes .empty,
        .ifThenIndented condSpan bodySpan indent bodyCert =>
        lang == .python && spanWithin span condSpan &&
          spanWithin span bodySpan && condSpan.stop ≤ bodySpan.start &&
          4 ≤ indent.length && indent.length % 4 == 0 &&
          indent.toList.all (· == ' ') &&
          suiteLinesWithin indent (bodySpan.text source) &&
          span.text source == "if " ++ condSpan.text source ++
            ":\n" ++ indent ++ bodySpan.text source &&
          validateFunctionExpr .python (condSpan.text source) cond &&
          validateStmtCertificate .python source bodySpan yes bodyCert
    | _, _ => false

theorem StmtDerives.syntax {lang control source span stmt}
    (h : StmtDerives lang control source span stmt) :
    StmtSyntax lang control (span.text source) stmt := by
  cases h with
  | ofSyntax _ hSyntax => exact hSyntax

theorem validateStmtCertificate_sound {lang source span stmt cert}
    (h : validateStmtCertificate lang source span stmt cert = true) :
    StmtDerives lang .function source span stmt := by
  induction cert generalizing span stmt with
  | empty =>
      cases stmt with
      | empty =>
          simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
            beq_iff_eq] at h
          exact .ofSyntax ⟨(by simpa using h.1.1), (by simpa using h.1.2)⟩
            (by simpa only [h.2] using StmtSyntax.empty lang .function)
      | _ => simp [validateStmtCertificate] at h
  | final bodySpan bodyCert ih =>
      cases stmt with
      | sequence body rest =>
          cases rest with
          | empty =>
              simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
                beq_iff_eq] at h
              rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
                ⟨⟨⟨hSingle, hWithin⟩, hSource⟩, hBody⟩⟩
              have hChild := ih hBody
              have hSyntax := StmtDerives.syntax hChild
              apply StmtDerives.ofSyntax
                ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
              rw [hSource]
              cases lang with
              | ts =>
                  exact .tsFinal (singleStatementCheck_sound hSingle) hSyntax
              | python =>
                  exact .pythonFinal (singleStatementCheck_sound hSingle)
                    hSyntax
          | _ => simp [validateStmtCertificate] at h
      | _ => simp [validateStmtCertificate] at h
  | sequence firstSpan restSpan firstCert restCert ihFirst ihRest =>
      cases stmt with
      | sequence first rest =>
          simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
            beq_iff_eq] at h
          rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
            ⟨⟨⟨⟨⟨hSingle, hFirstWithin⟩, hRestWithin⟩,
              hOrder⟩, hSource⟩, hFirst⟩, hRest⟩
          have hFirstSyntax := StmtDerives.syntax (ihFirst hFirst)
          have hRestSyntax := StmtDerives.syntax (ihRest hRest)
          apply StmtDerives.ofSyntax
            ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
          rw [hSource]
          cases lang with
          | ts =>
              exact .tsSequence (singleStatementCheck_sound hSingle)
                hFirstSyntax hRestSyntax
          | python =>
              exact .pythonSequence (singleStatementCheck_sound hSingle)
                hFirstSyntax hRestSyntax
      | _ => simp [validateStmtCertificate] at h
  | returnExpr exprSpan =>
      cases stmt with
      | returnValue value =>
          simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
            beq_iff_eq] at h
          rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
            ⟨⟨hWithin, hSource⟩, hValue⟩⟩
          apply StmtDerives.ofSyntax
            ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
          cases lang with
          | ts =>
              simp at hSource
              rw [hSource]
              exact .tsReturn (validateFunctionExpr_sound hValue)
          | python =>
              simp at hSource
              rw [hSource]
              exact .pythonReturn (validateFunctionExpr_sound hValue)
      | _ => simp [validateStmtCertificate] at h
  | throwExpr exprSpan =>
      cases stmt with
      | throwValue value =>
          simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
            beq_iff_eq] at h
          rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
            ⟨⟨hWithin, hSource⟩, hValue⟩⟩
          apply StmtDerives.ofSyntax
            ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
          cases lang with
          | ts =>
              simp at hSource
              rw [hSource]
              exact .tsThrow (validateFunctionExpr_sound hValue)
          | python =>
              simp at hSource
              rw [hSource]
              exact .pythonRaise (validateFunctionExpr_sound hValue)
      | _ => simp [validateStmtCertificate] at h
  | doExpr exprSpan =>
      cases stmt with
      | doExpr value =>
          simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
            beq_iff_eq] at h
          rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
            ⟨⟨hWithin, hSource⟩, hValue⟩⟩
          apply StmtDerives.ofSyntax
            ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
          cases lang with
          | ts =>
              simp at hSource
              rw [hSource]
              exact .tsDo (validateFunctionExpr_sound hValue)
          | python =>
              simp at hSource
              rw [hSource]
              exact .pythonDo (validateFunctionExpr_sound hValue)
      | _ => simp [validateStmtCertificate] at h
  | localBinding exprSpan =>
      cases stmt with
      | letLocal name mutable value =>
          simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
            beq_iff_eq] at h
          rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
            ⟨⟨⟨hLang, hWithin⟩, hName⟩, hSource⟩, hValue⟩
          have hLangEq : lang = .ts := by simpa using hLang
          subst lang
          apply StmtDerives.ofSyntax
            ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
          rw [hSource]
          exact .tsFunctionLet (expressionIdentifierCheck_sound hName)
            (validateFunctionExpr_sound hValue)
      | assign target value =>
          cases target with
          | «local» name =>
              simp only [validateStmtCertificate, spanWithin,
                Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
                ⟨⟨⟨hLang, hWithin⟩, hName⟩, hSource⟩, hValue⟩
              have hLangEq : lang = .python := by simpa using hLang
              subst lang
              apply StmtDerives.ofSyntax
                ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
              rw [hSource]
              exact .pythonFunctionAssign
                (expressionIdentifierCheck_sound hName)
                (validateFunctionExpr_sound hValue)
          | _ => simp [validateStmtCertificate] at h
      | _ => simp [validateStmtCertificate] at h
  | augmentLocal exprSpan =>
      cases stmt with
      | augment target op value =>
          cases target with
          | «local» name =>
              cases op <;> simp [validateStmtCertificate] at h
              case add =>
                simp only [validateStmtCertificate, spanWithin,
                  Bool.and_eq_true, beq_iff_eq] at h
                rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
                  ⟨⟨⟨hLang, hWithin⟩, hName⟩, hSource⟩, hValue⟩
                have hLangEq : lang = .python := by simpa using hLang
                subst lang
                apply StmtDerives.ofSyntax
                  ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
                rw [hSource]
                exact .pythonAugmentAdd
                  (expressionIdentifierCheck_sound hName)
                  (validateFunctionExpr_sound hValue)
          | _ => simp [validateStmtCertificate] at h
      | _ => simp [validateStmtCertificate] at h
  | ifThen condSpan bodySpan bodyCert ih =>
      cases stmt with
      | ifThenElse condition yes no =>
          cases no with
          | empty =>
              simp only [validateStmtCertificate, spanWithin, Bool.and_eq_true,
                beq_iff_eq] at h
              rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩,
                ⟨⟨⟨⟨hCondWithin, hBodyWithin⟩, hOrder⟩,
                  hSource⟩, hCond⟩, hBody⟩
              have hBodySyntax := StmtDerives.syntax (ih hBody)
              apply StmtDerives.ofSyntax
                ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
              cases lang with
              | ts =>
                  simp only [Bool.and_eq_true] at hSource
                  rcases hSource with ⟨hSingle, hSource⟩
                  have hText : span.text source = "if (" ++
                      condSpan.text source ++ ") " ++ bodySpan.text source := by
                    simpa only [beq_iff_eq] using hSource
                  rw [hText]
                  exact .tsIfThen (validateFunctionExpr_sound hCond)
                    (singleStatementCheck_sound hSingle) hBodySyntax
              | python =>
                  simp only [Bool.and_eq_true] at hSource
                  rcases hSource with ⟨hSuite, hSource⟩
                  have hText : span.text source = "if " ++
                      condSpan.text source ++ ":\n        " ++
                        bodySpan.text source := by
                    simpa only [beq_iff_eq] using hSource
                  rw [hText]
                  exact .pythonIfThen (validateFunctionExpr_sound hCond)
                    hSuite hBodySyntax
          | _ => simp [validateStmtCertificate] at h
      | _ => simp [validateStmtCertificate] at h
  | ifThenIndented condSpan bodySpan indent bodyCert ih =>
      cases stmt with
      | ifThenElse condition yes no =>
          cases no with
          | empty =>
              simp only [validateStmtCertificate, spanWithin,
                Bool.and_eq_true, beq_iff_eq] at h
              rcases h with ⟨⟨hBoundsStart, hBoundsStop⟩, hRest⟩
              rcases hRest with ⟨hPrefix, hBody⟩
              rcases hPrefix with ⟨hPrefix, hCond⟩
              rcases hPrefix with ⟨hPrefix, hSource⟩
              rcases hPrefix with ⟨hPrefix, hSuite⟩
              rcases hPrefix with ⟨hPrefix, hIndentSpaces⟩
              rcases hPrefix with ⟨hPrefix, hIndentSteps⟩
              rcases hPrefix with ⟨hPrefix, hIndentLength⟩
              rcases hPrefix with ⟨hPrefix, hOrder⟩
              rcases hPrefix with ⟨hPrefix, hBodyWithin⟩
              rcases hPrefix with ⟨hLang, hCondWithin⟩
              have hLangEq : lang = .python := by simpa using hLang
              subst lang
              have hBodySyntax := StmtDerives.syntax (ih hBody)
              apply StmtDerives.ofSyntax
                ⟨(by simpa using hBoundsStart), (by simpa using hBoundsStop)⟩
              rw [hSource]
              exact .pythonIfThenIndented
                (by simpa using hIndentLength)
                (by simpa using hIndentSteps)
                hIndentSpaces
                (validateFunctionExpr_sound hCond) hSuite hBodySyntax
          | _ => simp [validateStmtCertificate] at h
      | _ => simp [validateStmtCertificate] at h

end Harmonia.Applications.Kadmos.Generated
