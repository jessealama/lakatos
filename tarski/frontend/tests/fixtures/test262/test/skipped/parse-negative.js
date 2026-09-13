// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: |
    The parser is TypeScript's, not this evaluator's, so a parse-phase
    negative test says nothing about the evaluator and is not scored.
negative:
  phase: parse
  type: SyntaxError
---*/

$DONOTEVALUATE();

var var var;
