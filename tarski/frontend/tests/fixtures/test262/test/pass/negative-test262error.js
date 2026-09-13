// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: |
    A negative test whose class is the harness's own, which is not an
    Error subclass at all: the runner reads the name off the report.
negative:
  phase: runtime
  type: Test262Error
---*/

const $fake = "fake: exit 1 Uncaught Test262Error: m";

Test262Error.thrower("m");
