// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A runtime-phase negative test that throws the class it declares.
negative:
  phase: runtime
  type: TypeError
---*/

const $fake = "fake: exit 1 Uncaught TypeError: t";

throw new TypeError("t");
