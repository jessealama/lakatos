// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A negative test that throws a class other than the one it declares.
negative:
  phase: runtime
  type: TypeError
---*/

const $fake = "fake: exit 1 Uncaught RangeError: r";

throw new RangeError("r");
