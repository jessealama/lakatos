// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A negative test that completes instead of throwing.
negative:
  phase: runtime
  type: TypeError
---*/

const $fake = "fake: exit 0";

assert(true, "nothing is thrown here, which is the failure");
