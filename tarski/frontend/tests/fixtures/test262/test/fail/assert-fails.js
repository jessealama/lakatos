// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A test whose assertion does not hold.
---*/

const $fake = "fake: exit 1 Uncaught Test262Error: boom";

assert(false, "boom");
