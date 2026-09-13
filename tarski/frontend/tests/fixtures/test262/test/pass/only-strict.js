// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: onlyStrict is the same run as the unflagged default here.
flags: [onlyStrict]
---*/

const $fake = "fake: exit 0";

assert.sameValue(typeof this, "undefined", "strict mode, no receiver");
