"use strict";
// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A raw test that is already strict, run alone and unmodified.
flags: [raw]
---*/

const $fake = "fake: exit 0";

if (1 + 1 !== 2) {
  throw new Error("raw tests get no harness, so there is no assert here");
}
