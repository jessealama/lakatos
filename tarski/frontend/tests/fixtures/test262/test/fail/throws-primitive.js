// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: |
    An uncaught primitive has no class name to read, so the report
    carries none and the test fails on what it threw.
---*/

const $fake = "fake: exit 1 Uncaught 1";

throw 1;
