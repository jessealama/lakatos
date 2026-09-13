// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: |
    A caller of a $262 hook the epic puts out of scope. The decoder
    refuses it by name, so this is unsupported and not a failure.
---*/

const $fake = "fake: exit 3 unsupported: $262.evalScript";

$262.evalScript("1");
