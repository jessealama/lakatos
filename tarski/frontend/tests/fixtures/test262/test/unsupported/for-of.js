// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A test written with a statement the evaluator does not have.
---*/

const $fake = "fake: exit 3 unsupported: ForOfStatement";

const xs = [1];
for (const x of xs) {
  print(x);
}
