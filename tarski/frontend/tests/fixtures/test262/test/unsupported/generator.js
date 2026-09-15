// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A test written with a declaration form the evaluator does not have.
---*/

const $fake = "fake: exit 3 unsupported: FunctionDeclaration generator";

function* g() {
  yield 1;
}

for (const x of g()) {
  print(x);
}
