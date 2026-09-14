// Copyright (C) 2026 the lakatos authors. All rights reserved.
/*---
description: A test written with an operator the evaluator does not have.
---*/

const $fake = "fake: exit 3 unsupported: DeleteExpression";

const o = { p: 1 };
delete o.p;
