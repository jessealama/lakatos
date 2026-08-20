import ThalesDsl

-- Pure-arithmetic model: function add(a: number, b: number): number { return a + b; }
ts_def "add" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["a"], ts.id["b"]))
}

-- Commutativity over a bounded domain: decidable, so decide yields Theorem.
#thales_prove "arith.ts" "add" "forall (a b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10)), ts.binder["b"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["add"](ts.id["a"], ts.id["b"]), ts.call["add"](ts.id["b"], ts.id["a"]))
  }

-- Boolean islands, one per comparison operator, over a range with negative
-- endpoints.
#thales_prove "arith.ts" "add" "forall (a: int ∈ [-5, 5)) { add(a, 1) > a }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(-5, 5))) {
    ts.istrue(ts.binop[">"](ts.call["add"](ts.id["a"], ts.num[1]), ts.id["a"]))
  }

#thales_prove "arith.ts" "add" "forall (a: int ∈ [-5, 5)) { a < add(a, 1) }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(-5, 5))) {
    ts.istrue(ts.binop["<"](ts.id["a"], ts.call["add"](ts.id["a"], ts.num[1])))
  }

#thales_prove "arith.ts" "add" "forall (a: int ∈ [-5, 5)) { add(a, 0) <= a }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(-5, 5))) {
    ts.istrue(ts.binop["<="](ts.call["add"](ts.id["a"], ts.num[0]), ts.id["a"]))
  }

#thales_prove "arith.ts" "add" "forall (a: int ∈ [-5, 5)) { add(a, 0) >= a }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(-5, 5))) {
    ts.istrue(ts.binop[">="](ts.call["add"](ts.id["a"], ts.num[0]), ts.id["a"]))
  }

#thales_prove "arith.ts" "add" "forall (a: int ∈ [-5, 5)) { add(a, 0) === a }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(-5, 5))) {
    ts.istrue(ts.binop["==="](ts.call["add"](ts.id["a"], ts.num[0]), ts.id["a"]))
  }

#thales_prove "arith.ts" "add" "forall (a: int ∈ [-5, 5)) { add(a, 1) !== a }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(-5, 5))) {
    ts.istrue(ts.binop["!=="](ts.call["add"](ts.id["a"], ts.num[1]), ts.id["a"]))
  }

-- Binder values coerce into a Float body. Doubling is exact for every
-- representable integer, so this proves.
ts_def "dbl" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["x"], ts.id["x"]))
}
#thales_prove "coerce.ts" "dbl" "doubles" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 40))) {
    ts.eq(ts.call["dbl"](ts.id["x"]), ts.binop["*"](ts.id["x"], ts.num[2]))
  }

-- Nested ∀-properties (binders introduced by separate foralls).
#thales_prove "arith.ts" "add" "forall (a: int ∈ [0, 5)) { forall (b: int ∈ [0, 5)) { add(a, b) ≡ add(b, a) } }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 5))) {
    ts.forall(ts.binder["b"](ts.int, ts.range(0, 5))) {
      ts.eq(ts.call["add"](ts.id["a"], ts.id["b"]), ts.call["add"](ts.id["b"], ts.id["a"]))
    }
  }
