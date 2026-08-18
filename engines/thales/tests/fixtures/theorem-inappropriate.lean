import ThalesDsl

-- Mappable: function add(a: number, b: number): number { return a + b; }
ts_def "add" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["a"], ts.id["b"]))
}

-- Unmappable expression position:
--   function fetchTotal(x: number): number { return await remote(x); }
ts_def "fetchTotal" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.opaque["AwaitExpression"](2, 49))
}

-- Unmappable statement position:
--   function spin(n: number): number { while (true) {} return n; }
ts_def "spin" := ts.fn(ts.param["n"](ts.number)) : ts.number {
  ts.opaque["WhileStatement"](5, 36)
  ts.return(ts.id["n"])
}

-- A declaration after the failures still elaborates normally.
ts_def "sq" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}

#thales_prove "mixed.ts" "add" "forall (a b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10)), ts.binder["b"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["add"](ts.id["a"], ts.id["b"]), ts.call["add"](ts.id["b"], ts.id["a"]))
  }

#thales_prove "mixed.ts" "fetchTotal" "forall (x: int ∈ [0, 10)) { fetchTotal(x) >= 0 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.istrue(ts.binop[">="](ts.call["fetchTotal"](ts.id["x"]), ts.num[0]))
  }

#thales_prove "mixed.ts" "spin" "forall (n: int ∈ [0, 10)) { spin(n) ≡ n }" :=
  ts.forall(ts.binder["n"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["spin"](ts.id["n"]), ts.id["n"])
  }

#thales_prove "mixed.ts" "sq" "forall (x: int ∈ [-5, 5)) { sq(x) >= 0 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(-5, 5))) {
    ts.istrue(ts.binop[">="](ts.call["sq"](ts.id["x"]), ts.num[0]))
  }
