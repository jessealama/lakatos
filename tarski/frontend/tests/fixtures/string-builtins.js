"use strict";
const wrapped = new String("ab");
const parts = "a,b,,c".split(",", 3);
"Hello".toUpperCase() === "HELLO" &&
  "a,b".split(",").length === 2 &&
  "abc".at(-1) === "c" &&
  "x".padStart(3, "ab") === "abx" &&
  "\u{1F600}".length === 2 &&
  "abc".codePointAt(1) === 98 &&
  String.fromCharCode(65) === "A" &&
  "\u{1F600}"[0].charCodeAt(0) === 0xd83d &&
  "\ud83d" + "\ude00" === "\u{1F600}" &&
  "\u{10000}" < "￿" &&
  wrapped.length === 2 &&
  wrapped[1] === "b" &&
  Object.getOwnPropertyNames(wrapped).join() === "0,1,length" &&
  parts.join("|") === "a|b|" &&
  "x".replace("x", "$&$&") === "xx" &&
  "abcabc".lastIndexOf("bc") === 4 &&
  " a\t".trim() === "a" &&
  String.raw({ raw: ["a", "b"] }, 1) === "a1b" &&
  String.prototype.indexOf.call(123, "2") === 1;
