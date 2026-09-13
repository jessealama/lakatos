"use strict";
const counter = {
  n: 0,
  bump: function () {
    const step = () => {
      this.n = this.n + 1;
      return this.n;
    };
    return step();
  },
};
counter.bump();
counter.bump();
