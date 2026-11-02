"use strict";
const assert = require("node:assert/strict");
const {histogram} = require("./assets/stats.js");

assert.deepEqual(histogram({A: 0, B: 0}, "20"), [{min: 0, max: 0, count: 2}]);
assert.deepEqual(histogram({A: 0, B: 2, C: 2, D: 1000}, "exact"), [
  {min: 0, max: 0, count: 1}, {min: 2, max: 2, count: 2},
  {min: 1000, max: 1000, count: 1},
]);
assert.throws(() => histogram({bad: -1}, "20"));
assert.throws(() => histogram({bad: 1.5}, "20"));
assert.throws(() => histogram({fine: 1}, "3"));
let seed = 14;
for (let iteration = 0; iteration < 50; iteration++) {
  const values = {};
  for (let i = 0; i < 200; i++) {
    seed = (seed * 1664525 + 1013904223) >>> 0;
    values[`declaration${i}`] = seed % (iteration * 53 + 1);
  }
  for (const choice of ["10", "20", "50", "exact"]) {
    const bins = histogram(values, choice);
    assert.equal(bins[0].min, 0);
    assert.equal(bins[0].max, 0);
    assert.equal(bins.reduce((sum, bin) => sum + bin.count, 0), 200);
    if (choice !== "exact") assert.ok(bins.length <= Number(choice));
    for (const value of Object.values(values)) {
      assert.equal(bins.filter(b => value >= b.min && value <= b.max).length, 1);
    }
    for (const bin of bins) {
      assert.equal(bin.count, Object.values(values).filter(v => v >= bin.min && v <= bin.max).length);
    }
  }
}
console.log("Histogram: zero, exact counts, grouped ranges and membership checks passed");
