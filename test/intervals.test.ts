import { describe, expect, it } from 'vitest';
import fc from 'fast-check';
import { mergeIntervals, type Interval } from '../src/intervals';

// Read the spec in src/intervals/mergeIntervals.ts, then check your progress
// with `npm run mutants:intervals`.
//
// Label every property with its pattern, on the line above its `it(`:
//   // Pattern: invariant. The output is sorted.
// (invariant, algebraic, metamorphic, differential, or conditional)

// the old generator made stuff like [5, -3] where start > end, which breaks the
// precondition. so now we build valid intervals directly: pick a start and a
// length, end = start + length. small range on purpose so intervals overlap and
// share endpoints a lot (that's where the edge case bugs live).
const interval: fc.Arbitrary<Interval> = fc
  .tuple(fc.integer({ min: -20, max: 20 }), fc.nat(8))
  .map(([s, len]): Interval => [s, s + len]);
const intervalList = fc.array(interval, { maxLength: 12 });

// same thing but sometimes duplicates intervals and sometimes adds ones that
// touch exactly at an endpoint, so we hit those cases way more often
const trickyList = intervalList.chain(xs =>
  fc
    .array(
      fc.oneof(
        fc.constantFrom(...(xs.length ? xs : [[0, 0] as Interval])),
        fc.tuple(fc.constantFrom(...(xs.length ? xs : [[0, 0] as Interval])), fc.nat(5)).map(
          ([[, e], len]): Interval => [e, e + len],
        ),
        interval,
      ),
      { maxLength: 6 },
    )
    .chain(extra => fc.shuffledSubarray([...xs, ...extra], { minLength: xs.length + extra.length, maxLength: xs.length + extra.length })),
);

// simple, obviously right check for "is point p covered"
const covers = (xs: readonly Interval[], p: number) => xs.some(([s, e]) => s <= p && p <= e);

// disjoint intervals with a real gap between each one (gap >= 1 so they don't touch)
const gappedList = fc
  .tuple(
    fc.integer({ min: -20, max: 20 }),
    fc.array(fc.tuple(fc.nat(6), fc.integer({ min: 1, max: 4 })), { maxLength: 8 }),
  )
  .map(([start, parts]) => {
    const out: Interval[] = [];
    let cur = start;
    for (const [len, gap] of parts) {
      out.push([cur, cur + len]);
      cur = cur + len + gap + 1;
    }
    return out;
  });

describe('mergeIntervals', () => {
  // Pattern: invariant. Every input interval lies inside some output interval.
  it('every input interval lies inside some output interval', () => {
    fc.assert(
      fc.property(trickyList, xs => {
        const out = mergeIntervals(xs);
        const uncovered = xs.filter(([s, e]) => !out.some(([a, b]) => a <= s && e <= b));
        expect(uncovered).toEqual([]);
      }),
    );
  });

  // Pattern: invariant. Output is sorted, each interval is valid, and neighbours
  // don't overlap or touch (out[i][1] < out[i+1][0]).
  it('output is sorted and strictly disjoint', () => {
    fc.assert(
      fc.property(trickyList, xs => {
        const out = mergeIntervals(xs);
        for (const [s, e] of out) {
          expect(Number.isInteger(s) && Number.isInteger(e)).toBe(true);
          expect(s).toBeLessThanOrEqual(e);
        }
        for (let i = 0; i + 1 < out.length; i++) {
          expect(out[i][1]).toBeLessThan(out[i + 1][0]);
        }
      }),
    );
  });

  // Pattern: differential. Every point (integers and the halves between them, which
  // stand in for all the real numbers in each gap) is covered by the output
  // exactly when it's covered by the input.
  it('covers exactly the same points as the input', () => {
    fc.assert(
      fc.property(trickyList, xs => {
        const out = mergeIntervals(xs);
        for (let p = -25; p <= 50; p += 0.5) {
          expect([p, covers(out, p)]).toEqual([p, covers(xs, p)]);
        }
      }),
    );
  });

  // Pattern: metamorphic. Shuffling the input or duplicating it doesn't change the output.
  it('order and duplicates in the input do not matter', () => {
    fc.assert(
      fc.property(
        trickyList.chain(xs =>
          fc.tuple(fc.constant(xs), fc.shuffledSubarray(xs, { minLength: xs.length, maxLength: xs.length })),
        ),
        ([xs, shuffled]) => {
          const expected = mergeIntervals(xs);
          expect(mergeIntervals(shuffled)).toEqual(expected);
          expect(mergeIntervals([...xs, ...shuffled])).toEqual(expected);
        },
      ),
    );
  });

  // Pattern: algebraic. Merging an already merged list gives back the same list (idempotent).
  it('merging twice is the same as merging once', () => {
    fc.assert(
      fc.property(trickyList, xs => {
        const once = mergeIntervals(xs);
        expect(mergeIntervals(once)).toEqual(once);
      }),
    );
  });

  // Pattern: conditional. If the intervals already don't overlap or touch, the output
  // is just the input sorted by start.
  it('already disjoint input comes back sorted and unchanged', () => {
    fc.assert(
      fc.property(
        gappedList.chain(xs =>
          fc.tuple(fc.constant(xs), fc.shuffledSubarray(xs, { minLength: xs.length, maxLength: xs.length })),
        ),
        ([sorted, shuffled]) => {
          expect(mergeIntervals(shuffled)).toEqual(sorted);
        },
      ),
    );
  });

  // Pattern: conditional. If two intervals touch exactly at one endpoint they merge into one.
  it('intervals that touch at an endpoint merge', () => {
    fc.assert(
      fc.property(fc.integer({ min: -20, max: 20 }), fc.nat(6), fc.nat(6), (s, a, b) => {
        expect(mergeIntervals([[s, s + a], [s + a, s + a + b]])).toEqual([[s, s + a + b]]);
        expect(mergeIntervals([[s + a, s + a + b], [s, s + a]])).toEqual([[s, s + a + b]]);
      }),
    );
  });

  // Pattern: invariant. The input array and the intervals in it are not modified.
  it('does not modify the input', () => {
    fc.assert(
      fc.property(trickyList, xs => {
        const copy = xs.map(([s, e]): Interval => [s, e]);
        mergeIntervals(xs);
        expect(xs).toEqual(copy);
      }),
    );
  });

  // Pattern: conditional. Invalid input (start > end, or non integer endpoints) throws a RangeError.
  it('throws RangeError on invalid intervals', () => {
    const bad: fc.Arbitrary<Interval> = fc.oneof(
      fc.tuple(fc.integer({ min: -20, max: 20 }), fc.integer({ min: 1, max: 8 })).map(([s, d]): Interval => [s, s - d]),
      fc.tuple(fc.integer({ min: -20, max: 20 }), fc.nat(5)).map(([s, len]): Interval => [s + 0.5, s + len + 1]),
      fc.tuple(fc.integer({ min: -20, max: 20 }), fc.nat(5)).map(([s, len]): Interval => [s, s + len + 0.5]),
      fc.constantFrom<Interval>([NaN, 1], [0, NaN], [0, Infinity], [-Infinity, 0]),
    );
    fc.assert(
      fc.property(intervalList, bad, intervalList, (before, b, after) => {
        expect(() => mergeIntervals([...before, b, ...after])).toThrow(RangeError);
      }),
    );
  });

  // Pattern: conditional. Empty input gives empty output.
  it('empty input gives empty output', () => {
    expect(mergeIntervals([])).toEqual([]);
  });
});
