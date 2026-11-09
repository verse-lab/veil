import assert from 'node:assert/strict';
import { test } from 'node:test';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';

// Rollup's browser bundles assume a window exists.
globalThis.window = {};
const { default: Ring } = await import('../js/ringVisualizer.js');
const { default: DieHard } = await import('../js/dieHardVisualizer.js');

const set = (...elements) => ({ $veil: 'set', elements });
const defaults = { theory: {}, instantiation: {}, hiddenFields: [], showRemovals: false };

test('DieHard hides a jug without showing a zero amount or its goal', () => {
  const html = renderToStaticMarkup(createElement(DieHard, {
    ...defaults, fields: { big: 4, small: 2 }, hiddenFields: ['big'],
  }));
  assert.match(html, /class="jug-label"[^>]*>Small<\/text>/);
  assert.match(html, /class="jug-amount"[^>]*>2<\/text>/);
  assert.doesNotMatch(html, /class="jug-label"[^>]*>Big<\/text>|<g class="goal-indicator"/);
});

test('Ring draws the supplied topology and leaves missing topology to the field view', () => {
  const props = { ...defaults, instantiation: { node: 'Fin 3' }, fields: { leader: set(), pending: set() } };
  const theory = { 'btwn.btw': set([0, 2, 1], [2, 1, 0], [1, 0, 2]) };
  const svg = renderToStaticMarkup(createElement(Ring, { ...props, theory }));
  const edge = svg.match(/<path d="M \S+ \S+ Q \S+ \S+ (\S+) (\S+)" class="ring-edge"/);
  assert.ok(edge, 'node 0 should have an outgoing edge');
  const nodes = [...svg.matchAll(/<circle cx="([^"]+)" cy="([^"]+)"[^>]*class="ring-node"/g)];
  assert.equal(nodes.length, 3);
  const distanceToArrow = ([, x, y]) => Math.hypot(Number(x) - Number(edge[1]), Number(y) - Number(edge[2]));
  assert.ok(distanceToArrow(nodes[2]) < distanceToArrow(nodes[1]), 'node 0 should point to node 2');
  assert.equal(renderToStaticMarkup(createElement(Ring, props, 'State fields')), 'State fields');
});
