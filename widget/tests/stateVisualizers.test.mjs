import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { test } from 'node:test';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';

// Rollup's browser bundles assume a window exists.
globalThis.window = {};
const { default: Ring } = await import('../js/ringVisualizer.js');
const { default: DieHard } = await import('../js/dieHardVisualizer.js');

const set = (...elements) => ({ $veil: 'set', elements });
const defaults = { theory: {}, instantiation: {}, hiddenFields: [], showRemovals: false };

// The saved thesis infoview used DOM serialization and random marker IDs; React
// uses self-closing tags and stable IDs. Normalize those two differences only.
function svgDigest(View, props) {
  const html = renderToStaticMarkup(createElement(View, { ...defaults, ...props }));
  const svg = html.match(/<svg\b[^]*?<\/svg>/)[0]
    .replace(/<([\w-]+)([^<>]*?)\/>/g, '<$1$2></$1>')
    .replace(/ring-arrow-:[^\s")]+:/g, 'ring-arrow-ID');
  return createHash('sha256').update(svg).digest('hex');
}

test('Ring matches both thesis counterexample frames', () => {
  const instantiation = { node: 'Fin 2' };
  const theory = { 'tot.le': set('(0, 0)', '(0, 1)', '(1, 1)') };
  const pre = { leader: set(0), pending: set('(0, 1)', '(1, 1)') };
  const post = { leader: set(0, 1), pending: set('(0, 1)') };
  assert.equal(svgDigest(Ring, { instantiation, theory, fields: pre }),
    '731283a8f9e96cdcf4683dc5ec12e9aa46036bf83d6861209f1e215784f09e2e');
  assert.equal(svgDigest(Ring, { instantiation, theory, fields: post, previous: pre }),
    'a4aa8c6d93eb9bf6f28dfd3bb7003033baf4f656af5ebaa47166d70a7b781efc');
});

test('DieHard matches every frame of the thesis solution trace', () => {
  const amounts = [[0, 0], [5, 0], [2, 3], [2, 0], [0, 2], [5, 2], [4, 3]];
  const frames = amounts.map(([big, small]) => ({ big, small }));
  assert.deepEqual(frames.map((fields, i) => svgDigest(DieHard, { fields, previous: frames[i - 1] })), [
    'f3a19317e1106b8354c0ca01d4840480d87bf6392359fb412e037d5e463981d0',
    '1944c135d9d72aaa867a86cb47f0e7169b7977db21c01d5449d448714bb5d2c9',
    '6a74a47a05675c98af9b709764b27d19a71ce2de2c3bd86cf96bf960ed068caa',
    'd06fe8a3e2b1ea1a99d34727ce97fd82e798d52fce88a0c2a96bb128dee3c97d',
    '11fa87005301322c28a5a9435a0baeee2f45b8e294ea03d4790149cb89d0f55c',
    '1014392eaf3f77a94563f4d78772e3da1081d6c6d37554746fc0283f62c15959',
    '044f5a2fdaaf5ae6396ff1d46dac6a8c60621d3eb84983a5bacb530691ea53cb',
  ]);
});

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
  // Node 0 is at the top. In the reversed ring its outgoing arrow points left to node 2.
  const edge = svg.match(/<path d="M \S+ \S+ Q \S+ \S+ (\S+) \S+" class="ring-edge"/);
  assert.ok(edge && Number(edge[1]) < 150, svg);
  assert.equal(renderToStaticMarkup(createElement(Ring, props, 'State fields')), 'State fields');
});
