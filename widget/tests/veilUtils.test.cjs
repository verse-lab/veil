const assert = require('assert').strict;
const fs = require('fs');
const path = require('path');
const Module = require('module');
const ts = require('typescript');
const React = require('react');
const { renderToStaticMarkup } = require('react-dom/server');

// Load the actual TSX modules with the compiler the widget build already uses.
function loadTsx(file, extraSource = '', requireOverride) {
  const sourcePath = path.resolve(__dirname, '../src', file);
  const compiled = ts.transpileModule(fs.readFileSync(sourcePath, 'utf8') + extraSource, {
    fileName: sourcePath,
    compilerOptions: {
      module: ts.ModuleKind.CommonJS,
      jsx: ts.JsxEmit.ReactJSX,
      target: ts.ScriptTarget.ES2022,
      esModuleInterop: true,
    },
  });
  const loaded = new Module(sourcePath, module);
  loaded.paths = Module._nodeModulePaths(path.dirname(sourcePath));
  if (requireOverride) loaded.require = requireOverride;
  loaded._compile(compiled.outputText, sourcePath);
  return loaded.exports;
}

const utils = loadTsx('veilUtils.tsx');
const { renderValue, renderValueInline, diffChanges, formatActionLabel, formatValue, deepEqual,
  logicalContainer } = utils;
// The trace row and the collapsed preview are internal to traceDisplay.tsx: export them for the
// test only, and stub the RPC-backed HtmlDisplay.
const { previewValue, KVRow } = loadTsx('traceDisplay.tsx', '\nexport { previewValue, KVRow };',
  (name) => {
    if (name === './veilUtils') return utils;
    if (name === './htmlDisplay') return { __esModule: true, default: () => null };
    return require(name);
  });

/** The text a reader sees, with React's HTML escaping undone. */
function visibleText(node) {
  return renderToStaticMarkup(node).replace(/<[^>]*>/g, '')
    .replace(/&quot;/g, '"').replace(/&#x27;/g, "'")
    .replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
}

const set = (...elements) => ({ $veil: 'set', elements });
const map = (...pairs) => ({ $veil: 'map', entries: pairs.map(([key, value]) => ({ key, value })) });
const multiset = (...pairs) => ({ $veil: 'multiset', entries: pairs.map(([element, count]) => ({ element, count })) });

// Strings are shown verbatim: no namespace stripping, which used to drop parentheses and make
// different values look the same.
for (const value of ['Msg.f (g a) b', 'Msg.f g (a b)', '#[some (Msg.response Reply 0 1)]', '<tag>&value']) {
  assert.equal(visibleText(renderValue(value)), value);
  assert.equal(visibleText(renderValueInline(value)), value);
  assert.equal(previewValue(value), value);
}
assert.notEqual(visibleText(renderValue('Msg.f (g a) b')), visibleText(renderValue('Msg.f g (a b)')));
assert.equal(previewValue('  line one\n  line two  '), ' line one line two ');
const longString = 'Namespace.Msg (' + 'x'.repeat(90) + ')';
assert.equal(previewValue(longString), longString.slice(0, 80) + '…');

// Objects (derived `ToJson` of inductives) read as the text output writes them.
const response = { response: { dat: 0, ses: 1 } };
assert.equal(formatValue({ client: { id: 0 } }), '{client: {id: 0}}');
assert.equal(formatActionLabel({ send: { m: response, to: 2 } }), 'send(m = {response: {dat: 0, ses: 1}}, to = 2)');
assert.equal(formatActionLabel('after_init'), 'after_init');

// Untagged sequences keep their behavior, including the per-row view of arrays of tuples.
const before = [['cloud', []], [{ client: { id: 0 } }, []]];
const after = [['cloud', []], [{ client: { id: 0 } }, [response]]];
assert.ok(renderToStaticMarkup(renderValue(after)).includes('<ul class="list">'));
assert.ok(visibleText(renderValue(after)).includes('{client: {id: 0}}'));
assert.equal(diffChanges({ chan: before }, { chan: after }).get('chan').type, 'array');

// Tagged containers render in set notation, also nested and inside ordinary values.
for (const [value, expected] of [
  [set(0, 1), '{0, 1}'],
  [map([0, 7]), '{0 ↦ 7}'],
  [multiset([1, 1], [2, 2]), '{1 × 1, 2 × 2}'],
  [map([[0, 1], set(2, 3)]), '{[0, 1] ↦ {2, 3}}'],
  [map([set(0, 1), multiset([2, 3])]), '{{0, 1} ↦ {2 × 3}}'],
  [[set(0, 1), map([2, multiset([3, 4])])], '[{0, 1}, {2 ↦ {3 × 4}}]'],
  [{ request: { targets: set(0, 1) } }, '{request: {targets: {0, 1}}}'],
  [set('<tag>&value', 'b'), '{<tag>&value, b}'],
  [set(), '{}'], [map(), '{}'], [multiset(), '{}'], [[], '[]'],
]) {
  assert.equal(formatValue(value), expected);
  assert.equal(visibleText(renderValue(value)), expected);
  assert.equal(visibleText(renderValueInline(value)), expected);
}
assert.equal(formatActionLabel({ send: { q: set(0, 1), m: map([2, multiset([3, 4])]) } }),
  'send(q = {0, 1}, m = {2 ↦ {3 × 4}})');

// Collapsing a structured value hides its contents, even when the expanded text is short.
// Multisets count distinct entries, not the sum of their multiplicities.
for (const [value, expected] of [
  [set(), 'Set(0)'],
  [set(0, 1), 'Set(2)'],
  [map(), 'Map(0)'],
  [map([0, 'start'], [1, 'start']), 'Map(2)'],
  [map([0, []], [1, [{ pc: 'cs', waker: 0 }]]), 'Map(2)'],
  [map(['long', 'x'.repeat(100)]), 'Map(1)'],
  [multiset(), 'Multiset(0 distinct)'],
  [multiset([1, 3], [2, 5]), 'Multiset(2 distinct)'],
  [{}, 'Object(0 fields)'],
  [{ request: { targets: set(0, 1) } }, 'Object(1 field)'],
  [{ pc: 'cs', waker: 0 }, 'Object(2 fields)'],
  [[], 'Array(0)'],
  [[0, 1], 'Array(2)'],
  [[[0, 1]], 'Array(1) of tuples'],
]) {
  assert.equal(previewValue(value), expected);
  assert.notEqual(previewValue(value), formatValue(value));
}

// Unknown or malformed envelopes stay ordinary objects.
for (const [value, expected] of [
  [{ $veil: 'unknown', elements: [] }, '{$veil: unknown, elements: []}'],
  [{ $veil: 'set', elements: [], extra: true }, '{$veil: set, elements: [], extra: true}'],
  [{ $veil: 'map', entries: [{ key: 0 }] }, '{$veil: map, entries: [{key: 0}]}'],
  [{ $veil: 'multiset', entries: [{ element: 0, count: -1 }] }, '{$veil: multiset, entries: [{element: 0, count: -1}]}'],
  [{ $veil: 'multiset', entries: [{ element: 0, count: 1.5 }] }, '{$veil: multiset, entries: [{element: 0, count: 1.5}]}'],
]) {
  assert.equal(logicalContainer(value), undefined);
  assert.equal(visibleText(renderValue(value)), expected);
  assert.equal(previewValue(value), `Object(${Object.keys(value).length} fields)`);
}

// A container longer than 80 characters gets one entry per row; a short one stays inline.
const big = map(...Array.from({ length: 12 }, (_, i) => [i, set(i, i + 1)]));
assert.ok(formatValue(big).length > 80);
const bigMarkup = renderToStaticMarkup(renderValue(big));
assert.ok(bigMarkup.startsWith('<ul class="list">'));
assert.equal((bigMarkup.match(/<li>/g) || []).length, 12);
assert.ok(visibleText(renderValue(big)).startsWith('0 ↦ {0, 1}1 ↦ {1, 2}'));
assert.ok(!renderToStaticMarkup(renderValue(set(0, 1))).includes('<ul'));

// Storage order is not a logical change; the order of a sequence still is.
for (const [prev, curr] of [
  [set(0, 1), set(1, 0)],
  [map([0, set(1, 2)], [1, 3]), map([1, 3], [0, set(2, 1)])],
  [multiset([0, 2], [1, 3]), multiset([1, 3], [0, 2])],
]) {
  assert.equal(deepEqual(prev, curr), true);
  assert.equal(diffChanges({ value: prev }, { value: curr }).size, 0);
}
assert.equal(deepEqual([0, 1], [1, 0]), false);
assert.equal(diffChanges({ value: set(0) }, { value: map([0, 1]) }).get('value').type, 'full');

// A changed map value or multiplicity keeps both the old and the new entry for highlighting.
for (const [prev, curr, expected, statuses] of [
  [set(0, 1), set(1, 2), '{1, 2, 0}', ['unchanged', 'added', 'removed']],
  [map([0, set(1)]), map([0, set(2)]), '{0 ↦ {1}, 0 ↦ {2}}', ['removed', 'added']],
  [multiset([0, 2]), multiset([0, 3]), '{0 × 2, 0 × 3}', ['removed', 'added']],
]) {
  const change = diffChanges({ value: prev }, { value: curr }).get('value');
  assert.equal(change.type, 'array');
  assert.deepEqual(change.mergedView.map(e => e.status), statuses);
  const rendered = renderValue(curr, change.mergedView);
  assert.equal(visibleText(rendered), expected);
  const html = renderToStaticMarkup(rendered);
  assert.ok(html.includes('changed-element'));
  assert.ok(html.includes('removed-element'));
  assert.equal(visibleText(renderValue(curr, change.mergedView.filter(e => e.status !== 'removed'))),
    visibleText(renderValue(curr)));
  assert.equal(visibleText(React.createElement(KVRow, {
    k: 'value', v: curr, changeInfo: change, showRemovals: true,
  })), `value↦▼${expected}`);
  assert.equal(visibleText(React.createElement(KVRow, {
    k: 'value', v: curr, changeInfo: change, showRemovals: false,
  })), `value↦▼${visibleText(renderValue(curr))}`);
}

// Highlighting also applies row by row in the per-row view.
const bigNext = map(...Array.from({ length: 12 }, (_, i) => [i, set(i, i + (i === 3 ? 2 : 1))]));
const bigChange = diffChanges({ value: big }, { value: bigNext }).get('value');
const bigDiff = renderToStaticMarkup(renderValue(bigNext, bigChange.mergedView));
assert.equal((bigDiff.match(/<li>/g) || []).length, 13);
assert.ok(bigDiff.includes('<code class="removed-element">3 ↦ {3, 4}</code>'));
assert.ok(bigDiff.includes('<code class="changed-element">3 ↦ {3, 5}</code>'));

console.log('veilUtils rendering regression tests passed');
