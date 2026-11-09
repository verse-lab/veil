import { useId, type PropsWithChildren } from 'react';
import type { StateViewProps } from './stateVisualization';
import { logicalContainer } from './veilUtils';

type Point = { x: number; y: number };
type Curve = { from: Point; to: Point; control: Point };
type Pending = [sender: number, destination: number];
type Message = { sender: number; dest: number; change: '' | 'added' | 'removed' };

const size = 300;
const center = size / 2;
const nodeRadius = 20;
const ringRadius = 90;

function members(value: unknown): unknown[] | undefined {
  const container = logicalContainer(value);
  if (container?.kind === 'set') return container.items;
  if (Array.isArray(value)) return value;
}

function isNode(value: unknown, count: number): value is number {
  return typeof value === 'number' && Number.isSafeInteger(value) && value >= 0 && value < count;
}

function nodeTuple(value: unknown, arity: number, count: number): number[] | undefined {
  // Products may be arrays or the displayed Repr of a tuple of Fin values.
  if (typeof value === 'string' && /^\([0-9, ()]+\)$/.test(value)) {
    value = value.match(/\d+/g)?.map(Number);
  }
  if (!Array.isArray(value)) return undefined;
  const tuple: unknown[] = value.flat(Infinity);
  if (tuple.length === arity && tuple.every(node => isNode(node, count))) return tuple;
}

function readPending(value: unknown, count: number): Pending[] | undefined {
  const entries = members(value);
  if (!entries) return undefined;

  const pending: Pending[] = [];
  for (const entry of entries) {
    const pair = nodeTuple(entry, 2, count);
    if (!pair) return undefined;
    pending.push([pair[0], pair[1]]);
  }
  return pending;
}

function theoryRelation(theory: StateViewProps['theory'], instance: string, relation: string) {
  function lookup(name: string) {
    const qualified = Object.keys(theory).find(key => key.endsWith(`.${name}`));
    return theory[name] ?? (qualified ? theory[qualified] : undefined);
  }
  return members(lookup(`${instance}.${relation}`) ?? lookup(relation));
}

function ringSuccessors(theory: StateViewProps['theory'], nodes: number[]) {
  const count = nodes.length;
  if (count <= 2) return nodes.map(node => (node + 1) % count);

  const between = theoryRelation(theory, 'btwn', 'btw');
  if (!between) return undefined;
  const triples = new Set<string>();
  for (const entry of between) {
    const triple = nodeTuple(entry, 3, count);
    if (triple) triples.add(triple.join(','));
  }

  // Ring.isNext: from the source, the successor lies before every other node.
  const successors = nodes.map(from => nodes.find(to => to !== from &&
    nodes.every(other => other === from || other === to || triples.has(`${from},${to},${other}`))));
  return successors.every(to => to !== undefined) ? successors : undefined;
}

function nodeRanks(theory: StateViewProps['theory'], count: number) {
  const lessOrEqual = theoryRelation(theory, 'tot', 'le') ?? [];
  const lowerNodes = Array.from({ length: count }, () => new Set<number>());
  for (const entry of lessOrEqual) {
    const pair = nodeTuple(entry, 2, count);
    if (pair) lowerNodes[pair[1]].add(pair[0]);
  }
  return lowerNodes.map(nodes => nodes.size);
}

function messageChanges(current: Pending[], previous: Pending[] | undefined, showRemovals: boolean): Message[] {
  const key = (pair: Pending) => pair.join(',');
  const before = previous && new Set(previous.map(key));
  const messages = current.map(([sender, dest]): Message => ({
    sender, dest, change: before && !before.has(key([sender, dest])) ? 'added' : '',
  }));
  if (previous && showRemovals) {
    const after = new Set(current.map(key));
    for (const [sender, dest] of previous) {
      if (!after.has(key([sender, dest]))) messages.push({ sender, dest, change: 'removed' });
    }
  }
  return messages;
}

function nodePosition(index: number, count: number): Point {
  const angle = index * 2 * Math.PI / count - Math.PI / 2;
  return { x: center + ringRadius * Math.cos(angle), y: center + ringRadius * Math.sin(angle) };
}

function curveBetween(from: Point, to: Point): Curve | undefined {
  if (from === to) return undefined;
  const midX = (from.x + to.x) / 2;
  const midY = (from.y + to.y) / 2;
  const dx = midX - center;
  const dy = midY - center;
  const distance = Math.sqrt(dx * dx + dy * dy);
  const curvature = 0.15;

  // A diameter has no outward midpoint direction. Bend to the left of the edge instead.
  if (distance < 1) {
    const edgeX = to.x - from.x;
    const edgeY = to.y - from.y;
    const length = Math.sqrt(edgeX * edgeX + edgeY * edgeY);
    const offset = length * curvature * 1.5;
    return { from, to, control: { x: midX + (-edgeY / length) * offset, y: midY + (edgeX / length) * offset } };
  }

  return { from, to, control: {
    x: midX + (dx / distance) * curvature * distance,
    y: midY + (dy / distance) * curvature * distance,
  } };
}

function inset(point: Point, toward: Point, amount: number): Point {
  const dx = point.x - toward.x;
  const dy = point.y - toward.y;
  const length = Math.sqrt(dx * dx + dy * dy);
  return { x: point.x - (dx / length) * amount, y: point.y - (dy / length) * amount };
}

function edgePath({ from, to, control }: Curve): string {
  const start = inset(from, control, nodeRadius + 4);
  const end = inset(to, control, nodeRadius + 8);
  return `M ${start.x} ${start.y} Q ${control.x} ${control.y} ${end.x} ${end.y}`;
}

function messagePosition({ from, to, control }: Curve, t: number): Point {
  const s = 1 - t;
  const x = s * s * from.x + 2 * s * t * control.x + t * t * to.x;
  const y = s * s * from.y + 2 * s * t * control.y + t * t * to.y;
  const dx = 2 * s * (control.x - from.x) + 2 * t * (to.x - control.x);
  const dy = 2 * s * (control.y - from.y) + 2 * t * (to.y - control.y);
  const length = Math.sqrt(dx * dx + dy * dy);
  const normalX = -dy / length;
  const normalY = dx / length;
  // Put messages on the side of the curve facing away from the center.
  const direction = normalX * (center - x) + normalY * (center - y) > 0 ? -1 : 1;
  return { x: x + normalX * direction * 35, y: y + normalY * direction * 35 };
}

function Crown({ x, y }: Point) {
  return (
    <g className="ring-crown" transform={`translate(${x - 8}, ${y - 16 - 8})`}>
      <path d="M0,16 L3.2,6.4 L8,11.2 L12.8,6.4 L16,16 Z" fill="#FFD700" stroke="#DAA520" strokeWidth={1} />
      <circle cx={1.6} cy={5.6} r={2} fill="#DAA520" />
      <circle cx={8} cy={9.6} r={2} fill="#DAA520" />
      <circle cx={14.4} cy={5.6} r={2} fill="#DAA520" />
    </g>
  );
}

function MessageBox({ sender, dest, change, x, y }: Message & Point) {
  return (
    <g className={`ring-message ${change}`} transform={`translate(${x - 25}, ${y - 14})`}>
      <rect x={0} y={0} width={50} height={28} rx={3} ry={3} className="ring-message-bg" />
      <text x={6} y={12} className="ring-message-text">{`id: ${sender}`}</text>
      <text x={6} y={24} className="ring-message-text">{`to: ${dest}`}</text>
    </g>
  );
}

export default function RingVisualizer({
  fields, previous, instantiation, theory, showRemovals, hiddenFields, children,
}: PropsWithChildren<StateViewProps>) {
  const markerId = `ring-arrow-${useId()}`;
  const nodeType = instantiation.node;
  const count = typeof nodeType === 'string' ? Number(/^Fin\s+(\d+)$/.exec(nodeType)?.[1]) : NaN;
  if (!Number.isSafeInteger(count) || count <= 0) return children;

  const showPending = !hiddenFields.includes('pending');
  const pending = showPending ? readPending(fields.pending, count) : [];
  const leaders = hiddenFields.includes('leader') ? [] : members(fields.leader);
  if (!pending || !leaders || !leaders.every(node => isNode(node, count))) return children;

  const before = showPending ? readPending(previous?.pending, count) : undefined;
  const byDestination = new Map<number, Message[]>();
  for (const message of messageChanges(pending, before, showRemovals)) {
    const group = byDestination.get(message.dest);
    if (group) group.push(message);
    else byDestination.set(message.dest, [message]);
  }

  const nodes = Array.from({ length: count }, (_, i) => i);
  const positions = nodes.map(node => nodePosition(node, count));
  const ranks = nodeRanks(theory, count);
  const maxRank = ranks.reduce((max, rank) => Math.max(max, rank), 0);
  const leaderSet = new Set(leaders);
  const successors = ringSuccessors(theory, nodes);
  if (!successors) return children;
  const incoming = new Map<number, Curve>();
  const edges = nodes.map(from => {
    const dest = successors[from];
    const curve = curveBetween(positions[from], positions[dest]);
    if (curve && !incoming.has(dest)) incoming.set(dest, curve);
    return curve;
  });

  return (
    <>
      <style>{styles}</style>
      <div className="ring-visualizer-container">
        <svg width={size} height={size} viewBox={`0 0 ${size} ${size}`} className="ring-svg">
          <defs>
            <marker id={markerId} viewBox="0 0 10 10" refX={9} refY={5} markerWidth={6} markerHeight={6} orient="auto-start-reverse">
              <path d="M 0 0 L 10 5 L 0 10 z" className="ring-arrow" />
            </marker>
          </defs>
          {edges.map((curve, from) => curve && (
            <path key={from} d={edgePath(curve)} className="ring-edge" markerEnd={`url(#${markerId})`} />
          ))}
          {Array.from(byDestination, ([dest, messages]) => {
            const position = positions[dest];
            const curve = incoming.get(dest) ?? curveBetween(positions[(dest - 1 + count) % count], position);
            return messages.map((message, i) => {
              const t = 0.5 + (i - (messages.length - 1) / 2) * 0.35;
              const point = curve ? messagePosition(curve, t) : { x: position.x + 48, y: position.y };
              return <MessageBox key={`${dest}-${i}`} {...message} {...point} />;
            });
          })}
          {positions.map(({ x, y }, node) => {
            const rank = ranks[node];
            const radius = rank > 0 && maxRank > 1
              ? nodeRadius * (0.7 + 0.6 * (rank - 1) / (maxRank - 1))
              : nodeRadius;
            return (
              <g key={node} className="ring-node-group">
                {leaderSet.has(node) && <Crown x={x} y={y - radius} />}
                <circle cx={x} cy={y} r={radius} className="ring-node" />
                <text x={x} y={y} className="ring-node-label" textAnchor="middle" dominantBaseline="central">{node}</text>
              </g>
            );
          })}
        </svg>
      </div>
    </>
  );
}

const styles = `
.ring-visualizer-container {
  display: flex;
  flex-direction: column;
}
.ring-svg {
  max-width: 100%;
  height: auto;
  background: var(--vscode-editor-background, #1e1e1e);
  border-radius: 8px;
}
.ring-node {
  fill: var(--vscode-activityBarBadge-background, #007acc);
  stroke: var(--vscode-panel-border, #454545);
  stroke-width: 2;
}
.ring-node-label {
  fill: var(--vscode-activityBarBadge-foreground, #fff);
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 12px;
  font-weight: 600;
}
.ring-edge {
  fill: none;
  stroke: var(--vscode-descriptionForeground, #888);
  stroke-width: 2;
}
.ring-arrow {
  fill: var(--vscode-descriptionForeground, #888);
}
.ring-crown {
  filter: drop-shadow(0 1px 2px rgba(0, 0, 0, 0.3));
}
.ring-message-bg {
  fill: var(--vscode-editorWidget-background, #252526);
  stroke: var(--vscode-panel-border, #454545);
  stroke-width: 1;
}
.ring-message-text {
  fill: var(--vscode-foreground, #ccc);
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 9px;
}
.ring-message.added .ring-message-bg {
  fill: var(--vscode-diffEditor-insertedTextBackground, rgba(0, 255, 0, 0.2));
  stroke: var(--vscode-diffEditor-insertedLineBackground, rgba(0, 255, 0, 0.5));
  stroke-width: 2;
}
.ring-message.removed .ring-message-bg {
  fill: var(--vscode-diffEditor-removedTextBackground, rgba(255, 0, 0, 0.2));
  stroke: var(--vscode-diffEditor-removedLineBackground, rgba(255, 0, 0, 0.5));
  stroke-width: 2;
}
.ring-message.removed .ring-message-text {
  text-decoration: line-through;
  opacity: 0.7;
}
`;
