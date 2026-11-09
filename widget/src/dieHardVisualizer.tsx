import { Fragment, type PropsWithChildren } from 'react';
import type { StateViewProps } from './stateVisualization';

function Jug({ x, capacity, label, amount, previous }: {
  x: number;
  capacity: number;
  label: string;
  amount: number;
  previous: unknown;
}) {
  const width = 70;
  const bottom = 200;
  const height = 28 * capacity;
  const top = bottom - height;
  const wall = 4;
  const innerBottom = bottom - wall;
  const innerRight = x + width - wall;
  const innerWidth = width - 2 * wall;
  const innerHeight = height - wall;
  const waterHeight = (amount / capacity) * innerHeight;
  const waterY = innerBottom - waterHeight;
  const delta = typeof previous === 'number' ? amount - previous : 0;
  const change = delta > 0 ? 'added' : delta < 0 ? 'removed' : '';

  const outline = `
    M ${x} ${top}
    L ${x} ${bottom}
    L ${x + width} ${bottom}
    L ${x + width} ${top}
    L ${innerRight} ${top}
    L ${innerRight} ${innerBottom}
    L ${x + wall} ${innerBottom}
    L ${x + wall} ${top}
    Z
  `;

  return (
    <g className="jug-group">
      <path d={outline} className={`jug-body ${change && `jug-changed-${change}`}`} />
      {amount > 0 && <>
        <rect x={x + wall} y={waterY} width={innerWidth} height={waterHeight} className="jug-water" rx={2} />
        <rect x={x + wall + 2} y={waterY} width={innerWidth - 4} height={3} className="water-surface" />
      </>}
      {Array.from({ length: capacity }, (_, index) => {
        const mark = index + 1;
        const markY = innerBottom - (mark / capacity) * innerHeight;
        const markWidth = mark === capacity ? 15 : 10;
        return (
          <Fragment key={mark}>
            <line x1={innerRight} y1={markY} x2={innerRight + markWidth} y2={markY} className="jug-mark" />
            <text x={x + width + 20} y={markY + 4} className="jug-mark-label">{mark}</text>
          </Fragment>
        );
      })}
      <text x={x + width / 2} y={bottom + 30} className="jug-label" textAnchor="middle">{label}</text>
      <text x={x + width / 2} y={bottom + 48} className="jug-capacity" textAnchor="middle">{`(${capacity} gal)`}</text>
      <text x={x + width / 2} y={top + height / 2} className="jug-amount" textAnchor="middle" dominantBaseline="central">
        {amount}
      </text>
      {change && (
        <text x={x - 8} y={top + 16} className={`jug-delta delta-${change}`} textAnchor="end">
          {delta > 0 ? `+${delta}` : delta}
        </text>
      )}
    </g>
  );
}

export default function DieHardVisualizer({
  fields, previous, hiddenFields, children,
}: PropsWithChildren<StateViewProps>) {
  const { big, small } = fields;
  if (typeof big !== 'number' || typeof small !== 'number') return children;

  const showBig = !hiddenFields.includes('big');
  const showSmall = !hiddenFields.includes('small');
  if (!showBig && !showSmall) return children;
  const solved = big === 4;

  return (
    <>
      <style>{styles}</style>
      <svg width={320} height={280} viewBox="0 0 320 280" className="diehard-svg">
        {showBig && (
          <g className="goal-indicator" transform="translate(90, 10)">
            <rect x={0} y={0} width={140} height={36} rx={6} className={solved ? 'goal-achieved' : 'goal-pending'} />
            <text x={70} y={22} className="goal-text" textAnchor="middle">{solved ? 'SOLVED!' : 'Goal: Big = 4'}</text>
          </g>
        )}
        {showSmall && <Jug x={60} capacity={3} label="Small" amount={small} previous={previous?.small} />}
        {showBig && <Jug x={190} capacity={5} label="Big" amount={big} previous={previous?.big} />}
      </svg>
    </>
  );
}

const styles = `
.diehard-svg {
  max-width: 100%;
  height: auto;
  background: var(--vscode-editor-background, #1e1e1e);
  border-radius: 8px;
}
.diehard-svg .jug-body {
  fill: var(--vscode-editorWidget-background, #252526);
  stroke: var(--vscode-panel-border, #454545);
  stroke-width: 2;
  opacity: 0.9;
}
/* Jug border highlights when changed - green for added, orange for removed */
.diehard-svg .jug-body.jug-changed-added {
  stroke: var(--vscode-charts-green, #89d185);
  stroke-width: 3;
}
.diehard-svg .jug-body.jug-changed-removed {
  stroke: var(--vscode-charts-orange, #cca700);
  stroke-width: 3;
}
/* Water is always blue - it's just water */
.diehard-svg .jug-water {
  fill: var(--vscode-charts-blue, #3794ff);
  opacity: 0.8;
}
.diehard-svg .water-surface {
  fill: var(--vscode-charts-blue, #5ba9ff);
  opacity: 0.5;
}
.diehard-svg .jug-mark {
  stroke: var(--vscode-descriptionForeground, #888);
  stroke-width: 1;
}
.diehard-svg .jug-mark-label {
  fill: var(--vscode-descriptionForeground, #888);
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 10px;
}
.diehard-svg .jug-label {
  fill: var(--vscode-foreground, #ccc);
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 14px;
  font-weight: 600;
}
.diehard-svg .jug-capacity {
  fill: var(--vscode-descriptionForeground, #888);
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 11px;
}
.diehard-svg .jug-amount {
  fill: var(--vscode-activityBarBadge-foreground, #fff);
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 24px;
  font-weight: bold;
  text-shadow: 0 1px 3px rgba(0, 0, 0, 0.5);
}
/* Delta indicator above jugs showing +X or -X */
.diehard-svg .jug-delta {
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 16px;
  font-weight: bold;
}
.diehard-svg .jug-delta.delta-added {
  fill: var(--vscode-charts-green, #89d185);
}
.diehard-svg .jug-delta.delta-removed {
  fill: var(--vscode-charts-orange, #cca700);
}
.diehard-svg .goal-indicator .goal-achieved {
  fill: var(--vscode-charts-green, #89d185);
  stroke: var(--vscode-charts-green, #89d185);
  stroke-width: 2;
}
.diehard-svg .goal-indicator .goal-pending {
  fill: var(--vscode-editorWidget-background, #252526);
  stroke: var(--vscode-panel-border, #454545);
  stroke-width: 2;
}
.diehard-svg .goal-text {
  fill: var(--vscode-foreground, #ccc);
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: 14px;
  font-weight: 600;
}
.diehard-svg .goal-achieved + .goal-text,
.diehard-svg .goal-indicator .goal-achieved ~ text {
  fill: var(--vscode-editor-background, #1e1e1e);
}
`;
