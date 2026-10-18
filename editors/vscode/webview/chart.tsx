// A line chart of one metric over time, for the metrics history. A chart has one series, so its
// title names it and it has no legend. The table view of the history shows the same values.
import * as React from 'react';

export interface ChartPoint {
  timeMs: number;
  value: number;
}

const PLOT_HEIGHT = 110;
const TOP = 8;
/** The band below the plot, for the time ticks */
const AXIS_HEIGHT = 18;
/** Room for the value ticks on the left, and for the label of the last value on the right */
const LEFT = 44;
const RIGHT = 52;
const MIN_WIDTH = 220;

/** The least of 1, 2 or 5 times a power of ten that is at least `x` */
function niceCeil(x: number): number {
  if (x <= 0) return 1;
  const power = Math.pow(10, Math.floor(Math.log10(x)));
  return ([1, 2, 5, 10].find(m => m * power >= x) ?? 10) * power;
}

/** E.g. 950, 1.3K, 12.9M */
export function compact(n: number): string {
  for (const [unit, size] of [['B', 1e9], ['M', 1e6], ['K', 1e3]] as const) {
    if (Math.abs(n) >= size) {
      const scaled = n / size;
      return `${(Math.abs(scaled) >= 100 ? scaled.toFixed(0) : scaled.toFixed(1)).replace(/\.0$/, '')}${unit}`;
    }
  }
  return `${n}`;
}

/** E.g. 0:05, 12:30, 1:02:03 */
export function clockTime(ms: number): string {
  const seconds = Math.round(ms / 1000);
  const pad = (n: number) => String(n).padStart(2, '0');
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  return h > 0 ? `${h}:${pad(m)}:${pad(seconds % 60)}` : `${m}:${pad(seconds % 60)}`;
}

/** Up to 4 ticks of round values from 0, the last at least `max` */
function valueTicks(max: number): number[] {
  const step = Math.max(1, niceCeil(max / 3));
  const top = Math.max(step, step * Math.ceil(max / step));
  const ticks = [];
  for (let v = 0; v <= top; v += step) ticks.push(v);
  return ticks;
}

const TIME_STEPS_S = [1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 900, 1800, 3600, 7200, 14400, 28800, 86400];

/** Ticks at round times between `from` and `to`, at most 5 */
function timeTicks(from: number, to: number): number[] {
  const stepMs = 1000 * (TIME_STEPS_S.find(s => (to - from) / (1000 * s) <= 4) ?? TIME_STEPS_S[TIME_STEPS_S.length - 1]);
  const ticks = [];
  for (let t = Math.ceil(from / stepMs) * stepMs; t <= to; t += stepMs) ticks.push(t);
  return ticks;
}

export function MetricChart({ title, points }: { title: string; points: ChartPoint[] }) {
  const container = React.useRef<HTMLDivElement>(null);
  const [width, setWidth] = React.useState(360);
  // The point under the crosshair
  const [selected, setSelected] = React.useState<number | undefined>(undefined);
  React.useEffect(() => {
    const element = container.current;
    if (!element || typeof ResizeObserver === 'undefined') return;
    const observer = new ResizeObserver(entries => setWidth(Math.max(MIN_WIDTH, entries[0].contentRect.width)));
    observer.observe(element);
    return () => observer.disconnect();
  }, []);

  const first = points[0];
  const last = points[points.length - 1];
  const ticks = valueTicks(Math.max(...points.map(p => p.value)));
  const top = ticks[ticks.length - 1];
  const plotWidth = width - LEFT - RIGHT;
  const x = (t: number) => LEFT + (last.timeMs === first.timeMs ? plotWidth : (t - first.timeMs) / (last.timeMs - first.timeMs) * plotWidth);
  const y = (v: number) => TOP + PLOT_HEIGHT - v / top * PLOT_HEIGHT;
  const line = points.map((p, i) => `${i === 0 ? 'M' : 'L'}${x(p.timeMs).toFixed(1)},${y(p.value).toFixed(1)}`).join('');
  const area = `${line}L${x(last.timeMs).toFixed(1)},${y(0)}L${x(first.timeMs).toFixed(1)},${y(0)}Z`;

  const select = (clientX: number, svg: SVGSVGElement) => {
    const px = clientX - svg.getBoundingClientRect().left;
    let nearest = 0;
    points.forEach((p, i) => {
      if (Math.abs(x(p.timeMs) - px) < Math.abs(x(points[nearest].timeMs) - px)) nearest = i;
    });
    setSelected(nearest);
  };
  const onKeyDown = (event: React.KeyboardEvent) => {
    const moves: Record<string, number> = { ArrowLeft: -1, ArrowRight: 1, Home: -points.length, End: points.length };
    if (!(event.key in moves)) return;
    event.preventDefault();
    setSelected(Math.min(points.length - 1, Math.max(0, (selected ?? points.length - 1) + moves[event.key])));
  };

  const shown = selected === undefined ? undefined : points[selected];
  const tooltipLeft = shown && x(shown.timeMs) > width - 140 ? x(shown.timeMs) - 140 : (shown ? x(shown.timeMs) + 10 : 0);
  return <div className="chart" ref={container}>
    <div className="chart-title">{title}</div>
    <svg width={width} height={TOP + PLOT_HEIGHT + AXIS_HEIGHT} tabIndex={0} role="img"
        aria-label={`${title}: ${last.value.toLocaleString('en-US')} at ${clockTime(last.timeMs)}`}
        onPointerMove={event => select(event.clientX, event.currentTarget)}
        onPointerLeave={() => setSelected(undefined)}
        onFocus={() => setSelected(points.length - 1)}
        onBlur={() => setSelected(undefined)}
        onKeyDown={onKeyDown}>
      {ticks.map(v => <g key={v}>
        <line className="chart-grid" x1={LEFT} x2={LEFT + plotWidth} y1={y(v)} y2={y(v)} />
        <text className="chart-tick" x={LEFT - 6} y={y(v)} textAnchor="end" dominantBaseline="middle">{compact(v)}</text>
      </g>)}
      {timeTicks(first.timeMs, last.timeMs).map(t =>
        <text key={t} className="chart-tick" x={x(t)} y={TOP + PLOT_HEIGHT + 13} textAnchor="middle">{clockTime(t)}</text>)}
      <path className="chart-area" d={area} />
      <path className="chart-line" d={line} />
      {shown && <line className="chart-crosshair" x1={x(shown.timeMs)} x2={x(shown.timeMs)} y1={TOP} y2={TOP + PLOT_HEIGHT} />}
      <circle className="chart-dot" cx={x(last.timeMs)} cy={y(last.value)} r={4} />
      <text className="chart-end-label" x={x(last.timeMs) + 8} y={y(last.value)} dominantBaseline="middle">{compact(last.value)}</text>
      {shown && <circle className="chart-dot" cx={x(shown.timeMs)} cy={y(shown.value)} r={4} />}
    </svg>
    {shown && <div className="chart-tooltip" style={{ left: tooltipLeft, top: TOP + 14 }}>
      <strong>{shown.value.toLocaleString('en-US')}</strong> <span>at {clockTime(shown.timeMs)}</span>
    </div>}
  </div>;
}

export const CHART_CSS = `
.chart { position: relative; margin-bottom: 12px; --viz-series: var(--vscode-charts-blue, #3794ff); }
.chart-title { font-size: 11px; color: var(--vscode-descriptionForeground); margin-bottom: 2px; }
.chart svg { display: block; overflow: visible; outline: none; }
.chart svg:focus-visible { outline: 1px solid var(--vscode-focusBorder); }
.chart-grid { stroke: var(--vscode-panel-border, rgba(128, 128, 128, 0.35)); stroke-width: 1; shape-rendering: crispEdges; }
.chart-tick { fill: var(--vscode-descriptionForeground); font-size: 10px; font-variant-numeric: tabular-nums; }
.chart-area { fill: var(--viz-series); fill-opacity: 0.1; stroke: none; }
.chart-line { fill: none; stroke: var(--viz-series); stroke-width: 2; stroke-linejoin: round; stroke-linecap: round; }
.chart-dot { fill: var(--viz-series); stroke: var(--vscode-editor-background); stroke-width: 2; }
.chart-end-label { fill: var(--vscode-foreground); font-size: 11px; }
.chart-crosshair { stroke: var(--vscode-descriptionForeground); stroke-width: 1; }
.chart-tooltip {
  position: absolute; pointer-events: none; white-space: nowrap; padding: 2px 6px; font-size: 11px;
  color: var(--vscode-editorHoverWidget-foreground, var(--vscode-foreground));
  background: var(--vscode-editorHoverWidget-background, var(--vscode-editor-background));
  border: 1px solid var(--vscode-editorHoverWidget-border, var(--vscode-panel-border)); border-radius: 3px;
}
.chart-tooltip span { color: var(--vscode-descriptionForeground); }
`;
