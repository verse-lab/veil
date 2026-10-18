// The widgets of the Lean infoview (`widget/src`) that the panel uses. `esbuild.mjs` bundles them
// in from their sources; the widget package checks their types.
declare module '@veil/widget/traceDisplay' {
  import type { FC } from 'react';

  /** The result of a model checker, with its counterexample trace if it has one */
  const ModelCheckerView: FC<{
    /** The JSON of a `ModelCheckingResult` */
    result: unknown;
    layout?: 'vertical' | 'horizontal';
    kind?: 'modelCheck' | 'simulate' | 'symbolicTrace';
  }>;
  export default ModelCheckerView;
}

declare module '@veil/widget/veilUtils' {
  export function logicalCtor(value: unknown): {
    name: string;
    args: [string | undefined, unknown][];
  } | undefined;
  export function formatValue(value: unknown): string;
}
