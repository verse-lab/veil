// The widgets of the Lean infoview (`widget/src`) that the panel uses. `esbuild.mjs` bundles them
// in from their sources; the widget package checks their types.
declare module '@veil/widget/veilUtils' {
  import type { Context, FC, PropsWithChildren } from 'react';

  /** Opens the source of an action or of a property, by the name that the results give it */
  export type OpenSource = (kind: 'action' | 'property', name: string) => (() => void) | undefined;
  /** What the widgets link the actions and properties to; none in the infoview */
  export const OpenSourceContext: Context<OpenSource | undefined>;
  /** Its children, as a link to the source of an action or a property when there is one */
  export const SourceLink: FC<PropsWithChildren<{ kind: 'action' | 'property'; name?: string }>>;
}

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
