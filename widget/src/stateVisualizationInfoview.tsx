import * as React from 'react';
import { EnvPosContext, importWidgetModule, useAsync, useRpcSession } from '@leanprover/infoview';
import { RendererContext, StateRenderer, StateVisualizer } from './stateVisualization';

function LoadVisualizer({ visualizer, children }: React.PropsWithChildren<{visualizer: StateVisualizer}>) {
  const rs = useRpcSession();
  const pos = React.useContext(EnvPosContext);
  const { hash, exportName } = visualizer;
  const loaded = useAsync<StateRenderer | undefined>(async () => {
    if (!pos) return undefined;
    const mod = await importWidgetModule(rs, pos, hash);
    const component: unknown = mod[exportName];
    // React.memo and forwardRef produce objects rather than functions.
    return (typeof component === 'function' || (typeof component === 'object' && component !== null))
      ? component as StateRenderer : undefined;
  }, [rs, pos, hash, exportName]);
  return <RendererContext.Provider value={loaded.state === 'resolved' ? loaded.value : undefined}>
    {children}
  </RendererContext.Provider>;
}

export function VisualizationProvider({ visualizer, children }: React.PropsWithChildren<{
  visualizer?: StateVisualizer | null;
}>) {
  if (!visualizer) return <>{children}</>;
  return <LoadVisualizer visualizer={visualizer}>{children}</LoadVisualizer>;
}
