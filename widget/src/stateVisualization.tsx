import * as React from 'react';

/** The widget selected by `#set_visualizer`. The hash is a string to preserve all 64 bits. */
export interface StateVisualizer {
  hash: string;
  exportName: string;
}

/** Shared state view contract (Veil.StateViewProps). Values retain their Display encoding. */
export interface StateViewProps {
  fields: Record<string, unknown>;
  previous?: Record<string, unknown>;
  theory: Record<string, unknown>;
  instantiation: Record<string, unknown>;
  transition?: unknown;
  showRemovals: boolean;
  hiddenFields: readonly string[];
}

export type StateRenderer = React.ComponentType<React.PropsWithChildren<StateViewProps>>;
export const RendererContext = React.createContext<StateRenderer | undefined>(undefined);

export function useHasVisualizer(): boolean {
  return React.useContext(RendererContext) !== undefined;
}

// A faulty renderer must not hide the witness or interfere with its result.
class VisualizerBoundary extends React.Component<React.PropsWithChildren<{fallback: React.ReactNode}>> {
  state = { failed: false };
  static getDerivedStateFromError() { return { failed: true }; }
  render() { return this.state.failed ? this.props.fallback : this.props.children; }
}

export function VisualizedState({ view, children }: React.PropsWithChildren<{ view?: StateViewProps }>) {
  const Renderer = React.useContext(RendererContext);
  if (!Renderer || !view) return <>{children}</>;
  return <VisualizerBoundary fallback={children}>
    <Renderer {...view}>{children}</Renderer>
  </VisualizerBoundary>;
}
