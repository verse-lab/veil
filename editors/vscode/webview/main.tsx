// The panel: it shows the run that the extension sends, and sends back what the user asks for.
import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { ExtensionMessage, PanelMessage, PanelState } from '../src/snapshot';
import { CSS, NoRun, RunView, Send } from './view';

declare function acquireVsCodeApi(): { postMessage(message: unknown): void };
const vscode = acquireVsCodeApi();
const send = (message: PanelMessage) => vscode.postMessage(message);

function App() {
  const [state, setState] = React.useState<PanelState | null | undefined>(undefined);
  const [now, setNow] = React.useState(() => Date.now());
  React.useEffect(() => {
    const onMessage = (event: MessageEvent<ExtensionMessage>) => {
      if (event.data?.type === 'state') {
        // A new run may start while the clock is stopped between runs.
        setNow(Date.now());
        setState(event.data.state);
      }
    };
    window.addEventListener('message', onMessage);
    send({ type: 'ready' });
    return () => window.removeEventListener('message', onMessage);
  }, []);
  // Keep the elapsed time going between updates
  const active = state?.run.status === 'running' || state?.run.status === 'stopping';
  React.useEffect(() => {
    if (!active) return;
    const timer = setInterval(() => setNow(Date.now()), 1000);
    return () => clearInterval(timer);
  }, [active]);
  if (state === undefined) return null;
  return state === null ? <NoRun /> : <RunView {...state} now={now} />;
}

const style = document.createElement('style');
style.textContent = CSS;
document.head.appendChild(style);
createRoot(document.getElementById('root')!).render(<Send.Provider value={send}><App /></Send.Provider>);
