import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
import ModelCheckerView from './traceDisplay';
import { OpenSource, OpenSourceContext } from './veilUtils';

/** Where a declaration of the module is, as the results of the infoview give it */
interface UriSource {
  name: string;
  uri: string;
  line: number;
  character: number;
}

/** The `sources` of a result: see `infoviewSources` in `ExecutionWorkflow.lean` */
interface ResultSources {
  actions: UriSource[];
  properties: UriSource[];
}

/** `ModelCheckerView` in the infoview, which links the actions and the properties of a result to their
 * sources in the editor, when the result gives them. The VS Code extension of Veil links them itself. */
export default function TraceDisplayInfoview(props: React.ComponentProps<typeof ModelCheckerView>) {
  const editor = React.useContext(EditorContext);
  const sources = (props.result as unknown as { sources?: ResultSources }).sources;
  const openSource = React.useMemo<OpenSource | undefined>(() => sources && ((kind, name) => {
    const source = (kind === 'action' ? sources.actions : sources.properties).find((s) => s.name === name);
    return source && (() => void editor.revealPosition({ uri: source.uri, line: source.line, character: source.character }));
  }), [sources, editor]);
  return (
    <OpenSourceContext.Provider value={openSource}>
      <ModelCheckerView {...props} />
    </OpenSourceContext.Provider>
  );
}
