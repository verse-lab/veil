// Stands in for `widget/src/htmlDisplay.tsx` in the panel, which has no Lean server to render Lean
// HTML with. `ModelCheckerView` renders Lean HTML only when it is given some, and the panel gives
// it none.
export type Html = never;

export default function HtmlDisplay(): null {
  return null;
}
