/*
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
*/
import React from "react";
import { useRpcSession, RpcPtr } from "@leanprover/infoview";
import HtmlDisplay, { Html } from './htmlDisplay';

/** The arguments passed to a `RefreshComponent` */
interface RefreshComponentProps {
  /** The ref to the refresh state of the HTML display */
  state : RpcPtr<'RefreshRef'>
  /** A cancel token that will cancel the refresh computation */
  cancelTk? : RpcPtr<'IO.CancelToken'>
}

interface RequestProps {
  state : RpcPtr<'RefreshRef'>
  oldIdx : number
}

interface ResultProps {
  /** The new HTML to display */
  html : Html
  idx : number
}

export default function RefreshComponent(props: RefreshComponentProps): JSX.Element {
  const rs = useRpcSession()
  const [html, setHtml] = React.useState<Html | null>(null)

  // Repeatedly call Lean to update
  React.useEffect(() => {
    let cancelled = false
    async function loop(idx: number) {
        const result = await rs.call<RequestProps, ResultProps | null>(
            "ProofWidgets.RefreshComponent.awaitRefresh", { oldIdx: idx, state: props.state })
        if (cancelled || !result) return
        setHtml(result.html)
        return loop(result.idx)
    }
    (async () => {
        // Set the HTML to the current value at the start of each re-render
        const result = await rs.call<RpcPtr<'RefreshRef'>, ResultProps>(
            "ProofWidgets.RefreshComponent.getCurrState", props.state)
        if (cancelled) return
        setHtml(result.html)
        // And then repeatedly refresh the HTML
        return loop(result.idx)
    })()
    return () => {
        cancelled = true
        if (props.cancelTk) {
            rs.call<RpcPtr<'IO.CancelToken'>, void>(
                "ProofWidgets.RefreshComponent.cancelRefresh", props.cancelTk)
        }
    }
  // React checks if `props` has changed using pointer equality.
  // We claim that here this is equivalent to deep equality of the objects.
  // This is because whenever a new `props` is created, this is done by Lean
  // in a way that creates fresh `RpcPtr`s.
  }, [props])
  // For the short time that `html` doesn't have a value yet, we return the empty HTML.
  return html ? <HtmlDisplay html={html}/> : <></>
}
