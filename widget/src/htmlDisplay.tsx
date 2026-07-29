/*
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers, Wojciech Nawrocki
*/

import * as React from 'react';
import { DocumentPosition, EnvPosContext, RpcSessionAtPos, importWidgetModule, mapRpcError,
    useAsyncPersistent, useRpcSession } from '@leanprover/infoview';
import type { DynamicComponent } from '@leanprover/infoview';

export type Html =
    | { element: [string, [string, any][], Html[]] }
    | { text: string }
    | { component: [string, string, any, Html[]] }

/**
 * Render a HTML tree into JSX, resolving any dynamic imports corresponding to `component`s along
 * the way.
 *
 * This guarantees that the resulting React tree is exactly as written down in Lean. In particular,
 * there are no extraneous {@link DynamicComponent} nodes which works better with some libraries
 * that directly inspect the children nodes.
 */
export async function renderHtml(rs: RpcSessionAtPos, pos: DocumentPosition, html: Html):
        Promise<JSX.Element> {
    if ('text' in html) {
        return <>{html.text}</>
    } else if ('element' in html) {
        const [tag, attrsList, cs] = html.element
        const attrs: any = {}
        for (const [k,v] of attrsList) {
            attrs[k] = v
        }
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        if (tag === "hr") {
            // React is greatly concerned by <hr/>s having children.
            return <hr/>
        } else if (children.length === 0) {
            return React.createElement(tag, attrs)
        } else {
            return React.createElement(tag, attrs, children)
        }
    } else if ('component' in html) {
        const [hash, export_, props, cs] = html.component
        const children = await Promise.all(cs.map(async html => await renderHtml(rs, pos, html)))
        const dynProps = {...props, pos}
        const mod = await importWidgetModule(rs, pos, hash)
        if (!(export_ in mod)) throw new Error(`Module '${hash}' does not export '${export_}'`)
        if (children.length === 0) {
            return React.createElement(mod[export_], dynProps)
        } else {
            return React.createElement(mod[export_], dynProps, children)
        }
    } else {
        return <span className="red">Unknown HTML variant: {JSON.stringify(html)}</span>
    }
}

export default function HtmlDisplay({html} : {html: Html}): JSX.Element {
    const rs = useRpcSession()
    const pos = React.useContext(EnvPosContext)!
    const state = useAsyncPersistent(() => renderHtml(rs, pos, html), [rs, pos, html])
    if (state.state === 'resolved')
        return state.value
    else if (state.state === 'rejected')
        return <span className="red">Error rendering HTML: {mapRpcError(state.error).message}</span>
    return <></>
}
